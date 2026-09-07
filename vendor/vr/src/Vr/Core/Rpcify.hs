-- | Extract client-to-server calls from polymorphic Core.  This is the
-- target-independent contract of Ur/Web's @Rpcify@: @rpc f@ and @tryRpc f@
-- become explicit server calls, and each named transaction target receives
-- exactly one RPC export.
module Vr.Core.Rpcify
  ( rpcifyFile
  ) where

import Control.Monad.State.Strict (State, get, modify', runState)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Vr.Core.Syntax as C
import Vr.Middle (Effect (ReadWrite), ExportKind (Rpc), FailureMode (..))
import Vr.Source
  ( Diagnostic
  , DiagnosticPhase (CorePhase)
  , Located (..)
  , diagnostic
  )

data RpcState = RpcState
  { rpcExports :: !(Set.Set C.GlobalId)
  , pendingExports :: ![C.Decl]
  , rpcProblems :: ![Diagnostic]
  }

-- | Rewrite all declarations and place newly discovered exports immediately
-- after the declaration that first requires them, matching the reference
-- pass's declaration-order environment discipline.
rpcifyFile :: C.File -> Either [Diagnostic] C.File
rpcifyFile file =
  let valueTypes = collectValueTypes file
      constructors = collectConstructors file
      aliases = collectRpcAliases file
      initial = RpcState
        { rpcExports = Set.fromList
            [identifier | declaration <- file, C.DExport (Rpc _) identifier _ <- [locatedValue declaration]]
        , pendingExports = []
        , rpcProblems = []
        }
      (rewritten, final) = runState (fmap concat (mapM (rewriteDeclaration constructors valueTypes aliases) file)) initial
   in case reverse (rpcProblems final) of
        [] -> Right rewritten
        problems -> Left problems

rewriteDeclaration
  :: Map.Map C.GlobalId C.Con
  -> Map.Map C.GlobalId C.Con
  -> Map.Map C.GlobalId FailureMode
  -> C.Decl
  -> State RpcState [C.Decl]
rewriteDeclaration constructors valueTypes aliases declaration = do
  value <- case locatedValue declaration of
    C.DVal name identifier typ expression url ->
      C.DVal name identifier typ <$> rewriteExpression constructors valueTypes aliases expression <*> pure url
    C.DValRec bindings -> C.DValRec <$> mapM binding bindings
    C.DTable name identifier row sqlName primary primaryType constraints constraintsType ->
      C.DTable name identifier row sqlName
        <$> rewriteExpression constructors valueTypes aliases primary
        <*> pure primaryType
        <*> rewriteExpression constructors valueTypes aliases constraints
        <*> pure constraintsType
    C.DView name identifier sqlName expression row ->
      C.DView name identifier sqlName <$> rewriteExpression constructors valueTypes aliases expression <*> pure row
    C.DIndex table modes ->
      C.DIndex <$> rewriteExpression constructors valueTypes aliases table <*> rewriteExpression constructors valueTypes aliases modes
    C.DTask schedule body ->
      C.DTask <$> rewriteExpression constructors valueTypes aliases schedule <*> rewriteExpression constructors valueTypes aliases body
    C.DPolicy expression -> C.DPolicy <$> rewriteExpression constructors valueTypes aliases expression
    other -> pure other
  state <- get
  modify' (\next -> next {pendingExports = []})
  pure (declaration {locatedValue = value} : reverse (pendingExports state))
  where
    binding (name, identifier, typ, expression, url) =
      (,,,,) name identifier typ <$> rewriteExpression constructors valueTypes aliases expression <*> pure url

rewriteExpression
  :: Map.Map C.GlobalId C.Con
  -> Map.Map C.GlobalId C.Con
  -> Map.Map C.GlobalId FailureMode
  -> C.Expr
  -> State RpcState C.Expr
rewriteExpression constructors valueTypes aliases source = do
  descended <- case locatedValue source of
    C.ECon classification constructor arguments payload ->
      replace . C.ECon classification constructor arguments <$> traverse recur payload
    C.EFfiApp moduleName name arguments ->
      replace . C.EFfiApp moduleName name <$> mapM typed arguments
    C.EApp function argument -> replace <$> (C.EApp <$> recur function <*> recur argument)
    C.EAbs name domain range body -> replace . C.EAbs name domain range <$> recur body
    C.ECApp function argument -> replace . (`C.ECApp` argument) <$> recur function
    C.ECAbs name kind body -> replace . C.ECAbs name kind <$> recur body
    C.EKAbs name body -> replace . C.EKAbs name <$> recur body
    C.EKApp function kind -> replace . (`C.EKApp` kind) <$> recur function
    C.ERecord fields -> replace . C.ERecord <$> mapM field fields
    C.EField record name before after -> replace . (\record' -> C.EField record' name before after) <$> recur record
    C.EConcat left leftType right rightType ->
      replace <$> (C.EConcat <$> recur left <*> pure leftType <*> recur right <*> pure rightType)
    C.ECut record name fieldType resultType ->
      replace . (\record' -> C.ECut record' name fieldType resultType) <$> recur record
    C.ECutMulti record names resultType ->
      replace . (\record' -> C.ECutMulti record' names resultType) <$> recur record
    C.ECase scrutinee branches input result ->
      replace <$> (C.ECase <$> recur scrutinee <*> mapM branch branches <*> pure input <*> pure result)
    C.EWrite expression -> replace . C.EWrite <$> recur expression
    C.EClosure identifier captures -> replace . C.EClosure identifier <$> mapM recur captures
    C.ELet name typ value body -> replace <$> (C.ELet name typ <$> recur value <*> recur body)
    C.EServerCall identifier arguments typ failure ->
      replace . (\arguments' -> C.EServerCall identifier arguments' typ failure) <$> mapM recur arguments
    _ -> pure source
  rewriteRpc constructors valueTypes aliases descended
  where
    recur = rewriteExpression constructors valueTypes aliases
    replace value = source {locatedValue = value}
    typed (expression, typ) = (,typ) <$> recur expression
    field (name, expression, typ) = (,,) name <$> recur expression <*> pure typ
    branch (pattern', expression) = (pattern',) <$> recur expression

rewriteRpc
  :: Map.Map C.GlobalId C.Con
  -> Map.Map C.GlobalId C.Con
  -> Map.Map C.GlobalId FailureMode
  -> C.Expr
  -> State RpcState C.Expr
rewriteRpc constructors valueTypes aliases source = case rpcApplication aliases source of
  Nothing -> pure source
  Just (transaction, failure) -> case namedApplication transaction of
    Nothing -> problem transaction "RPC code doesn't use a named function or transaction"
    Just (identifier, arguments) -> case Map.lookup identifier valueTypes >>= transactionResult constructors of
      Nothing -> problem transaction
        ("RPC target #" <> show (C.unGlobalId identifier) <> " does not have a transaction result")
      Just result -> do
        state <- get
        if Set.member identifier (rpcExports state)
          then pure ()
          else modify' $ \next -> next
            { rpcExports = Set.insert identifier (rpcExports next)
            , pendingExports = Located (locatedSpan transaction)
                (C.DExport (Rpc ReadWrite) identifier False) : pendingExports next
            }
        pure source {locatedValue = C.EServerCall identifier arguments result failure}
  where
    problem at message = do
      modify' $ \state -> state
        {rpcProblems = diagnostic CorePhase "rpc-target" (locatedSpan at) message : rpcProblems state}
      pure source

rpcApplication :: Map.Map C.GlobalId FailureMode -> C.Expr -> Maybe (C.Expr, FailureMode)
rpcApplication aliases expression = case locatedValue expression of
  C.EApp specialized transaction -> case locatedValue specialized of
    C.ECApp function _ -> case locatedValue function of
      C.EFfi "Basis" "rpc" -> Just (transaction, FailureNone)
      C.EFfi "Basis" "tryRpc" -> Just (transaction, FailureError)
      C.ENamed identifier -> (transaction,) <$> Map.lookup identifier aliases
      _ -> Nothing
    _ -> Nothing
  _ -> Nothing

namedApplication :: C.Expr -> Maybe (C.GlobalId, [C.Expr])
namedApplication = go []
  where
    go arguments expression = case locatedValue expression of
      C.ENamed identifier -> Just (identifier, arguments)
      C.EApp function argument -> go (argument : arguments) function
      _ -> Nothing

transactionResult :: Map.Map C.GlobalId C.Con -> C.Con -> Maybe C.Con
transactionResult constructors = go Set.empty
  where
    go seen typ = case locatedValue typ of
      C.CNamed identifier
        | Set.member identifier seen -> Nothing
        | otherwise -> Map.lookup identifier constructors >>= go (Set.insert identifier seen)
      C.TFun _ range -> go seen range
      C.CApp constructor result -> case locatedValue (resolveNamed seen constructor) of
        C.CFfi "Basis" "transaction" -> Just result
        _ -> Nothing
      _ -> Nothing

    resolveNamed seen constructor = case locatedValue constructor of
      C.CNamed identifier
        | Set.member identifier seen -> constructor
        | otherwise -> maybe constructor (resolveNamed (Set.insert identifier seen)) (Map.lookup identifier constructors)
      _ -> constructor

collectConstructors :: C.File -> Map.Map C.GlobalId C.Con
collectConstructors = Map.fromList . concatMap collect
  where
    collect declaration = case locatedValue declaration of
      C.DCon _ identifier _ definition -> [(identifier, definition)]
      _ -> []

collectValueTypes :: C.File -> Map.Map C.GlobalId C.Con
collectValueTypes = Map.fromList . concatMap collect
  where
    collect declaration = case locatedValue declaration of
      C.DVal _ identifier typ _ _ -> [(identifier, typ)]
      C.DValRec bindings -> [(identifier, typ) | (_, identifier, typ, _, _) <- bindings]
      _ -> []

collectRpcAliases :: C.File -> Map.Map C.GlobalId FailureMode
collectRpcAliases = snd . foldl step (Map.empty, Map.empty)
  where
    step (known, result) declaration = case locatedValue declaration of
      C.DVal _ identifier _ expression _ -> case locatedValue expression of
        C.EFfi "Basis" "rpc" -> insert FailureNone
        C.EFfi "Basis" "tryRpc" -> insert FailureError
        C.ENamed target -> maybe (known, result) insert (Map.lookup target known)
        _ -> (known, result)
        where insert mode = (Map.insert identifier mode known, Map.insert identifier mode result)
      _ -> (known, result)
