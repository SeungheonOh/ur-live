-- | Pattern typing and binder introduction.
module Vr.Elaborate.Patterns
  ( checkPattern
  , primitiveType
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Vr.Elaborate.Classes (bindRelativeValue)
import Vr.Elaborate.Modules (projectConAt, projectDataConstructor, resolveStructurePath)
import Vr.Elaborate.State
import Vr.Elaborate.Types
import qualified Vr.Source as S
import Vr.Source (Located (..), Primitive (..))

checkPattern :: Environment -> S.SPattern -> Con -> ElabM (Pattern, Environment)
checkPattern environment source expected = do
  (pattern', environment', _) <- checkPatternWith Set.empty environment source expected
  pure (pattern', environment')

checkPatternWith :: Set.Set String -> Environment -> S.SPattern -> Con -> ElabM (Pattern, Environment, Set.Set String)
checkPatternWith bound environment source expected0 = case locatedValue source of
  S.SPVar name -> do
    if name /= "_" && Set.member name bound
      then withSpanError "duplicate-pattern-variable" location ("Duplicate pattern variable " <> name)
      else pure ()
    expected <- zonkCon expected0
    pure (at (PVar name expected), bindRelativeValue name expected environment, Set.insert name bound)
  S.SPPrim primitive -> do
    typ <- primitiveType environment location primitive
    unifyCon environment expected0 typ
    pure (at (PPrim primitive), environment, bound)
  S.SPCon modules name argument -> case lookupDataConstructor environment modules name of
    Nothing -> do
      withSpanError "unbound-data-constructor" location ("Unbound datatype constructor " <> qualify modules name)
      pure (at (PCon Default (PConVar (GlobalId (-1))) [] Nothing), environment, bound)
    Just (patternConstructor, binding) -> do
      (parameters, instantiated) <- instantiateScheme location (dataConstructorType binding)
      (argumentType, resultType) <- case locatedValue instantiated of
        TFun domain result -> pure (Just domain, result)
        _ -> pure (Nothing, instantiated)
      unifyCon environment expected0 resultType
      case (argument, argumentType) of
        (Nothing, Nothing) -> pure (at (PCon (dataConstructorKind binding) patternConstructor parameters Nothing), environment, bound)
        (Just nested, Just nestedType) -> do
          (nested', environment', bound') <- checkPatternWith bound environment nested nestedType
          pure (at (PCon (dataConstructorKind binding) patternConstructor parameters (Just nested')), environment', bound')
        (Nothing, Just _) -> do
          withSpanError "missing-pattern-argument" location ("Constructor " <> name <> " requires an argument")
          pure (at (PCon (dataConstructorKind binding) patternConstructor parameters Nothing), environment, bound)
        (Just _, Nothing) -> do
          withSpanError "unexpected-pattern-argument" location ("Constructor " <> name <> " takes no argument")
          pure (at (PCon (dataConstructorKind binding) patternConstructor parameters Nothing), environment, bound)
  S.SPRecord fields flexible -> do
    fieldTypes <- mapM (const (freshConMeta location 0 (Located location KType) "pattern-field")) fields
    let names = [Located location (CName name) | (name, _) <- fields]
        known = Located location (CRecord (Located location KType) (zip names fieldTypes))
    row <- if flexible
      then do
        rest <- freshConMeta location 0 (Located location (KRecord (Located location KType))) "pattern-rest"
        pure (Located location (CConcat known rest))
      else pure known
    unifyCon environment expected0 (Located location (TRecord row))
    (patterns, environment', bound') <- checkFields bound environment (zip3 fields names fieldTypes)
    pure (at (PRecord patterns flexible), environment', bound')
  S.SPAnnot patternSource annotation -> do
    annotation' <- checkCon annotation (Located location KType)
    unifyCon environment expected0 annotation'
    checkPatternWith bound environment patternSource annotation'
  where
    location = S.locatedSpan source
    at = Located location
    checkFields currentBound current [] = pure ([], current, currentBound)
    checkFields currentBound current (((name, patternSource), _, typ) : rest) = do
      (pattern', next, nextBound) <- checkPatternWith currentBound current patternSource typ
      (rest', final, finalBound) <- checkFields nextBound next rest
      pure ((name, pattern', typ) : rest', final, finalBound)

primitiveType :: Environment -> S.Span -> Primitive -> ElabM Con
primitiveType environment at primitive = named $ case primitive of
  PrimInt {} -> "int"
  PrimFloat {} -> "float"
  PrimString {} -> "string"
  PrimChar {} -> "char"
  where
    named name = case Map.lookup "Basis" (environmentStructures environment) of
      Just binding -> pure (Located at (CModProj (structureBindingId binding) [] name))
      Nothing -> case Map.lookup name (environmentConstructors environment) of
        Just binding -> pure (Located at (CNamed (conBindingId binding)))
        Nothing -> withSpanError "missing-primitive-type" at ("Primitive type " <> name <> " is not in scope") >> pure (Located at CError)

lookupDataConstructor :: Environment -> [String] -> String -> Maybe (PatCon, DataConstructorBinding)
lookupDataConstructor environment modules name = case modules of
  [] -> do
    binding <- Map.lookup name (environmentDataConstructors environment)
    pure (PConVar (dataConstructorId binding), binding)
  _ -> do
    (root, path, signature) <- resolveStructurePath environment modules
    binding <- projectDataConstructor signature name
    pure
      ( PConProj root path name
      , binding
          { dataConstructorArgument = fmap (projectConAt root path signature) (dataConstructorArgument binding)
          , dataConstructorType = projectConAt root path signature (dataConstructorType binding)
          }
      )

instantiateScheme :: S.Span -> Con -> ElabM ([Con], Con)
instantiateScheme at = go []
  where
    go arguments scheme = case locatedValue scheme of
      TCFun _ name kind body -> do
        argument <- freshConMeta at 0 kind name
        go (arguments <> [argument]) (substituteCon 0 argument body)
      _ -> pure (arguments, scheme)

qualify :: [String] -> String -> String
qualify modules name = foldr (\piece suffix -> piece <> "." <> suffix) name modules
