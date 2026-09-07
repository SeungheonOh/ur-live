{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Byte-spanned syntax produced by the Ur parser.
--
-- The types in this module are deliberately close to the source language.
-- Names have not been resolved, implicit constructor and dictionary arguments
-- have not been inserted, and most parser sugar has only been lowered far
-- enough to share a single representation.  Every recursive syntax node is a
-- located node so later diagnostics can point back to the original bytes.
module Vr.Source
  ( SourcePos (..)
  , Span (..)
  , Located (..)
  , noSpan
  , pointSpan
  , mergeSpans
  , mapLocated
  , DiagnosticSeverity (..)
  , DiagnosticPhase (..)
  , Diagnostic (..)
  , diagnostic
  , StringMode (..)
  , Primitive (..)
  , Explicitness (..)
  , Inference (..)
  , SKind
  , SKindF (..)
  , SCon
  , SConF (..)
  , SPattern
  , SPatternF (..)
  , SExpr
  , SExprF (..)
  , SEDecl
  , SEDeclF (..)
  , SSignature
  , SSignatureF (..)
  , SSigItem
  , SSigItemF (..)
  , SFfiMode (..)
  , SDecl
  , SDeclF (..)
  , SStructure
  , SStructureF (..)
  , SFile
  ) where

import Data.ByteString (ByteString)
import Data.Int (Int64)
import Data.Word (Word8)
import GHC.Exts (isTrue#, reallyUnsafePtrEquality#)

-- | Positions are byte-oriented.  Columns count bytes since the most recent
-- newline, matching Ur/Web's source model rather than Unicode code points.
data SourcePos = SourcePos
  { sourceOffset :: !Int
    -- ^ Zero-based byte offset from the start of the file.
  , sourceLine :: !Int
    -- ^ One-based source line.
  , sourceColumn :: !Int
    -- ^ Zero-based byte column, not a Unicode character column.
  }
  deriving stock (Eq, Ord, Show)

-- | A half-open source range.  Generated nodes use 'noSpan'.
data Span = Span
  { spanFile :: !FilePath
    -- ^ File whose bytes the range addresses.
  , spanStart :: !SourcePos
    -- ^ Position of the first byte belonging to the construct.
  , spanEnd :: !SourcePos
    -- ^ Position immediately after the construct's last byte.
  }
  deriving stock (Show)

instance Eq Span where
  Span leftFile leftStart leftEnd == Span rightFile rightStart rightEnd =
    (isTrue# (reallyUnsafePtrEquality# leftFile rightFile) || leftFile == rightFile)
      && leftStart == rightStart && leftEnd == rightEnd

instance Ord Span where
  compare (Span leftFile leftStart leftEnd) (Span rightFile rightStart rightEnd) =
    compareFiles <> compare leftStart rightStart <> compare leftEnd rightEnd
    where
      -- Parser nodes and their lowered descendants share their filename.
      -- A positive pointer comparison proves equality of these immutable
      -- strings; a negative result says nothing and must use the complete
      -- lexical comparison.  The strict fields already force both to WHNF.
      -- Keep the derived instance's file/start/end ordering, including every
      -- position field, since IR maps depend on that exact ordering.
      compareFiles
        | isTrue# (reallyUnsafePtrEquality# leftFile rightFile) = EQ
        | otherwise = compare leftFile rightFile

-- | The ubiquitous syntax-node constructor: a semantic value paired with the
-- exact source range that produced it.
data Located a = Located
  { locatedSpan :: !Span
    -- ^ Range used for diagnostics and for the location of generated IR.
  , locatedValue :: a
    -- ^ The phase-specific payload.
  }
  deriving stock (Eq, Ord, Show, Functor)

-- | Synthetic zero-width span used for compiler-generated nodes that have no
-- faithful source range.
noSpan :: Span
noSpan = Span "<generated>" start start
  where
    start = SourcePos 0 1 0

-- | Construct an empty span at one position, typically for a diagnostic that
-- concerns a boundary rather than a complete token.
pointSpan :: FilePath -> SourcePos -> Span
pointSpan file pos = Span file pos pos

-- | Cover the range from the first span's start through the second span's end.
-- Both spans are expected to refer to the same file.
mergeSpans :: Span -> Span -> Span
mergeSpans left right =
  Span
    { spanFile = spanFile left
    , spanStart = spanStart left
    , spanEnd = spanEnd right
    }

-- | Transform a located payload without changing its source range.
mapLocated :: (a -> b) -> Located a -> Located b
mapLocated f (Located at value) = Located at (f value)

-- | Whether a diagnostic prevents a successful phase result.
data DiagnosticSeverity
  = DiagnosticError
    -- ^ A rejected program or an invariant that could not be recovered.
  | DiagnosticWarning
    -- ^ A non-fatal observation; retained separately from compatibility errors.
  deriving stock (Eq, Ord, Show)

-- | Pipeline stage responsible for a diagnostic.
data DiagnosticPhase
  = ProjectPhase
    -- ^ Project discovery, @.urp@ directives, paths, and source-unit loading.
  | LexPhase
    -- ^ Conversion of source bytes into tokens and literal payloads.
  | ParsePhase
    -- ^ Grammar recognition and parser-level desugaring.
  | ElaboratePhase
    -- ^ Name resolution, kind/type inference, modules, rows, and instances.
  | ExplicitPhase
    -- ^ Final audit that no error or inference-only node reaches backend IR.
  | CorePhase
    -- ^ Module flattening and whole-program Core construction.
  | MonoPhase
    -- ^ Specialization and lowering to the target-independent monomorphic IR.
  | BackendPhase
    -- ^ Target-specific lowering, runtime ABI selection, and artifact emission.
  deriving stock (Eq, Ord, Show)

-- | A structured frontend diagnostic.  Related locations describe secondary
-- declarations or constraints without flattening them into the main message.
data Diagnostic = Diagnostic
  { diagnosticSeverity :: !DiagnosticSeverity
    -- ^ Fatality of the problem.
  , diagnosticPhase :: !DiagnosticPhase
    -- ^ Frontend phase that detected it.
  , diagnosticCode :: !String
    -- ^ Stable machine-oriented category such as @unbound-value@.
  , diagnosticSpan :: !Span
    -- ^ Primary source range.
  , diagnosticMessage :: !String
    -- ^ Human-readable explanation.
  , diagnosticRelated :: ![(Span, String)]
    -- ^ Secondary ranges and their relationship to the primary problem.
  }
  deriving stock (Eq, Ord, Show)

-- | Construct the common fatal diagnostic form with no related locations.
diagnostic :: DiagnosticPhase -> String -> Span -> String -> Diagnostic
diagnostic phase code at message =
  Diagnostic
    { diagnosticSeverity = DiagnosticError
    , diagnosticPhase = phase
    , diagnosticCode = code
    , diagnosticSpan = at
    , diagnosticMessage = message
    , diagnosticRelated = []
    }

-- | The lexical context in which a string payload was read.
data StringMode
  = NormalString
    -- ^ An ordinary quoted Ur string, with normal string escaping.
  | HtmlString
    -- ^ Literal text originating in XML syntax; escaping follows XML mode.
  deriving stock (Eq, Ord, Show)

-- | Literal payload shared by source patterns/expressions and elaborated IR.
data Primitive
  = PrimInt !Int64
    -- ^ A signed machine-independent integer literal.
  | PrimFloat !Double
    -- ^ A real literal represented with the reference compiler's precision.
  | PrimString !StringMode !ByteString
    -- ^ A byte string together with the lexical mode that determines how its
    -- contents are interpreted and escaped.
  | PrimChar !Word8
    -- ^ A byte-valued character literal.  Ur/Web characters are not Unicode
    -- scalar values at this frontend boundary.
  deriving stock (Eq, Ord, Show)

-- | Visibility of a constructor-polymorphic binder or application.
data Explicitness
  = Explicit
    -- ^ The caller supplies the constructor argument with explicit syntax.
  | Implicit
    -- ^ Elaboration may synthesize the constructor argument at a use site.
  deriving stock (Eq, Ord, Show)

-- | Source-level control over insertion of implicit arguments after a value
-- name or application head is resolved.
data Inference
  = Infer
    -- ^ Insert kind arguments, implicit constructor arguments, class
    -- dictionaries, and disjointness evidence as required.
  | DontInfer
    -- ^ Suppress ordinary constructor/dictionary inference, while still
    -- instantiating leading kind polymorphism needed to expose the type.
  | TypesOnly
    -- ^ Insert type-level arguments but do not synthesize class dictionaries
    -- or discharge disjointness-qualified arrows.
  deriving stock (Eq, Ord, Show)

-- | A source kind with its byte span.
type SKind = Located SKindF

-- | Source-language kinds classify constructors.  They are still named and
-- may contain wildcards; elaboration resolves binders and creates kind
-- metavariables.
data SKindF
  = SKType
    -- ^ @Type@: the kind of ordinary value types such as @int@ and
    -- @transaction page@.
  | SKArrow !SKind !SKind
    -- ^ @k1 -> k2@: the kind of a constructor function accepting a
    -- constructor of the first kind and returning one of the second.
  | SKName
    -- ^ @Name@: the kind inhabited by record-field name constructors such as
    -- @#Id@.
  | SKRecord !SKind
    -- ^ @{k}@ in Ur syntax: the kind of finite, ordered rows whose field
    -- values have kind @k@.  For example, @{Type}@ classifies record rows.
  | SKUnit
    -- ^ @Unit@: the singleton kind used for sets of names and SQL key rows;
    -- its sole constructor is 'SCUnit'.
  | SKTuple ![SKind]
    -- ^ A product kind.  Components are selected by the one-based 'SCProj'
    -- constructor form.
  | SKWild
    -- ^ @_@: request a fresh inferred kind.  Wildcards are useful in ordinary
    -- source but are rejected where the pinned language requires a complete
    -- signature.
  | SKFun !String !SKind
    -- ^ A kind-level lambda that binds the given kind-variable name in its
    -- body.  Bound occurrences are represented initially by 'SKVar'.
  | SKVar !String
    -- ^ A reference to a lexically bound kind variable.
  deriving stock (Eq, Ord, Show)

-- | A source constructor with its byte span.  Ur uses /constructor/ for every
-- type-level term, including types, rows, names, and constructor functions.
type SCon = Located SConF

-- | Unresolved source constructors and types.
data SConF
  = SCAnnot !SCon !SKind
    -- ^ Kind ascription @c :: k@.  The ascription constrains inference but
    -- does not survive as a distinct elaborated constructor node.
  | SCTFun !SCon !SCon
    -- ^ Ordinary value-function type @domain -> range@.  Both operands must
    -- elaborate at kind 'SKType'.
  | SCTCFun !Explicitness !String !SKind !SCon
    -- ^ Constructor-polymorphic value type.  The fields are binder
    -- explicitness, binder name, binder kind, and body; the name is in scope
    -- only in the body.
  | SCTRecord !SCon
    -- ^ Record type @$row@ (surface record-type syntax), formed from a
    -- constructor whose kind is @{Type}@.
  | SCTDisjoint !SCon !SCon !SCon
    -- ^ Disjointness-qualified type @[left ~ right] => body@.  A value of this
    -- type may be used only when the two row constructors are provably
    -- disjoint.
  | SCVar ![String] !String
    -- ^ A constructor name before resolution.  The list is the enclosing
    -- structure path and the final string is the component name; an empty path
    -- denotes a lexical or top-level constructor.
  | SCApp !SCon !SCon
    -- ^ Constructor-level application.  The function must have an arrow kind
    -- whose domain matches the argument's kind.
  | SCAbs !String !(Maybe SKind) !SCon
    -- ^ Constructor lambda.  The optional annotation gives the bound
    -- constructor's kind; when omitted it is inferred.  The name is in scope
    -- in the body.
  | SCKAbs !String !SCon
    -- ^ Kind abstraction in a constructor: bind a kind variable and produce a
    -- constructor that may later receive a kind argument.
  | SCTKFun !String !SCon
    -- ^ A kind-polymorphic value type.  It universally binds a kind variable
    -- in the following type, analogously to 'SCTCFun' at the kind level.
  | SCName !String
    -- ^ A literal field-name constructor, written with Ur's @#Field@ syntax
    -- and having kind 'SKName'.
  | SCRecord ![(SCon, SCon)]
    -- ^ A row constructor.  Each ordered pair is a name constructor and its
    -- field constructor; elaboration infers the common field kind and checks
    -- that field names are disjoint.
  | SCConcat !SCon !SCon
    -- ^ Ordered row concatenation.  The operands must be rows of a common
    -- element kind and must satisfy the surrounding disjointness requirements.
  | SCMap
    -- ^ The primitive constructor-level row mapper.  Applying it to a
    -- constructor function and a row maps that function over every field
    -- value while preserving field order and names.
  | SCUnit
    -- ^ The sole constructor of kind 'SKUnit', commonly used as the value in
    -- rows that represent finite name sets.
  | SCTuple ![SCon]
    -- ^ Constructor tuple used to pass several constructor components as one
    -- value of tuple kind.
  | SCProj !SCon !Int
    -- ^ One-based projection from a constructor tuple.  The integer is the
    -- source field number and is checked against the tuple kind.
  | SCWild !SKind
    -- ^ A constructor hole annotated with its expected kind.  Elaboration
    -- creates a unification metavariable; a nested 'SKWild' also infers the
    -- hole's kind.
  deriving stock (Eq, Ord, Show)

-- | A source pattern with its byte span.
type SPattern = Located SPatternF

-- | Patterns introduce value bindings and destructure datatypes or records.
data SPatternF
  = SPVar !String
    -- ^ A variable pattern.  The distinguished name @_@ is a wildcard and
    -- does not add a binding to the environment.
  | SPPrim !Primitive
    -- ^ A literal pattern that matches exactly the represented primitive.
  | SPCon ![String] !String !(Maybe SPattern)
    -- ^ A datatype-constructor pattern before name resolution.  The fields are
    -- module path, constructor name, and the optional payload pattern.
  | SPRecord ![(String, SPattern)] !Bool
    -- ^ A record pattern with source field labels and nested patterns.  The
    -- Boolean is true for the flexible @...@ form, which admits additional
    -- fields not named in the pattern.
  | SPAnnot !SPattern !SCon
    -- ^ A pattern type ascription.  It constrains the pattern's expected type
    -- but disappears after pattern elaboration.
  deriving stock (Eq, Ord, Show)

-- | A source expression with its byte span.
type SExpr = Located SExprF

-- | Core expression forms after XML, SQL, and operator syntax have been
-- desugared into ordinary applications and these structural forms.
data SExprF
  = SEAnnot !SExpr !SCon
    -- ^ Value type ascription @expression : type@.  Elaboration checks the
    -- inferred type against the source constructor and retains only the typed
    -- expression.
  | SEPrim !Primitive
    -- ^ An integer, real, string, XML-text, or character literal.
  | SEVar ![String] !String !Inference
    -- ^ An unresolved value reference.  The list is its structure path, the
    -- string is its final name, and 'Inference' controls which implicit
    -- arguments may be inserted at this use.
  | SEApp !SExpr !SExpr
    -- ^ Ordinary call-by-value function application.
  | SEAbs !String !(Maybe SCon) !SExpr
    -- ^ Value lambda with an optional parameter type.  The parameter name is
    -- in scope in the body; an omitted type is inferred.
  | SECApp !SExpr !SCon
    -- ^ Explicit constructor application of a polymorphic value, corresponding
    -- to supplying an argument bound by 'SCTCFun'.
  | SECAbs !Explicitness !String !SKind !SExpr
    -- ^ Value abstraction over a constructor.  The fields record binder
    -- visibility, name, kind, and body.
  | SEDisjoint !SCon !SCon !SExpr
    -- ^ Abstraction over a row-disjointness assumption.  The assumption is
    -- available while elaborating the body and becomes an 'SCTDisjoint'
    -- qualifier on the resulting type; it has no runtime representation.
  | SEDisjointApp !SExpr
    -- ^ Explicitly discharge the leading disjointness qualifier of an
    -- expression's type using facts in the current environment.
  | SEKAbs !String !SExpr
    -- ^ Value abstraction over a kind variable, producing a kind-polymorphic
    -- value whose type elaborates to @TKFun@.
  | SERecord ![(SCon, SExpr)] !Bool
    -- ^ Record construction with constructor-valued field names.  The Boolean
    -- records flexible syntax for parser uniformity; flexible records are
    -- legal only as patterns and are diagnosed in expression position.
  | SEField !SExpr !SCon
    -- ^ Select the field named by the constructor from a record expression.
  | SEConcat !SExpr !SExpr
    -- ^ Concatenate two records after proving their rows disjoint.  Source
    -- order is preserved.
  | SECut !SExpr !SCon
    -- ^ Remove one constructor-named field from a record and return the
    -- remaining record.
  | SECutMulti !SExpr !SCon
    -- ^ Remove an entire row of fields from a record.  The second constructor
    -- denotes the row being removed.
  | SEWild
    -- ^ Expression hole @_@.  It creates a dictionary-resolution goal and is
    -- accepted only when the language's ordered instance search can synthesize
    -- an expression.
  | SECase !SExpr ![(SPattern, SExpr)]
    -- ^ Pattern match: a scrutinee followed by ordered pattern/body branches.
    -- Branch result types are unified and basic exhaustiveness is checked.
  | SELet ![SEDecl] !SExpr
    -- ^ Lexically scoped local value declarations followed by their body.
  deriving stock (Eq, Ord, Show)

-- | A local expression declaration with its byte span.
type SEDecl = Located SEDeclF

-- | Declarations permitted inside an expression-level @let@.
data SEDeclF
  = SEDVal !SPattern !SExpr
    -- ^ Non-recursive pattern binding.  The expression is inferred before the
    -- pattern's names enter scope.
  | SEDValRec ![(String, Maybe SCon, SExpr)]
    -- ^ A mutually recursive group.  Each tuple gives name, optional declared
    -- type, and definition; all names are in scope in all definitions, and
    -- definitions must have an allowable function-like recursive shape.
  deriving stock (Eq, Ord, Show)

-- | A source module signature with its byte span.
type SSignature = Located SSignatureF

-- | Unresolved module-signature expressions.
data SSignatureF
  = SSigConst ![SSigItem]
    -- ^ A literal @sig ... end@ signature.  Items are elaborated sequentially,
    -- so earlier components are visible to later items.
  | SSigVar !String
    -- ^ Reference to a named signature in the current signature namespace.
  | SSigFun !String !SSignature !SSignature
    -- ^ Functor signature.  The module parameter name and domain signature are
    -- in scope while elaborating the range signature.
  | SSigWhere !SSignature ![String] !String !SCon
    -- ^ @where con@ refinement.  It makes the constructor component identified
    -- by nested structure path and component name equal to the supplied
    -- definition.
  | SSigProj !String ![String] !String
    -- ^ Signature projected from a structure.  The fields are root structure,
    -- nested structure path, and final signature component name.
  deriving stock (Eq, Ord, Show)

-- | One source signature item with its byte span.
type SSigItem = Located SSigItemF

-- | Components exported by a literal signature.
data SSigItemF
  = SSIConAbs !String !SKind
    -- ^ Abstract constructor component @con name :: kind@.  Clients know its
    -- kind and nominal identity but not a definition.
  | SSICon !String !(Maybe SKind) !SCon
    -- ^ Transparent constructor component.  The optional kind annotation is
    -- checked against the definition's inferred kind.
  | SSIDatatype ![(String, [String], [(String, Maybe SCon)])]
    -- ^ One mutually declared datatype group.  Each datatype gives its name,
    -- type-parameter names (all of kind @Type@), and constructors with optional
    -- payload types.
  | SSIDatatypeImp !String ![String] !String
    -- ^ Imported datatype specification: a fresh local component name aliases
    -- the datatype selected by a module path and original name, including its
    -- data constructors.
  | SSIVal !String !SCon
    -- ^ Value component with its required type.
  | SSITable !String !SCon !SExpr !SExpr
    -- ^ Table component containing name, row constructor, primary-key
    -- expression, and additional constraint expression.  Elaboration exposes
    -- the table value and the hidden row constraints required by its type.
  | SSIStr !String !SSignature
    -- ^ Nested structure component and its public signature.
  | SSISgn !String !SSignature
    -- ^ Nested named-signature component.
  | SSIInclude !SSignature
    -- ^ Include all components of another constant signature at this position,
    -- subject to the same duplicate-namespace checks as written-out items.
  | SSIConstraint !SCon !SCon
    -- ^ Exported row-disjointness fact between two row constructors.
  | SSIClassAbs !String !SKind
    -- ^ Abstract type-class constructor.  Its kind fixes the parameters of the
    -- class, while its representation remains hidden.
  | SSIClass !String !SKind !SCon
    -- ^ Transparent type-class constructor with name, declared kind, and
    -- defining constructor.
  deriving stock (Eq, Ord, Show)

-- | Operational annotations accepted on a low-level @ffi@ value declaration.
-- They describe where an external symbol exists and how calls may be treated;
-- they do not change the Ur type carried by 'SDFfi'.
data SFfiMode
  = FfiEffectful
    -- ^ Calls may perform externally observable effects and must be preserved
    -- and ordered accordingly.
  | FfiBenignEffectful
    -- ^ Calls are effectful for optimization purposes but belong to the
    -- reference compiler's less restrictive "benign" effect class.
  | FfiClientOnly
    -- ^ The binding is available only in generated client-side code.
  | FfiServerOnly
    -- ^ The binding is available only in generated server-side code.
  | FfiJsFunc !String
    -- ^ Associate the Ur binding with the given JavaScript function name.
  deriving stock (Eq, Ord, Show)

-- | A source top-level or structure declaration with its byte span.
type SDecl = Located SDeclF

-- | Source declaration forms.  Project loading also synthesizes several of
-- these forms (notably database, export, FFI-structure, and error-handler
-- declarations) from @.urp@ directives before elaboration.
data SDeclF
  = SDCon !String !(Maybe SKind) !SCon
    -- ^ Transparent constructor declaration.  The fields are name, optional
    -- kind annotation, and definition.
  | SDDatatype ![(String, [String], [(String, Maybe SCon)])]
    -- ^ A mutually recursive datatype declaration group.  Each entry contains
    -- datatype name, type parameters, and data constructors with optional
    -- payload types.
  | SDDatatypeImp !String ![String] !String
    -- ^ Import a datatype under a local name from the given structure path and
    -- original datatype name, preserving constructor identities through module
    -- projection.
  | SDVal !SPattern !SExpr
    -- ^ Non-recursive top-level pattern binding.  Simple variable patterns
    -- become named IR values; destructuring patterns are lowered through a
    -- checked case expression.
  | SDValRec ![(String, Maybe SCon, SExpr)]
    -- ^ A mutually recursive value/function group containing each name,
    -- optional type annotation, and body.
  | SDSgn !String !SSignature
    -- ^ Bind a name in the signature namespace.
  | SDStr !String !(Maybe SSignature) !(Maybe Integer) !SStructure !Bool
    -- ^ Structure or functor binding.  The fields are public name, optional
    -- signature ascription, optional source modification timestamp retained
    -- for Ur/Web compatibility, structure expression, and whether project
    -- loading marked the module as originating from a root directive.
  | SDFfiStr !String !SSignature !(Maybe Integer)
    -- ^ Foreign structure introduced by a project @ffi@ directive.  It carries
    -- a restricted signature and optional source modification timestamp but no
    -- Ur implementation body.
  | SDOpen !String ![String]
    -- ^ Open a structure path into the surrounding namespaces.  The root name
    -- is separate from the remaining path to make resolution and diagnostics
    -- explicit.
  | SDConstraint !SCon !SCon
    -- ^ Assert that two row constructors are disjoint for all following
    -- declarations in this scope.
  | SDOpenConstraints !String ![String]
    -- ^ Import only disjointness/class/instance constraints reachable from a
    -- structure path, without opening its ordinary component names.
  | SDExport !SStructure
    -- ^ Mark the named or computed structure as the project's externally
    -- exported application structure.  Project loading synthesizes a final
    -- export for the last compilation unit.
  | SDTable !String !SCon !SExpr !SExpr
    -- ^ SQL table declaration with table name, row constructor, primary-key
    -- specification, and remaining SQL-constraint specification.
  | SDSequence !String
    -- ^ SQL sequence declaration.  It introduces a value of the standard
    -- @sql_sequence@ type and a separately identified schema object.
  | SDView !String !SExpr
    -- ^ SQL view declaration with its source name and defining query.  The
    -- result row is inferred from the query.
  | SDIndex !SExpr !SExpr !(Maybe SCon)
    -- ^ SQL index declaration.  The first expression denotes the table, the
    -- second is the record of index modes, and the optional row constructor
    -- restricts the indexed fields.
  | SDDatabase !String
    -- ^ Select the database connection string supplied by the project file.
    -- It affects the eventual backend but is retained in frontend IR.
  | SDCookie !String !SCon
    -- ^ HTTP cookie declaration with source name and payload type.
  | SDStyle !String
    -- ^ CSS class declaration, introducing a value of standard type
    -- @css_class@.
  | SDTask !SExpr !SExpr
    -- ^ Scheduled-task declaration.  The first expression describes the task
    -- schedule/kind and the second is the handler function returning a unit
    -- transaction.
  | SDPolicy !SExpr
    -- ^ SQL policy declaration; the expression must have standard type
    -- @sql_policy@.
  | SDOnError !String ![String] !String
    -- ^ Project error-handler reference, split into root structure, nested
    -- structure path, and final value name.
  | SDFfi !String ![SFfiMode] !SCon
    -- ^ Direct foreign value declaration with Ur name, operational FFI modes,
    -- and declared Ur type.  It requires the project's @lessSafeFfi@ opt-in.
  deriving stock (Eq, Ord, Show)

-- | A source structure expression with its byte span.
type SStructure = Located SStructureF

-- | Module expressions before signature matching and selfification.
data SStructureF
  = SStrConst ![SDecl]
    -- ^ Literal @struct ... end@ body.  Declarations elaborate sequentially
    -- and their exported components form the inferred constant signature.
  | SStrVar !String
    -- ^ Reference to a structure bound in the current module environment.
  | SStrProj !SStructure !String
    -- ^ Select a nested structure component from another structure expression.
  | SStrFun !String !SSignature !(Maybe SSignature) !SStructure
    -- ^ Functor abstraction with parameter name, domain signature, optional
    -- result ascription, and body.  The parameter is in scope in both the body
    -- and the result-ascription check.
  | SStrApp !SStructure !SStructure
    -- ^ Generative functor application.  The argument signature is checked
    -- against the domain and formal module identities are substituted into the
    -- result signature.
  deriving stock (Eq, Ord, Show)

-- | A parsed implementation file: an ordered list of declarations.  Order is
-- semantically significant for scope, instance selection, and module identity.
type SFile = [SDecl]
