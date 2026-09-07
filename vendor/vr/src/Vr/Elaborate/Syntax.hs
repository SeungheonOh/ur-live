{-# LANGUAGE DerivingStrategies #-}

-- | The typed tree produced by elaboration. Its shape deliberately follows
-- Ur/Web's @Elab@ language: global names carry unique integer identities,
-- local constructors and values use de Bruijn indices, and inference
-- variables remain explicit until the solver reaches its fixed point.
module Vr.Elaborate.Syntax
  ( GlobalId (..)
  , MetaId (..)
  , Kind
  , KindF (..)
  , Con
  , ConF (..)
  , DatatypeKind (..)
  , PatCon (..)
  , Pattern
  , PatternF (..)
  , Expr
  , ExprF (..)
  , EDecl
  , EDeclF (..)
  , ImportMode (..)
  , Signature
  , SignatureF (..)
  , SigItem
  , SigItemF (..)
  , Decl
  , DeclF (..)
  , Structure
  , StructureF (..)
  , File
  ) where

import Vr.Source (Explicitness, Located, Primitive, SFfiMode, Span)

-- | Nominal identity allocated to a top-level or module component.  Source
-- spelling is insufficient because Ur permits shadowing and functor
-- application creates fresh identities.
newtype GlobalId = GlobalId
  { unGlobalId :: Int
    -- ^ Monotonically allocated identifier within one elaboration run.
  }
  deriving stock (Eq, Ord, Show)

-- | Identity of a kind, constructor, or expression inference variable.  The
-- namespace is shared by the elaboration state, while the node containing the
-- identifier determines which solution table applies.
newtype MetaId = MetaId
  { unMetaId :: Int
    -- ^ Monotonically allocated inference-variable identifier.
  }
  deriving stock (Eq, Ord, Show)

-- | An elaborated kind with a source or generated location.
type Kind = Located KindF

-- | Resolved kind language.  Relative variables use de Bruijn indices, while
-- metavariable constructors exist only during inference and must be solved or
-- diagnosed before backend consumption.
data KindF
  = KType
    -- ^ Kind of ordinary value types.
  | KArrow !Kind !Kind
    -- ^ Constructor-function kind from the first kind to the second.
  | KName
    -- ^ Kind of record-field name constructors.
  | KRecord !Kind
    -- ^ Kind of rows whose field values inhabit the contained element kind.
  | KUnit
    -- ^ Singleton kind used for row-encoded name sets.
  | KTuple ![Kind]
    -- ^ Product kind with one component for each constructor tuple element.
  | KError
    -- ^ Recovery sentinel introduced after a kind error.  Successful
    -- finalization rejects any tree in which it remains reachable.
  | KMeta !MetaId !Span !String
    -- ^ Unsolved ordinary kind metavariable: identity, creation span, and a
    -- diagnostic/debug label describing what was being inferred.
  | KTupleMeta !MetaId !Span ![(Int, Kind)]
    -- ^ Partially known tuple kind created by projecting before tuple arity is
    -- known.  The ordered pairs record one-based projections and the kinds
    -- already demanded for those positions.
  | KRel !Int
    -- ^ De Bruijn reference to a surrounding kind binder; zero names the
    -- nearest 'KFun', @CKAbs@, @TKFun@, @EKAbs@, or equivalent binder.
  | KFun !String !Kind
    -- ^ Kind-level abstraction.  The string is retained for diagnostics and
    -- pretty printing; bound occurrences in the body are 'KRel' indices.
  deriving stock (Eq, Ord, Show)

-- | An elaborated constructor or type with its location.
type Con = Located ConF

-- | Typed constructor language.  Every node has an inferable kind, and names
-- have been replaced by nominal IDs, module projections, or de Bruijn indices.
data ConF
  = TFun !Con !Con
    -- ^ Ordinary value-function type, storing domain and range.
  | TCFun !Explicitness !String !Kind !Con
    -- ^ Constructor-polymorphic value type.  It stores binder visibility,
    -- source name, binder kind, and body; 'CRel' zero refers to the binder in
    -- the body.
  | TRecord !Con
    -- ^ Value type of records described by the contained row constructor.
  | TDisjoint !Con !Con !Con
    -- ^ Type qualified by proof that the first two row constructors are
    -- disjoint, followed by the qualified body type.
  | CRel !Int
    -- ^ De Bruijn reference to a constructor binder, with zero denoting the
    -- nearest 'CAbs' or 'TCFun' binder.
  | CNamed !GlobalId
    -- ^ Direct reference to a globally allocated constructor identity.
  | CModProj !GlobalId ![String] !String
    -- ^ Constructor selected through a structure.  The fields are the root
    -- structure identity, nested structure path, and final component name;
    -- retaining this path is essential to module abstraction and selfification.
  | CApp !Con !Con
    -- ^ Constructor-level function application.
  | CAbs !String !Kind !Con
    -- ^ Constructor lambda with retained binder name, binder kind, and body.
  | CKAbs !String !Con
    -- ^ Constructor abstraction over a kind variable.  Kind occurrences in
    -- the body use 'KRel'.
  | CKApp !Con !Kind
    -- ^ Application of a kind-polymorphic constructor to a kind argument.
  | TKFun !String !Con
    -- ^ Kind-polymorphic value type.  The retained name binds a kind variable
    -- in the body type.
  | CName !String
    -- ^ Literal record-field name constructor of kind 'KName'.
  | CRecord !Kind ![(Con, Con)]
    -- ^ Ordered row constructor.  The explicit kind is the common kind of
    -- field values; each pair contains a name constructor and its value.
  | CConcat !Con !Con
    -- ^ Ordered concatenation of two row constructors.  Required disjointness
    -- is represented in the environment/constraints, not inside this node.
  | CMap !Kind !Kind
    -- ^ Primitive row-map constructor specialized to its inferred input and
    -- output element kinds.  Its kind is
    -- @(input -> output) -> {input} -> {output}@.
  | CUnit
    -- ^ Sole constructor of kind 'KUnit'.
  | CTuple ![Con]
    -- ^ Tuple of constructors; its kind is the tuple of their individual kinds.
  | CProj !Con !Int
    -- ^ One-based projection from a constructor tuple.
  | CError
    -- ^ Constructor/type recovery sentinel.  It prevents cascaded diagnostics
    -- but is forbidden in a successfully finalized file.
  | CMeta !MetaId !Int !Kind !String
    -- ^ Constructor metavariable.  Besides identity it stores the surrounding
    -- constructor-binder depth at creation, its kind, and a diagnostic label;
    -- depth tracking prevents an escaping local constructor from becoming its
    -- solution.
  deriving stock (Eq, Ord, Show)

-- | Shape classification cached for datatype patterns.  It mirrors the
-- reference elaborator's constructor-shape categories and helps pattern
-- compilation/coverage without changing nominal datatype identity.
data DatatypeKind
  = Enum
    -- ^ Every constructor is nullary.
  | Option
    -- ^ Exactly two constructors, one nullary and one carrying a payload.
  | Default
    -- ^ Any other constructor/payload arrangement.
  deriving stock (Eq, Ord, Show)

-- | Resolved identity of a data constructor used by a pattern.
data PatCon
  = PConVar !GlobalId
    -- ^ Direct reference to a named data-constructor identity in scope.
  | PConProj !GlobalId ![String] !String
    -- ^ Data constructor selected through a root structure identity, nested
    -- path, and component name.
  deriving stock (Eq, Ord, Show)

-- | A typed pattern with its source location.
type Pattern = Located PatternF

-- | Elaborated patterns.  Type information required by a backend's match
-- compiler is made explicit on bindings, constructor parameters, and fields.
data PatternF
  = PVar !String !Con
    -- ^ Variable or wildcard pattern paired with its inferred type.  The name
    -- @_@ remains the non-binding wildcard convention.
  | PPrim !Primitive
    -- ^ Exact primitive-literal pattern.
  | PCon !DatatypeKind !PatCon ![Con] !(Maybe Pattern)
    -- ^ Datatype-constructor pattern.  It stores the datatype shape category,
    -- resolved constructor, instantiated datatype parameters, and optional
    -- payload pattern.
  | PRecord ![(String, Pattern, Con)] !Bool
    -- ^ Typed record pattern.  Every entry contains source field label, nested
    -- pattern, and field type; the Boolean records whether the pattern is
    -- flexible and therefore accepts an unmentioned remainder row.
  deriving stock (Eq, Ord, Show)

-- | A typed expression with its source or generated location.
type Expr = Located ExprF

-- | Elaborated expression language.  Implicit constructor arguments and class
-- dictionaries have been inserted explicitly, and record operations retain
-- the row/type evidence a later backend needs.
data ExprF
  = EPrim !Primitive
    -- ^ Primitive literal.
  | ERel !Int
    -- ^ De Bruijn reference to a local value binder; zero denotes the nearest
    -- lambda, pattern binding, or local recursive binding as determined by the
    -- elaborated environment.
  | ENamed !GlobalId
    -- ^ Direct reference to a globally identified value.
  | EModProj !GlobalId ![String] !String
    -- ^ Value projected through a structure root identity, nested structure
    -- path, and final component name.
  | EApp !Expr !Expr
    -- ^ Ordinary value application.  Synthesized dictionary arguments also
    -- appear as this constructor, so no backend-side instance search remains.
  | EAbs !String !Con !Con !Expr
    -- ^ Value lambda containing retained parameter name, parameter type,
    -- result type, and body.
  | ECApp !Expr !Con
    -- ^ Explicit constructor application.  This includes constructor arguments
    -- inserted by inference as well as those written by the programmer.
  | ECAbs !Explicitness !String !Kind !Expr
    -- ^ Expression abstraction over a constructor, recording binder visibility,
    -- name, kind, and body.
  | EKAbs !String !Expr
    -- ^ Expression abstraction over a kind variable.
  | EKApp !Expr !Kind
    -- ^ Application of a kind-polymorphic expression to a kind.  Kind
    -- instantiations inferred at a use site are materialized with this node.
  | ERecord ![(Con, Expr, Con)]
    -- ^ Record value.  Each ordered entry stores field-name constructor, field
    -- expression, and the field's type.
  | EField !Expr !Con !Con !Con
    -- ^ Record projection with record expression, field-name constructor,
    -- selected field type, and the row of all remaining fields.
  | EConcat !Expr !Con !Expr !Con
    -- ^ Record concatenation with left expression and row followed by right
    -- expression and row.  Their proven disjointness lives in elaboration
    -- evidence; row order remains observable here.
  | ECut !Expr !Con !Con !Con
    -- ^ Remove one field from a record.  The fields are record expression,
    -- field name, removed field type, and remaining row.
  | ECutMulti !Expr !Con !Con
    -- ^ Remove a row of fields from a record, storing the record expression,
    -- removed row, and remaining row.
  | ECase !Expr ![(Pattern, Expr)] !Con !Con
    -- ^ Typed case expression containing scrutinee, ordered branches,
    -- scrutinee/discriminant type, and common branch-result type.
  | EError
    -- ^ Expression recovery sentinel, forbidden after successful finalization.
  | EMeta !MetaId
    -- ^ Expression metavariable used specifically for synthesized class
    -- dictionaries and source expression holes.  Solving replaces it with an
    -- explicit expression before finalized IR is returned.
  | ELet ![EDecl] !Expr !Con
    -- ^ Local declarations, body expression, and body/result type.
  deriving stock (Eq, Ord, Show)

-- | A typed local declaration with its source location.
type EDecl = Located EDeclF

-- | Elaborated declarations permitted inside 'ELet'.
data EDeclF
  = EDVal !Pattern !Con !Expr
    -- ^ Non-recursive local pattern binding with the matched type and value.
  | EDValRec ![(String, Con, Expr)]
    -- ^ Mutually recursive local bindings, each storing source name, checked
    -- type, and elaborated definition.  Local references use 'ERel'.
  deriving stock (Eq, Ord, Show)

-- | Whether instances and constraints nested inside a structure signature are
-- eligible to be imported when the surrounding signature is opened.
data ImportMode
  = Import
    -- ^ Import the nested structure normally, including its eligible instance
    -- and constraint information.
  | Skip
    -- ^ Keep the structure component visible but suppress recursive instance
    -- import.  Wildification uses this for hidden formal-module components.
  deriving stock (Eq, Ord, Show)

-- | A resolved signature item with its source location.
type SigItem = Located SigItemF

-- | Components of a constant elaborated signature.  Each namespace-bearing
-- item carries nominal IDs, and all constructor/type fields have been kinded.
data SigItemF
  = SgiConAbs !String !GlobalId !Kind
    -- ^ Abstract constructor component: public name, nominal identity, and
    -- kind.  No representation is available to clients.
  | SgiCon !String !GlobalId !Kind !Con
    -- ^ Transparent constructor component: name, identity, kind, and defining
    -- constructor.
  | SgiDatatype ![(String, GlobalId, [String], [(String, GlobalId, Maybe Con)])]
    -- ^ Mutually declared nominal datatypes.  Each tuple stores datatype name,
    -- datatype identity, type-parameter names, and data constructors; each data
    -- constructor has its own identity and optional payload type under those
    -- parameters.
  | SgiDatatypeImp !String !GlobalId !GlobalId ![String] !String ![String] ![(String, GlobalId, Maybe Con)]
    -- ^ Imported/projected datatype.  The fields are local name and identity,
    -- original root-structure identity, nested path, original datatype name,
    -- parameter names, and freshly identified local data constructors with
    -- optional payloads.
  | SgiVal !String !GlobalId !Con
    -- ^ Value component with public name, nominal value identity, and type.
  | SgiStr !ImportMode !String !GlobalId !Signature
    -- ^ Nested structure component with import policy, public name, nominal
    -- structure identity, and public signature.
  | SgiSgn !String !GlobalId !Signature
    -- ^ Named-signature component with public name, nominal identity, and
    -- signature value.
  | SgiConstraint !Con !Con
    -- ^ Exported fact that the two row constructors are disjoint.
  | SgiClassAbs !String !GlobalId !Kind
    -- ^ Abstract class constructor with public name, nominal identity, and kind.
  | SgiClass !String !GlobalId !Kind !Con
    -- ^ Transparent class constructor with public name, nominal identity,
    -- declared kind, and representation constructor.
  deriving stock (Eq, Ord, Show)

-- | A resolved module signature with its source location.
type Signature = Located SignatureF

-- | Elaborated signatures.  Constant signatures contain nominal components;
-- other constructors retain just enough path/binder information for lazy
-- projection, refinement, functor matching, and selfification.
data SignatureF
  = SgnConst ![SigItem]
    -- ^ Ordered literal signature items.  Order is significant for visibility,
    -- duplicate handling, and reference-compatible instance behavior.
  | SgnVar !GlobalId
    -- ^ Reference to a named signature by nominal identity.
  | SgnFun !String !GlobalId !Signature !Signature
    -- ^ Functor signature containing parameter name, fresh parameter-structure
    -- identity, domain signature, and result signature.  The result may project
    -- components through the parameter identity.
  | SgnWhere !Signature ![String] !String !Con
    -- ^ Constructor refinement of a base signature at nested structure path
    -- and component name, equating that component with the final constructor.
  | SgnProj !GlobalId ![String] !String
    -- ^ Signature component projected through a root structure identity,
    -- nested path, and final signature name.
  | SgnError
    -- ^ Signature recovery sentinel, forbidden in successful finalized output.
  deriving stock (Eq, Ord, Show)

-- | A fully typed top-level declaration with its source location.
type Decl = Located DeclF

-- | Elaborated declarations.  Source-only annotations and opens have been
-- checked/lowered, while backend-relevant schema, FFI, export, and scheduling
-- declarations remain explicit.
data DeclF
  = DCon !String !GlobalId !Kind !Con
    -- ^ Transparent constructor binding containing source name, nominal
    -- identity, inferred/checked kind, and definition.
  | DDatatype ![(String, GlobalId, [String], [(String, GlobalId, Maybe Con)])]
    -- ^ Mutually declared datatypes.  Each entry stores datatype name and
    -- identity, type-parameter names, and nominal data constructors with
    -- optional payload types.
  | DDatatypeImp !String !GlobalId !GlobalId ![String] !String ![String] ![(String, GlobalId, Maybe Con)]
    -- ^ Imported datatype alias containing local name/identity, original root
    -- structure and path, original datatype name, parameters, and local data
    -- constructor identities/payloads.
  | DVal !String !GlobalId !Con !Expr
    -- ^ Non-recursive named value with source name, nominal identity, checked
    -- type, and elaborated expression.
  | DValRec ![(String, GlobalId, Con, Expr)]
    -- ^ Mutually recursive named values; every tuple stores name, nominal
    -- identity, checked type, and body, with all identities in scope throughout
    -- the group.
  | DSgn !String !GlobalId !Signature
    -- ^ Named signature binding with source name, nominal identity, and
    -- elaborated signature.
  | DStr !String !GlobalId !Signature !Structure
    -- ^ Structure/functor binding with public name, nominal identity, checked
    -- public signature, and elaborated structure expression.
  | DFfiStr !String !GlobalId !Signature
    -- ^ Foreign structure supplied by project configuration.  It has a public
    -- name, nominal identity, and checked restricted signature but no Ur body.
  | DConstraint !Con !Con
    -- ^ Persistent assertion that two row constructors are disjoint.
  | DExport !GlobalId !Signature !Structure
    -- ^ Project export containing the exported structure's fresh root identity,
    -- public signature, and structure expression.
  | DTable !GlobalId !String !GlobalId !Con !Expr !Con !Expr !Con
    -- ^ SQL table declaration.  In order, fields are the nominal identity of
    -- the @Basis@ structure that owns @sql_table@, source name, Ur value
    -- identity, row constructor, primary-key expression, inferred primary-key
    -- row, additional-constraints expression, and inferred uniqueness/
    -- constraint row.
  | DSequence !GlobalId !String !GlobalId
    -- ^ SQL sequence with the owning @Basis@ structure identity, source name,
    -- and Ur value identity.  Its public type is @Basis.sql_sequence@.
  | DView !GlobalId !String !GlobalId !Expr !Con
    -- ^ SQL view with the owning @Basis@ structure identity, source name, Ur
    -- value identity, defining query expression, and inferred output row.
  | DIndex !Expr !Expr
    -- ^ Checked SQL index declaration storing table expression and record of
    -- index modes.  Field-row evidence has already constrained their types.
  | DDatabase !String
    -- ^ Selected database connection string retained for a future backend.
  | DCookie !GlobalId !String !GlobalId !Con
    -- ^ HTTP cookie with the owning @Basis@ structure identity, source name,
    -- Ur value identity, and payload type.  Its public type is
    -- @Basis.http_cookie payload@.
  | DStyle !GlobalId !String !GlobalId
    -- ^ CSS class with the owning @Basis@ structure identity, source name, and
    -- Ur value identity.  Its public type is @Basis.css_class@.
  | DTask !Expr !Expr
    -- ^ Scheduled task containing checked scheduling-kind expression and
    -- handler function.
  | DPolicy !Expr
    -- ^ Checked SQL policy expression.
  | DOnError !GlobalId ![String] !String
    -- ^ Resolved application error handler: root structure identity, nested
    -- structure path, and final value name.
  | DFfi !String !GlobalId ![SFfiMode] !Con
    -- ^ Direct foreign value with Ur name, nominal identity, operational FFI
    -- annotations, and checked Ur type.
  deriving stock (Eq, Ord, Show)

-- | An elaborated structure expression with its source location.
type Structure = Located StructureF

-- | Resolved module expressions.  Each successful structure binding separately
-- carries its public 'Signature'; these nodes retain executable/generative
-- structure shape and nominal references.
data StructureF
  = StrConst ![Decl]
    -- ^ Literal structure body as an ordered sequence of typed declarations.
  | StrVar !GlobalId
    -- ^ Direct reference to a structure's nominal identity.
  | StrProj !Structure !String
    -- ^ Projection of a named nested structure from another structure
    -- expression.
  | StrFun !String !GlobalId !Signature !Signature !Structure
    -- ^ Functor abstraction containing parameter name and nominal identity,
    -- domain signature, checked result signature, and body.  Result projections
    -- may refer to the parameter identity.
  | StrApp !Structure !Structure
    -- ^ Generative functor application after domain matching and result
    -- identity substitution have succeeded.
  | StrError
    -- ^ Structure recovery sentinel, forbidden in successful finalized output.
  deriving stock (Eq, Ord, Show)

-- | Complete backend-neutral elaborated program.  Declaration order preserves
-- source/module sequencing; a successful public result has been zonked and
-- audited so it contains no @KMeta@, @CMeta@, @EMeta@, or error sentinel.
type File = [Decl]
