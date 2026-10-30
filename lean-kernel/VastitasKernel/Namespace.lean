import VastitasKernel.Surface
import VastitasKernel.Identity

/-! Protocol 3 retains unresolved paths and declaration provenance. Files are
placement metadata; only package identity and logical modules determine owners. -/
namespace VastitasKernel.Namespace

inductive Kind where
  | module | function | generic | abstractType | grant | contribution | delegation | transfer
  | indexedDeclaration | resourceFunction
  deriving Repr, Inhabited, DecidableEq, BEq

structure Target where
  owner : Owner
  kind : Kind
  isPublic : Bool
  deriving Repr, Inhabited, DecidableEq, BEq

structure Import where
  path : List String
  alias : String
  isPublic : Bool
  span : Span
  deriving Repr, Inhabited

structure Function extends Surface.Function where
  isPublic : Bool
  deriving Repr, Inhabited

/-- A resource declaration contributes a name, never a fabricated pure body.
The combined source checker must separately accept its actual resource body. -/
structure ResourceHeader where
  name : String
  isPublic : Bool
  span : Span
  deriving Repr, Inhabited

structure Generic extends RawGeneric where
  isPublic : Bool
  deriving Repr, Inhabited

structure AbstractType extends RawAbstractType where
  isPublic : Bool
  deriving Repr, Inhabited

structure Grant where
  name : String
  target : List String
  granteeSource : String
  granteePath : List String
  region : List (List String)
  delegable : Bool := false
  span : Span
  isPublic : Bool
  deriving Repr, Inhabited

structure Transfer where
  name : String
  target : List String
  granteeSource : String
  granteePath : List String
  span : Span
  isPublic : Bool
  deriving Repr, Inhabited

structure Contribution where
  name : String
  target : List String
  methods : List Surface.Method
  span : Span
  isPublic : Bool
  deriving Repr, Inhabited

inductive EditEvent where
  | borrow (grant : List String) (loan : String) (span : Span)
  | apply (contribution : List String) (loan : Option String) (span : Span)
  | release (loan : String) (span : Span)
  | seal (target : List String) (span : Span)
  | reborrow (parent : String) (delegation : List String) (loan : String) (span : Span)
  | transfer (declaration : List String) (span : Span)
  deriving Repr, Inhabited

def EditEvent.span : EditEvent → Span
  | .borrow _ _ span | .apply _ _ span | .release _ span | .seal _ span
    | .reborrow _ _ _ span | .transfer _ span => span

def EditEvent.authority : EditEvent → Bool
  | .reborrow .. | .transfer .. => true
  | _ => false

structure Assembly where
  events : List EditEvent
  span : Span
  deriving Repr, Inhabited

structure Module where
  path : List String
  isPublic : Bool
  imports : List Import
  functions : List Function
  generics : List Generic
  methods : List Surface.Method
  abstractTypes : List AbstractType := []
  subtypes : List RawSubtype := []
  abstractMethods : List RawAbstractMethod := []
  grants : List Grant := []
  delegations : List Grant := []
  transfers : List Transfer := []
  contributions : List Contribution := []
  assembly : Option Assembly := none
  resourceFunctions : List ResourceHeader := []
  span : Span
  deriving Repr, Inhabited

structure Dependency where
  alias : String
  target : String -- canonical manifest location, not a frontend function ID
  deriving Repr, Inhabited

structure Package where
  id : PackageId
  dependencies : List Dependency
  modules : List Module
  deriving Repr, Inhabited

structure Program where
  extended : Bool := false
  editable : Bool := false
  authority : Bool := false
  file : String
  root : String
  packages : List Package
  deriving Repr, Inhabited

def Program.scopes (p : Program) : List Scope :=
  p.packages.flatMap fun pkg => pkg.modules.map fun m => ⟨pkg.id, m.path⟩

def Program.declarations (p : Program) : List Target :=
  p.packages.flatMap fun pkg => pkg.modules.flatMap fun m =>
    let scope : Scope := ⟨pkg.id, m.path⟩
    (m.functions.map fun f => ⟨⟨scope, f.name⟩, .function, f.isPublic⟩) ++
    (m.resourceFunctions.map fun f => ⟨⟨scope, f.name⟩, .resourceFunction, f.isPublic⟩) ++
    (m.generics.map fun g => ⟨⟨scope, g.name⟩, .generic, g.isPublic⟩) ++
    (m.abstractTypes.map fun t => ⟨⟨scope, t.name⟩, .abstractType, t.isPublic⟩) ++
    (m.grants.map fun g => ⟨⟨scope, g.name⟩, .grant, g.isPublic⟩) ++
    (m.delegations.map fun g => ⟨⟨scope, g.name⟩, .delegation, g.isPublic⟩) ++
    (m.transfers.map fun t => ⟨⟨scope, t.name⟩, .transfer, t.isPublic⟩) ++
    (m.contributions.map fun c => ⟨⟨scope, c.name⟩, .contribution, c.isPublic⟩) ++
    (if m.path.isEmpty then [] else
      [⟨⟨⟨pkg.id, m.path.dropLast⟩, m.path.getLast!⟩, .module, m.isPublic⟩])

/-- Internal, backend-built declaration index. It is not a wire input. The list
retains declaration order for diagnostics and duplicate checks; both indexes use
first-declaration precedence, including on invalid duplicate input. -/
structure Indexed extends Program where
  declarations : List Target
  byOwner : Std.HashMap Owner Target
  byScope : Std.HashMap Scope (List Target)

def ownerIndex (declarations : List Target) : Std.HashMap Owner Target :=
  declarations.foldr (fun target table => table.insert target.owner target) {}

def scopeIndex (declarations : List Target) : Std.HashMap Scope (List Target) :=
  declarations.foldr (fun target table =>
    table.insert target.owner.scope (target :: table[target.owner.scope]?.getD [])) {}

def Program.indexed (program : Program) : Indexed :=
  let declarations := program.declarations
  { toProgram := program, declarations,
    byOwner := ownerIndex declarations, byScope := scopeIndex declarations }

def Target.moduleScope (t : Target) : Scope :=
  ⟨t.owner.scope.package, t.owner.scope.path ++ [t.owner.name]⟩

def visible (requester : Scope) (target : Target) : Bool :=
  target.isPublic || (requester.package == target.owner.scope.package &&
    target.owner.scope.path.isPrefixOf requester.path)

-- Length-prefixed code point encoding is injective and contains only identifier
-- characters. It avoids dependence on input order, file placement, and aliases.
def encode (s : String) : String :=
  s!"{s.length}_" ++ String.intercalate "_" (s.toList.map (toString ∘ Char.toNat)) ++ "_"

def Owner.symbol (owner : Owner) : String :=
  "ns_f_" ++ encode owner.scope.package.source ++ encode owner.scope.package.name ++
    encode owner.scope.package.version ++
    String.intercalate "" (owner.scope.path.map encode) ++ "end_" ++ encode owner.name

def localName (name : String) : String := "ns_b_" ++ name

end VastitasKernel.Namespace
