import VastitasKernel.Surface

/-! Protocol 3 retains unresolved paths and declaration provenance. Files are
placement metadata; only package identity and logical modules determine owners. -/
namespace VastitasKernel.Namespace

structure PackageId where
  source : String
  name : String
  version : String
  deriving Repr, Inhabited, DecidableEq, BEq, ReflBEq, LawfulBEq, Hashable

structure Scope where
  package : PackageId
  path : List String
  deriving Repr, Inhabited, DecidableEq, BEq, ReflBEq, LawfulBEq, Hashable

structure Owner where
  scope : Scope
  name : String
  deriving Repr, Inhabited, DecidableEq, BEq, ReflBEq, LawfulBEq, Hashable

inductive Kind where
  | module | function | generic | abstractType
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

structure Generic extends RawGeneric where
  isPublic : Bool
  deriving Repr, Inhabited

structure AbstractType extends RawAbstractType where
  isPublic : Bool
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
    (m.generics.map fun g => ⟨⟨scope, g.name⟩, .generic, g.isPublic⟩) ++
    (m.abstractTypes.map fun t => ⟨⟨scope, t.name⟩, .abstractType, t.isPublic⟩) ++
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
