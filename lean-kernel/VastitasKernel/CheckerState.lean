import VastitasKernel.Core

/-! Checker state, its monad and the name checks of the retained Surface checker
(`Checker.lean`). The live dispatch and namespace modules use them without
importing that checker. -/
namespace VastitasKernel
namespace Checker.Internal

structure Binding where
  name : String
  symbol : Nat
  ty : Ty
  objectRef : Option ObjectRef := none
  deriving Inhabited

structure Signature where
  id : Nat
  raw : RawFunction
  params : List Binding
  result : Ty
  deriving Inhabited

abbrev Signatures := Std.HashMap String Signature

structure Result where
  term : Term
  deriving Inhabited

def Result.objectRef (result : Result) : Option ObjectRef := result.term.resultType.objectRef

def Binding.resultType (binding : Binding) : ResultType := ⟨binding.ty, binding.objectRef⟩

def Binding.checked (binding : Binding) : CheckedParam := ⟨binding.symbol, binding.resultType⟩

-- Provenance is diagnostic metadata. It never authorizes endpoint equality or
-- changes the nominal identity carried by the independently checked types.
structure ObjectOrigin where
  bindingName : Option String := none
  span : Span
  reason : String
  deriving Inhabited

structure CheckerState where
  nextSymbol : Nat := 1
  origins : Std.HashMap ObjectRef ObjectOrigin := {}
  deriving Inhabited

abbrev Context := List Binding
abbrev CheckM := StateT CheckerState (Except Diagnostic)

def fail (span : Span) (code message : String)
    (notes : List DiagnosticNote := []) : CheckM α :=
  throw { code, message, span, notes }

abbrev checkingBudgetExceeded (span : Span) : CheckM α :=
  fail span "E_LIMIT" s!"function exceeds the checking budget of {Limits.bodyChecking} units along one checking path"

def fresh : CheckM Nat := do
  let state ← get
  set { state with nextSymbol := state.nextSymbol + 1 }
  pure state.nextSymbol

def reserved : List String :=
  ["Affine", "Base", "origin", "id", "compose", "apply", "dim", "int", "pair", "pair_first", "pair_second", "Pair",
   "QQ", "CInfReal", "Nat", "Int", "Bool", "Unit", "Scheme", "CInfScheme",
   "Point", "Morphism", "Pointed", "Fn", "fn", "let", "if", "else", "pack", "unpack", "as", "true", "false",
   "return", "while", "for", "loop", "mut"]

/-- Presentation only (#778): the note on a call of `dimension` that names
nothing. `dimension` is an ordinary name and no operation; the dimension of a
vector or affine space is the operation `dim`. Acceptance never reads it. -/
def retiredDimension (name : String) (span : Span) (diagnostic : Diagnostic) : Diagnostic :=
  if name == "dimension" && diagnostic.code == "E_NAME" then
    { diagnostic with notes := diagnostic.notes ++ [{ span, message :=
      "the dimension of a vector or affine space is `dim(…)`, and physical dimensions are `nature::dimension`" }] }
  else diagnostic

def validName (name : String) : Bool :=
  let chars := name.toList
  match chars with
  | [] => false
  | first :: rest => (first.isAlpha && first.toNat < 128 || first == '_') &&
      rest.all (fun c => (c.isAlphanum && c.toNat < 128) || c == '_')

def checkName (name : String) (span : Span) : CheckM Unit := do
  unless validName name do fail span "E_NAME" s!"invalid identifier '{name}'"
  if reserved.contains name then fail span "E_RESERVED" s!"'{name}' is reserved"

def checkNewBinding (ctx : Context) (name : String) (span : Span) : CheckM Unit := do
  checkName name span
  if ctx.any (fun b => b.name == name) then
    fail span "E_DUPLICATE" s!"binding '{name}' is already in scope; shadowing is not allowed"

end Checker.Internal
end VastitasKernel
