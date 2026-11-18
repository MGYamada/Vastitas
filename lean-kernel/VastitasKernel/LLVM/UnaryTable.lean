import VastitasKernel.FiniteTables
import VastitasKernel.LLVM.TableSwitch

set_option autoImplicit false

/-! Qualification of a closed unary finite table. Carrier declarations fix
both ordinal orders independently of the textual order of the table rows. -/
namespace VastitasKernel.LLVM.UnaryTable

open Indexed TableSwitch

/-- The result must have the declared carrier and actually occupy the returned
ordinal in that carrier. In particular, a missing name cannot become a tag. -/
def entry (env : Environment) (table input output : DeclId) (range : List String)
    (name : String) : Option Tag := do
  let (owner, result) ← FiniteTables.lookupTag env table [(input, name)]
  guard (owner == output)
  let i := range.idxOf result
  guard (range[i]? == some result)
  if small : i < 4096 then return ⟨i, small⟩ else none

private theorem mapped_entry {α β : Type} (f : α → Option β) (xs : List α) (ys : List β)
    (success : xs.mapM f = some ys) (i : Nat) : ys[i]? = xs[i]?.bind f := by
  induction xs generalizing ys i with
  | nil =>
    simp at success
    subst ys
    simp
  | cons x xs ih =>
    rw [List.mapM_cons] at success
    cases head : f x with
    | none => simp [head] at success
    | some y =>
      cases tail : xs.mapM f with
      | none => simp [head, tail] at success
      | some rest =>
        simp [head, tail] at success
        subst ys
        cases i with
        | zero => simp [head]
        | succ i => simpa using ih rest tail i

/-- A successful image retains a checked equation for every input ordinal.
Out-of-domain inputs are represented by `none` on both sides. -/
structure Image (env : Environment) (table : DeclId) (header : TargetHeader) where
  input : DeclId
  output : DeclId
  rows : List (List String × String)
  signature : lookup env table = some (.finiteTable [input] output rows)
  domain : List String
  range : List String
  inputCarrier : FiniteTables.carrier env input = some domain
  outputCarrier : FiniteTables.carrier env output = some range
  outputs : List Tag
  total : outputs.length = domain.length
  bound : outputs.length ≤ 4096
  correspondence : ∀ i : Nat, outputs[i]? = domain[i]?.bind (entry env table input output range)

def lower (env : Environment) (table : DeclId) (header : TargetHeader) :
    Option (Image env table header) :=
  match receipt : lookup env table with
  | some (.finiteTable [input] output rows) =>
    match dom : FiniteTables.carrier env input, cod : FiniteTables.carrier env output with
    | some domain, some range =>
      let f := entry env table input output range
      match success : domain.mapM f with
      | some tags =>
        if h : tags.length = domain.length ∧ tags.length ≤ 4096 then
          some ⟨input, output, rows, receipt, domain, range, dom, cod, tags, h.1, h.2,
            mapped_entry f domain tags success⟩
        else none
      | none => none
    | _, _ => none
  | _ => none

def Image.toModule {env : Environment} {table : DeclId} {header : TargetHeader}
    (image : Image env table header) : TableSwitch.Module :=
  ⟨header, image.outputs, image.bound⟩

theorem accepted_bytes {env : Environment} {table : DeclId} {header : TargetHeader}
    (image : Image env table header) (bytes : List UInt8) :
    TableSwitch.parse bytes = some image.toModule ↔ bytes = TableSwitch.print image.toModule :=
  TableSwitch.parse_iff _ _

end VastitasKernel.LLVM.UnaryTable
