import VastitasKernel.MidIR.IR

set_option autoImplicit false

namespace VastitasKernel.MidIR
open Indexed

/-- The four ground literal constructors in checked Core. -/
inductive Literal where
  | unit | boolean (b : Bool) | natural (n : Nat) | integer (i : Int)

def Literal.term : Literal → Core.Term
  | .unit => .unit | .boolean b => .boolean b | .natural n => .natural n | .integer i => .integer i

def Literal.opcode (lit : Literal) (phase : Phase) : Opcode phase :=
  match lit with
  | .unit => .unit | .boolean b => .boolean b | .natural n => .natural n | .integer i => .integer i

/-- Named by the Lean declaration, independent of source spelling. -/
def Literal.origin : Literal → Lean.Name
  | .unit => ``Core.Term.unit | .boolean _ => ``Core.Term.boolean
  | .natural _ => ``Core.Term.natural | .integer _ => ``Core.Term.integer

def Literal.registryRow (lit : Literal) : Lean.Name × String :=
  (lit.origin, (lit.opcode .optimization).tag)

def literalRegistry : List (Lean.Name × String) :=
  ([.unit, .boolean false, .natural 0, .integer 0] : List Literal).map Literal.registryRow

theorem Literal.registered (lit : Literal) : lit.registryRow ∈ literalRegistry := by
  cases lit <;> simp [literalRegistry, Literal.registryRow, Literal.origin, Literal.opcode, Opcode.tag]

end VastitasKernel.MidIR
