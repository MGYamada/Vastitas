import VastitasKernel.LLVM.TableSwitch

set_option autoImplicit false

/-! A two-export module with one direct i32(i32) call. The canonical callee
is a unary table switch; the caller forwards its argument and returns the
callee's result. Source names and nominal types are bound by the checked
specialization. The fixed exports use a distinct ABI symbol for each role. -/
namespace VastitasKernel.LLVM.ForwardCall

structure Module where
  lookup : TableSwitch.Module
  deriving DecidableEq

inductive Symbol where | lookup | forward

def evaluate (m : Module) (symbol : Symbol) (arg : UInt32) : UInt32 :=
  match symbol with
  | .lookup => TableSwitch.evaluate m.lookup arg
  | .forward => TableSwitch.evaluate m.lookup arg

def caller := TableSwitch.ascii
  "\ndefine i32 @vq_forward(i32 %tag) {\nentry:\n  %result = call i32 @vq_lookup(i32 %tag)\n  ret i32 %result\n}\n"

def print (m : Module) := TableSwitch.print m.lookup ++ caller

/-- Enforce the exact fixed caller as well as the complete canonical
callee, before handing any bytes to the external LLVM parser. -/
def parse (xs : List UInt8) : Option Module := do
  guard (xs.length ≤ TableSwitch.maxBytes + caller.length)
  let n := xs.length - caller.length
  guard (xs.drop n == caller)
  return ⟨← TableSwitch.parse (xs.take n)⟩

theorem parse_iff (xs : List UInt8) (m : Module) :
    parse xs = some m ↔ xs = print m := by
  constructor
  · intro h
    simp [parse, Option.bind_eq_some_iff] at h
    obtain ⟨_, ⟨_, htail⟩, lookup, hp, rfl⟩ := h
    have suffix : xs.drop (xs.length - caller.length) = caller := by
      by_cases same : xs.drop (xs.length - caller.length) = caller
      · exact same
      · simp [guard, same, failure] at htail
    change xs = TableSwitch.print lookup ++ caller
    exact (List.take_append_drop _ _).symm.trans (by rw [(TableSwitch.parse_iff _ _).mp hp, suffix])
  · rintro rfl
    have limit := TableSwitch.print_length_le m.lookup
    have round := (TableSwitch.parse_iff (TableSwitch.print m.lookup) m.lookup).mpr rfl
    simp [parse, print, limit, round, guard]

end VastitasKernel.LLVM.ForwardCall
