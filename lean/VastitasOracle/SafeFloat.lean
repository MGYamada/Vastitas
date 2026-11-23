import VastitasOracle.BinaryFloat

set_option autoImplicit false

/-! Proof-only Float and SafeFloat sequencing for a fixed reference profile.
Each operation contributes its own symbolic flags to an ordered trace. The
public mathematical observation projects that trace to its five sticky flags.
Neither this trace nor these flags are observations of a NativeFast run. -/
namespace VastitasOracle.SafeFloat
open BinaryFloat

@[simp] theorem flags_left_unit (a : Flags) : ({} : Flags).merge a = a := by
  cases a; simp [Flags.merge]
@[simp] theorem flags_right_unit (a : Flags) : a.merge {} = a := by
  cases a; simp [Flags.merge]
theorem flags_assoc (a b c : Flags) : (a.merge b).merge c = a.merge (b.merge c) := by
  cases a; cases b; cases c; simp [Flags.merge, Bool.or_assoc]
theorem flags_comm (a b : Flags) : a.merge b = b.merge a := by
  cases a; cases b; simp [Flags.merge, Bool.or_comm]
@[simp] theorem flags_idempotent (a : Flags) : a.merge a = a := by
  cases a; simp [Flags.merge]

inductive Op where
  | convert | add | sub | mul | div | guardPass | guardFail
  deriving DecidableEq, Repr

structure Event where
  site : String
  operation : Op
  flags : Flags := {}
  deriving DecidableEq, Repr

def flags : List Event → Flags
  | [] => {}
  | e :: rest => e.flags.merge (flags rest)

@[simp] theorem flags_append (xs ys : List Event) :
    flags (xs ++ ys) = (flags xs).merge (flags ys) := by
  induction xs with
  | nil => simp [flags]
  | cons e es ih => simp [flags, ih, flags_assoc]

structure Audit (α : Type) where
  value : α
  events : List Event := []

abbrev Raw (α : Type) := Unit → Audit α
inductive Failure where | divisionByZero deriving DecidableEq, Repr
abbrev Safe (α : Type) := Raw (Except Failure α)

variable {α β γ : Type}

/-- Equality of observations uses equality of the carrier itself. A Scalar
therefore compares by bits, including on signed zeros and every NaN. -/
def run (p : Raw α) (cfg : Unit) : Local α :=
  let a := p cfg
  ⟨a.value, flags a.events⟩

def rawPure (x : α) : Raw α := fun _ => ⟨x, []⟩

def rawBind (p : Raw α) (k : α → Raw β) : Raw β := fun cfg =>
  let a := p cfg
  let b := k a.value cfg
  ⟨b.value, a.events ++ b.events⟩

def safePure (x : α) : Safe α := rawPure (.ok x)
def fail (err : Failure) : Safe α := rawPure (.error err)

def safeBind (p : Safe α) (k : α → Safe β) : Safe β :=
  rawBind p fun
    | .ok x => k x
    | .error e => fail e

def lift (p : Raw α) : Safe α := fun cfg =>
  let a := p cfg
  ⟨.ok a.value, a.events⟩

@[simp] theorem raw_left_unit (x : α) (k : α → Raw β) :
    rawBind (rawPure x) k = k x := by funext cfg; simp [rawBind, rawPure]
@[simp] theorem raw_right_unit (p : Raw α) : rawBind p rawPure = p := by
  funext cfg; simp [rawBind, rawPure]
theorem raw_assoc (p : Raw α) (k : α → Raw β) (g : β → Raw γ) :
    rawBind (rawBind p k) g = rawBind p (fun x => rawBind (k x) g) := by
  funext cfg; simp [rawBind, List.append_assoc]

@[simp] theorem safe_left_unit (x : α) (k : α → Safe β) :
    safeBind (safePure x) k = k x := by simp [safeBind, safePure]
@[simp] theorem safe_right_unit (p : Safe α) : safeBind p safePure = p := by
  funext cfg
  cases h : p cfg with
  | mk v t => cases v <;> simp [safeBind, safePure, rawBind, rawPure, fail, h]

theorem safe_assoc (p : Safe α) (k : α → Safe β) (g : β → Safe γ) :
    safeBind (safeBind p k) g = safeBind p (fun x => safeBind (k x) g) := by
  unfold safeBind
  rw [raw_assoc]
  congr 1
  funext v
  cases v <;> simp [fail]

@[simp] theorem lift_pure (x : α) : lift (rawPure x) = safePure x := rfl
theorem lift_bind (p : Raw α) (k : α → Raw β) :
    lift (rawBind p k) = safeBind (lift p) (fun x => lift (k x)) := rfl

theorem raw_projection (p : Raw α) (k : α → Raw β) (cfg : Unit) :
    run (rawBind p k) cfg = (run p cfg >>= fun x => run (k x) cfg) := by
  simp [run, rawBind, bind]

theorem safe_projection (p : Safe α) (k : α → Safe β) (cfg : Unit) :
    run (safeBind p k) cfg = (run p cfg >>= fun
      | .ok v => run (k v) cfg
      | .error e => pure (.error e)) := by
  simp only [safeBind, raw_projection]
  cases h : (p cfg).value <;> simp [bind, pure, fail, rawPure, run, flags, h]

def Same (p q : Raw α) := ∀ cfg, run p cfg = run q cfg

theorem raw_congr {p q : Raw α} {k g : α → Raw β} (first : Same p q)
    (next : ∀ x, Same (k x) (g x)) : Same (rawBind p k) (rawBind q g) := by
  intro cfg
  simp only [raw_projection, first cfg, next _ cfg]

theorem safe_congr {p q : Safe α} {k g : α → Safe β} (first : Same p q)
    (next : ∀ x, Same (k x) (g x)) : Same (safeBind p k) (safeBind q g) := by
  intro cfg
  simp only [safe_projection, first cfg, next _ cfg]

theorem lift_projection (p : Raw α) (cfg : Unit) :
    run (lift p) cfg = ⟨.ok (run p cfg).value, (run p cfg).flags⟩ := rfl

theorem lift_error_as_data (e : Failure) (cfg : Unit) :
    run (lift (rawPure (.error e : Except Failure α))) cfg = ⟨.ok (.error e),{}⟩ := rfl

theorem scalar_representation {f : Format} (a b : Scalar f) :
    a = b ↔ a.bits = b.bits := by cases a; cases b; simp

variable {f : Format}

private def primitive (site : String) (op : Op) (x : Local α) : Raw α :=
  fun _ => ⟨x.value, [⟨site, op, x.flags⟩]⟩
def convert (f : Format) (x : Rat) (site : String) : Raw (Scalar f) :=
  primitive site .convert (roundRNE f x)

inductive Arithmetic where | add | sub | mul | div deriving DecidableEq

def binary (op : Arithmetic) (a b : Scalar f) (site : String) : Raw (Scalar f) :=
  match op with
  | .add => primitive site .add (BinaryFloat.add a b)
  | .sub => primitive site .sub (BinaryFloat.sub a b)
  | .mul => primitive site .mul (BinaryFloat.mul a b)
  | .div => primitive site .div (ieeeDiv a b)

/-- This checked operation guards the represented divisor before evaluating
raw IEEE division. Ordinary totalized real division has a separate definition. -/
def checkedDiv (a b : Scalar f) (site : String) : Safe (Scalar f) :=
  if isZero b then fun _ => ⟨.error .divisionByZero, [⟨site, .guardFail, {}⟩]⟩
  else rawBind (primitive site .guardPass (pure ())) fun _ => lift (binary .div a b site)

theorem zero_patterns (b : Scalar f) : isZero b = true ↔ b = zero f ∨ b = zero f true := by
  simp only [scalar_representation b, ← BitVec.toNat_inj]
  have bounded := b.bits.isLt
  cases f
  · change (b.bits.toNat % 2147483648 == 0) = true ↔
      b.bits.toNat = 0 ∨ b.bits.toNat = 2147483648
    change b.bits.toNat < 4294967296 at bounded
    simp only [beq_iff_eq]; omega
  · change (b.bits.toNat % 9223372036854775808 == 0) = true ↔
      b.bits.toNat = 0 ∨ b.bits.toNat = 9223372036854775808
    change b.bits.toNat < 18446744073709551616 at bounded
    simp only [beq_iff_eq]; omega

theorem guard_fail (a b : Scalar f) (site : String) (zeroBits : b = zero f ∨ b = zero f true)
    (cfg : Unit) : checkedDiv a b site cfg =
      ⟨.error .divisionByZero, [⟨site,.guardFail,{}⟩]⟩ := by
  simp [checkedDiv, (zero_patterns b).mpr zeroBits]

theorem guard_pass (a b : Scalar f) (site : String) (nonzero : isZero b = false) (cfg : Unit) :
    checkedDiv a b site cfg = ⟨.ok (ieeeDiv a b).value,
      [⟨site,.guardPass,{}⟩, ⟨site,.div,(ieeeDiv a b).flags⟩]⟩ := by
  simp [checkedDiv, nonzero, rawBind, lift, binary, primitive, pure]

/-- Recover a failed zero guard by multiplying the original operands. The
result bits and sticky flags agree with totalized real division for all bit
patterns in either format, including exceptional numerators. -/
theorem recover_checked_real_div (a b : Scalar f) (site : String) (cfg : Unit) :
    ((run (checkedDiv a b site) cfg) >>= fun
      | .ok x => pure x
      | .error .divisionByZero => BinaryFloat.mul a b) = realDiv a b := by
  cases h : isZero b with
  | true =>
    simp [run, guard_fail a b site ((zero_patterns b).mp h), realDiv, h, flags, bind]
  | false =>
    simp [run, guard_pass a b site h, realDiv, h, flags, bind, pure]

theorem first_error (p : Safe α) (k : α → Safe β) (cfg : Unit) (e : Failure)
    (failed : (p cfg).value = .error e) :
    safeBind p k cfg = ⟨.error e,(p cfg).events⟩ := by
  simp [safeBind, rawBind, failed, fail, rawPure]

def divide (left right : Safe (Scalar f)) (site : String) : Safe (Scalar f) :=
  safeBind left fun a => safeBind right fun b => checkedDiv a b site

theorem divide_first_error (left right : Safe (Scalar f)) (site : String) (cfg : Unit)
    (e : Failure) (h : (left cfg).value = .error e) :
    divide left right site cfg = ⟨.error e,(left cfg).events⟩ :=
  first_error _ _ _ e h

theorem divide_right_error (left right : Safe (Scalar f)) (a : Scalar f) (site : String) (cfg : Unit)
    (ok : (left cfg).value = .ok a) (e : Failure) (h : (right cfg).value = .error e) :
    divide left right site cfg = ⟨.error e,(left cfg).events ++ (right cfg).events⟩ := by
  simp [divide, safeBind, rawBind, ok, h, fail, rawPure]

theorem divide_order (left right : Safe (Scalar f)) (a b : Scalar f) (site : String) (cfg : Unit)
    (hl : (left cfg).value = .ok a) (hr : (right cfg).value = .ok b) :
    divide left right site cfg = ⟨(checkedDiv a b site cfg).value,
      (left cfg).events ++ (right cfg).events ++ (checkedDiv a b site cfg).events⟩ := by
  simp [divide, safeBind, rawBind, hl, hr, List.append_assoc]

def choose (condition : Safe Bool) (yes no : Unit → Safe α) : Safe α :=
  safeBind condition fun b => if b then yes () else no ()

theorem choose_true (condition : Safe Bool) (yes no : Unit → Safe α) (cfg : Unit)
    (h : (condition cfg).value = .ok true) :
    choose condition yes no cfg = ⟨(yes () cfg).value,(condition cfg).events ++ (yes () cfg).events⟩ := by
  simp [choose, safeBind, rawBind, h]

theorem choose_false (condition : Safe Bool) (yes no : Unit → Safe α) (cfg : Unit)
    (h : (condition cfg).value = .ok false) :
    choose condition yes no cfg = ⟨(no () cfg).value,(condition cfg).events ++ (no () cfg).events⟩ := by
  simp [choose, safeBind, rawBind, h]

theorem choose_error (condition : Safe Bool) (yes no : Unit → Safe α) (cfg : Unit)
    (e : Failure) (h : (condition cfg).value = .error e) :
    choose condition yes no cfg = ⟨.error e,(condition cfg).events⟩ :=
  first_error _ _ _ e h

/-- Different first failure sites have the same minimal observation. -/
theorem failed_site_projection (a b : Scalar f) (x y : String)
    (hz : b = zero f ∨ b = zero f true) :
    Same (checkedDiv a b x) (checkedDiv a b y) := by
  intro cfg
  simp only [run, guard_fail a b _ hz, flags]

namespace Regression

/-- Raw binary32 division runs twice. The sign changes on the result while
both event occurrences contribute the same sticky divide-by-zero flag. -/
private def repeated : Raw (Scalar .binary32) :=
  rawBind (binary .div (one .binary32) (zero _) "first") fun _ =>
    binary .div (one _) (zero _ true) "second"

example : run repeated () = ⟨infinity .binary32 true, { divideByZero := true }⟩ := rfl
example : (repeated ()).events =
    [⟨"first", .div, { divideByZero := true }⟩, ⟨"second", .div, { divideByZero := true }⟩] := rfl

/-- The binary64 signaling numerator does not raise invalid on the failed
guard. Earlier underflow and inexact survive, and later work has no events. -/
private def stopped : Safe (Scalar .binary64) :=
  safeBind (lift (convert .binary64 (Rat.divInt 1 (2^1075)) "underflow")) fun divisor =>
    safeBind (checkedDiv (fromBits .binary64 0x7ff0000000000001) divisor "guard") fun _ =>
      lift (binary .div (one _) (zero _) "skipped")

#eval show IO Unit from do
  let ⟨.error .divisionByZero, observed⟩ := run stopped ()
    | throw (IO.userError "expected the rounded-zero guard to reject")
  let tiny : Flags := { underflow := true, inexact := true }
  unless observed == tiny && (stopped ()).events ==
      [⟨"underflow", .convert, tiny⟩, ⟨"guard", .guardFail, {}⟩] do
    throw (IO.userError "checked division lost earlier flags or ran the skipped branch")

end Regression
end VastitasOracle.SafeFloat
