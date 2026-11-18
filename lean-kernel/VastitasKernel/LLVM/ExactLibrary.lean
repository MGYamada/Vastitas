import VastitasKernel.LLVM.Syntax
import VastitasKernel.MidIR.IR

set_option autoImplicit false

/-! Straight-line boxed integer library ABI. Parameters are borrowed. Each
instruction defines an owned result. The return transfers a single ownership
to the caller, retaining it first only when the selected slot is borrowed. -/
namespace VastitasKernel.LLVM.ExactLibrary
open MidIR

inductive Step where
  | nat (value : Nat)
  | int (value : Int)
  | apply (op : ExactOp) (args : List Nat)
  deriving DecidableEq

inductive Kind where
  | nat | int
  deriving DecidableEq, Repr

def Kind.name : Kind → String | .nat => "Nat" | .int => "Int"
def Kind.read : String → Option Kind | "Nat" => some .nat | "Int" => some .int | _ => none
def Kind.ofTy : MidIR.Ty → Option Kind | .nat => some .nat | .int => some .int | _ => none
def Kind.type : Kind → MidIR.Ty | .nat => .nat | .int => .int

structure Code where
  header : TargetHeader
  params : List Kind
  resultType : Kind
  steps : List Step
  result : Nat
  deriving DecidableEq

def Code.arity (c : Code) := c.params.length

def slot (i : Nat) := s!"%v{i}"
def arg (i : Nat) := "ptr " ++ slot i
def symbol (name : String) := "@vastitas_" ++ name ++ "_v1"

def Step.literal : Step → Option String
  | .int n => some (toString n) | .nat n => some (toString n) | _ => none

def Step.callee : Step → String
  | .int _ => "int_decimal" | .nat _ => "nat_decimal" | .apply op _ => op.name

def Step.argCount : Step → Nat
  | .apply op _ => op.operands.length | _ => 1

def global (value : String) (i : Nat) (scope : String := "") :=
  s!"@c{scope}{i} = private constant [{value.length+1} x i8] c\"{value}\\00\""

def call (s : Step) (i : Nat) (scope : String := "") :=
  let args := match s with
    | .apply _ refs => refs.map arg
    | _ => [s!"ptr @c{scope}{i}"]
  "  " ++ slot i ++ " = call ptr " ++ symbol s.callee ++ "(" ++ String.intercalate ", " args ++ ")"

def rcCall (name : String) (i : Nat) :=
  "  call void " ++ symbol name ++ "(" ++ arg i ++ ")"

def Code.releases (c : Code) : List Nat :=
  ((List.range' c.arity c.steps.length).reverse).filter (· != c.result)

theorem Code.release_iff (c : Code) (i : Nat) :
    i ∈ c.releases ↔ c.arity ≤ i ∧ i < c.arity + c.steps.length ∧ i ≠ c.result := by
  simp [Code.releases, and_assoc]

theorem Code.releases_once (c : Code) : c.releases.Nodup :=
  List.Pairwise.filter _ (List.pairwise_reverse.mpr
    ((List.nodup_range' (s := c.arity) (n := c.steps.length) 1).imp Ne.symm))

def Code.print (c : Code) : List UInt8 := Id.run do
  let operations := c.steps.zipIdx c.arity
  let globals := operations.filterMap fun (s,i) => s.literal.map (fun v => global v i)
  let declarations := (c.steps.map fun s => "declare ptr " ++ symbol s.callee ++ "(" ++
    String.intercalate ", " (List.replicate s.argCount "ptr") ++ ")").eraseDups
  let keep := c.result < c.arity
  let drops := c.releases
  let rc := (if keep then ["retain"] else []) ++ (if drops.isEmpty then [] else ["release"])
  let signature := "define ptr @vq_exact(" ++ String.intercalate ", " ((List.range c.arity).map arg) ++ ") {"
  let contract := "; boxed (" ++ String.intercalate ", " (c.params.map Kind.name) ++ ") -> " ++ c.resultType.name
  let lines := [contract] ++ globals ++ declarations ++ rc.map (fun n => "declare void " ++ symbol n ++ "(ptr)") ++
    [signature,"entry:"] ++ operations.map (fun (s,i) => call s i) ++
    (if keep then [rcCall "retain" c.result] else []) ++ drops.map (rcCall "release") ++
    ["  ret " ++ arg c.result,"}"]
  return c.header.print ++ ("\n" ++ String.intercalate "\n" lines ++ "\n").toUTF8.data.toList

def Code.valid (c : Code) : Bool := Id.run do
  unless c.arity + c.steps.length ≤ 4096 do return false
  let mut slots := (c.params.map Kind.type).toArray
  for s in c.steps do
    match s with
    | .int _ => slots := slots.push .int
    | .nat _ => slots := slots.push .nat
    | .apply op refs =>
      unless refs.mapM (fun r => slots[r]?) == some op.operands do return false
      slots := slots.push op.result
  return slots[c.result]? == some c.resultType.type

private def operations : List ExactOp :=
  let arith : List Arithmetic := [.add,.sub,.mul,.div]
  arith.map .nat ++ arith.map .int ++ [.natIntDiv,.intNatDiv,.neg,.natToInt]

def strip (s left right : String) : Option String := do
  guard (s.startsWith left && s.endsWith right && s.length ≥ left.length + right.length)
  return ((s.drop left.length).dropEnd right.length).toString

def indexOf (s pre : String) : Option Nat := do
  let digits ← strip s pre ""
  guard (digits.length ≤ 4)
  digits.toNat?

def fields (s : String) := if s.isEmpty then [] else s.splitOn ", "

def readGlobal (line : String) (scope : String := "") : Option (Nat × String) := do
  let [lhs,rhs] := line.splitOn " x i8] c\"" | none
  let [name,_] := lhs.splitOn " = private constant [" | none
  return (← indexOf name ("@c" ++ scope), ← strip rhs "" "\\00\"")

def readCall (constants : Std.HashMap Nat String) (i : Nat) (line : String) (scope : String := "") : Option Step := do
  let [dst,rhs] := line.splitOn " = call ptr " | none
  guard (dst == "  " ++ slot i)
  let [name,tail] := rhs.splitOn "(" | none
  let args ← strip tail "" ")"
  if name == symbol "int_decimal" || name == symbol "nat_decimal" then
    -- A literal reads its own global once. Reject a repeated reference before
    -- converting its arbitrary-precision payload.
    guard (args == s!"ptr @c{scope}{i}")
    let value ← constants[i]?
    if name == symbol "int_decimal" then return .int (← value.toInt?)
    else return .nat (← value.toNat?)
  let op ← operations.find? (fun op => symbol op.name == name)
  let operands := fields args
  guard (operands.length == op.operands.length)
  return .apply op (← operands.mapM (indexOf · "ptr %v"))

/-- Reconstruct constants, calls and SSA operands. Canonical reprinting also
checks the declarations, literal lengths, register definitions and RC schedule. -/
private def decode (bytes : List UInt8) : Option Code := do
  guard (bytes.length ≤ 16777216)
  let (header,tail) ← TargetHeader.readPrefix (bytes.take TargetHeader.maxBytes)
  let s ← String.fromUTF8? ⟨(tail ++ bytes.drop TargetHeader.maxBytes).toArray⟩
  let signature :: lines := (← strip s "\n" "").splitOn "\n" | none
  let [kinds,retKind] := (← strip signature "; boxed (" "").splitOn ") -> " | none
  let kinds ← (fields kinds).mapM Kind.read
  let resultType ← Kind.read retKind
  let [decls,body] := (String.intercalate "\n" lines).splitOn "define ptr @vq_exact(" | none
  let [params,block] := body.splitOn ") {\nentry:\n" | none
  let arity := (fields params).length
  guard (arity == kinds.length && arity ≤ 4096)
  let mut constants : Std.HashMap Nat String := {}
  for l in decls.splitOn "\n" do
    if l.startsWith "@c" then
      let (i,v) ← readGlobal l
      constants := constants.insert i v
  let [calls,ret] := block.splitOn "  ret ptr %v" | none
  let result ← indexOf (← strip ret "" "\n}\n") ""
  let mut steps := #[]
  for l in calls.splitOn "\n" do
    if l.startsWith "  %v" then
      guard (arity + steps.size < 4096)
      steps := steps.push (← readCall constants (arity + steps.size) l)
  return ⟨header,kinds,resultType,steps.toList,result⟩

def parse (bytes : List UInt8) : Option Code :=
  match decode bytes with
  | some c => if c.valid = true ∧ bytes = c.print then some c else none
  | none => none

theorem parse_sound {bytes : List UInt8} {c : Code} (h : parse bytes = some c) :
    c.valid = true ∧ bytes = c.print := by
  unfold parse at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  next ok => cases h; exact ok

def translate (header : TargetHeader) (f : MidIR.Function .execution) : Option Code := do
  let params ← f.params.toList.mapM Kind.ofTy
  let output ← Kind.ofTy f.result
  let [block] := f.blocks.toList | none
  guard (block.params == f.params && f.params.size + block.ops.size ≤ 4096)
  let .ret ⟨0⟩ ⟨0,result⟩ := block.term | none
  let steps ← block.ops.toList.mapM fun op => do
    match op.code, op.args with
    | .natural n, [] => pure (Step.nat n)
    | .integer n, [] => pure (.int n)
    | .exactOp arithmetic, refs =>
      guard (refs.all (·.block == 0))
      pure (.apply arithmetic (refs.map (·.slot)))
    | _, _ => none
  let c := Code.mk header params output steps result
  guard c.valid
  return c

end VastitasKernel.LLVM.ExactLibrary
