import VastitasKernel.LLVM.ExactProgram
import VastitasKernel.LLVM.ExactFlowProgram
import VastitasKernel.LLVM.StorageProgram
import VastitasKernel.LLVM.ExactFunction
import VastitasKernel.LLVM.CallFunction
import VastitasKernel.LLVM.BinaryFunction
import VastitasKernel.LLVM.DispatchFunction
import VastitasKernel.LLVM.FiniteProgram

set_option autoImplicit false

/-! The protocol checker selects a complete module from the actual checked
Core. Every result retains its source-bound specialization and the equality
for the canonical parser on the exact UTF-8 bytes returned to the driver. -/
namespace VastitasKernel.LLVM.Emission
open Lean ResourceSource

inductive Output (json : Json) (header : TargetHeader) where
  | storage {main : Bool} {req : Wire.CheckedInput json main}
      (a : StorageProgram.Artifact req header) (text : String)
      (parsed : StorageModule.parse text.toUTF8.data.toList = some a.model)
  | exactProgram {main : Bool} {req : Wire.CheckedInput json main}
      (a : ExactProgram.Artifact req header) (text : String)
      (parsed : ExactProgram.parse text.toUTF8.data.toList = some a.model)
  | exactFlow {main : Bool} {req : Wire.CheckedInput json main}
      (a : ExactFlow.Artifact req header) (text : String)
      (parsed : ExactFlow.parse text.toUTF8.data.toList = some a.model)
  | exactLibrary {req : Wire.CheckedInput json false}
      (a : ExactFunction.Artifact req header) (text : String)
      (parsed : ExactLibrary.parse text.toUTF8.data.toList = some a.model)
  | lookup {req : Wire.CheckedInput json false} {owner}
      (a : UnaryFunction.Artifact req owner header) (text : String)
      (parsed : TableSwitch.parse text.toUTF8.data.toList = some a.image.toModule)
  | binary {req : Wire.CheckedInput json false} {owner}
      (a : BinaryFunction.Artifact req owner header) (text : String)
      (parsed : BinaryTable.parse text.toUTF8.data.toList = some a.image.code)
  | forwarding {req : Wire.CheckedInput json false} {leaf caller}
      (a : CallFunction.Artifact req leaf caller header) (text : String)
      (parsed : ForwardCall.parse text.toUTF8.data.toList = some ⟨a.image.toModule⟩)
  | executable {main : Bool} {req : Wire.CheckedInput json main}
      (a : ExitFunction.Artifact req header) (text : String)
      (parsed : ExitMain.parse text.toUTF8.data.toList = some a.toModule)
  | folded {main : Bool} {req : Wire.CheckedInput json main}
      (a : ExitFunction.FoldArtifact req header) (text : String)
      (parsed : ExitMain.parse text.toUTF8.data.toList = some a.toModule)
  | dispatch {main : Bool} {req : Wire.CheckedInput json main}
      (a : DispatchFunction.Artifact req) (text : String)
      (parsed : DispatchBool.parse text.toUTF8.data.toList = some (a.toModule header))
  | finite {main : Bool} {req : Wire.CheckedInput json main}
      (a : FiniteProgram.Artifact req header) (text : String)
      (parsed : FiniteModule.parse text.toUTF8.data.toList = some a.model)

def Output.text {json header} : Output json header → String
  | .exactFlow _ s _ | .storage _ s _ | .exactProgram _ s _ | .exactLibrary _ s _ | .lookup _ s _ | .binary _ s _ | .forwarding _ s _ | .executable _ s _ | .folded _ s _ | .dispatch _ s _ | .finite _ s _ => s

/-- Revision carried by the same artifact whose canonical text is published. -/
def Output.revision {json header} : Output json header → Json
  | .storage a .. => a.revision
  | .exactProgram a .. => a.linked.exe.revision
  | .exactFlow a .. => a.linked.exe.revision
  | .finite a .. => a.linked.exe.revision
  | .exactLibrary a .. => a.exe.revision
  | .lookup a .. => a.exe.revision
  | .binary a .. => a.exe.revision
  | .forwarding a .. => a.exe.revision
  | .executable a .. => a.exe.revision
  | .folded a .. => a.exe.revision
  | .dispatch a .. => a.exe.revision

def Output.kind {json header} : Output json header → String
  | .storage a .. => if a.model.calls.any (fun c => c.target == .gemm || c.target == .diagonalPair) then "storage-gemm-program" else "storage-program"
  | .exactFlow .. => "boxed-control-flow"
  | .exactProgram .. => "boxed-exact-program"
  | .exactLibrary .. => "boxed-exact-library"
  | .lookup .. => "unary-lookup"
  | .binary .. => "binary-lookup"
  | .forwarding .. => "static-call"
  | .executable .. | .folded .. => "entry-status"
  | .dispatch .. => "assembled-bool"
  | .finite .. => "finite-program"

/-- Reparse a candidate buffer as the specific model in the public output. -/
def Output.Decodes {json header} (o : Output json header) (bytes : List UInt8) : Prop :=
  match o with
  | .storage a .. => StorageModule.parse bytes = some a.model
  | .exactProgram a .. => ExactProgram.parse bytes = some a.model
  | .exactFlow a .. => ExactFlow.parse bytes = some a.model
  | .exactLibrary a .. => ExactLibrary.parse bytes = some a.model
  | .lookup a .. => TableSwitch.parse bytes = some a.image.toModule
  | .binary a .. => BinaryTable.parse bytes = some a.image.code
  | .forwarding a .. => ForwardCall.parse bytes = some ⟨a.image.toModule⟩
  | .executable a .. => ExitMain.parse bytes = some a.toModule
  | .folded a .. => ExitMain.parse bytes = some a.toModule
  | .dispatch a .. => DispatchBool.parse bytes = some (a.toModule header)
  | .finite a .. => FiniteModule.parse bytes = some a.model

private theorem sameReadback {α : Type} {parse : List UInt8 → Option α} {m : α}
    {printed published candidate : List UInt8}
    (canonical : ∀ b, parse b = some m → b = printed) (accepted : parse published = some m) :
    parse candidate = some m ↔ candidate = published := by
  constructor
  · exact fun h => (canonical _ h).trans (canonical _ accepted).symm
  · rintro rfl
    exact accepted

/-- Equality with the exact UTF-8 payload handed to the driver is necessary and
sufficient for the candidate to decode to the published model, for every emitter. -/
theorem Output.decodes_iff {json header} (o : Output json header) (bytes : List UInt8) :
    o.Decodes bytes ↔ bytes = o.text.toUTF8.data.toList := by
  match o with
  | .storage _ _ h => exact sameReadback (fun _ p => StorageModule.parse_sound p) h
  | .exactProgram _ _ h => exact sameReadback (fun _ p => (ExactProgram.parse_sound p).2) h
  | .exactFlow _ _ h => exact sameReadback (fun _ p => (ExactFlow.parse_sound p).2) h
  | .exactLibrary _ _ h => exact sameReadback (fun _ p => (ExactLibrary.parse_sound p).2) h
  | .lookup _ _ h => exact sameReadback (fun b => (TableSwitch.parse_iff b _).mp) h
  | .binary _ _ h => exact sameReadback (fun b => (BinaryTable.parse_iff b _).mp) h
  | .forwarding _ _ h => exact sameReadback (fun b => (ForwardCall.parse_iff b _).mp) h
  | .executable _ _ h => exact sameReadback (fun b => (ExitMain.parse_iff b _).mp) h
  | .folded _ _ h => exact sameReadback (fun b => (ExitMain.parse_iff b _).mp) h
  | .dispatch _ _ h => exact sameReadback (fun b => (DispatchBool.parse_iff b _).mp) h
  | .finite _ _ h => exact sameReadback (fun b => (FiniteModule.parse_iff b _).mp) h

private def checkedText {α : Type} [DecidableEq α] (m : α) (print : α → List UInt8)
    (parse : List UInt8 → Option α) : Option { s : String // parse s.toUTF8.data.toList = some m } := do
  let s ← String.fromUTF8? ⟨(print m).toArray⟩
  if h : parse s.toUTF8.data.toList = some m then return ⟨s,h⟩ else none

private def scalarApp {json main} (req : Wire.CheckedInput json main) (header : TargetHeader) :
    Option (Output json header) := do
  unless req.checked.pureProgram.dispatcher.families.isEmpty do
    let a ← DispatchFunction.compile req
    let ⟨s, parsed⟩ ← checkedText (a.toModule header) DispatchBool.print DispatchBool.parse
    return .dispatch a s parsed
  let [entry] := (ExitFunction.core req).functions | none
  if (ExitFunction.literalBody entry.body).isSome then
    let a ← ExitFunction.compile req header
    let ⟨s, parsed⟩ ← checkedText a.toModule ExitMain.print ExitMain.parse
    return .executable a s parsed
  let a ← ExitFunction.compileFold req header
  let ⟨s, parsed⟩ ← checkedText a.toModule ExitMain.print ExitMain.parse
  return .folded a s parsed

private def app {json main} (req : Wire.CheckedInput json main) (header : TargetHeader) :
    Option (Output json header) :=
  if req.input.entry.isSome then do
    let a ← StorageProgram.compile req header
    let s ← a.model.render
    if parsed : StorageModule.parse s.toUTF8.data.toList = some a.model then
      return .storage a s parsed
    else none
  else scalarApp req header <|> (do
    let a ← FiniteProgram.compile req header
    let ⟨s, parsed⟩ ← checkedText a.model FiniteModule.print FiniteModule.parse
    return .finite a s parsed) <|> (do
    let a ← ExactProgram.compile req header
    let ⟨s, parsed⟩ ← checkedText a.model ExactProgram.Code.print ExactProgram.parse
    return .exactProgram a s parsed) <|> do
    let a ← ExactFlow.compile req header
    let ⟨s, parsed⟩ ← checkedText a.model ExactFlow.Code.print ExactFlow.parse
    return .exactFlow a s parsed

private def library {json} (req : Wire.CheckedInput json false) (header : TargetHeader) :
    Option (Output json header) := do
  match (UnaryFunction.checkedCore req).functions with
  | [f] =>
    if f.returnType matches .pure .int | .pure .nat | .pure .bool | .pure (.pair _) then
      let a ← ExactFunction.compile req header
      let ⟨s,parsed⟩ ← checkedText a.model ExactLibrary.Code.print ExactLibrary.parse
      return .exactLibrary a s parsed
    if f.parameters.length == 2 then
      let a ← BinaryFunction.compile req ⟨f.definition⟩ header
      let ⟨s, parsed⟩ ← checkedText a.image.code BinaryTable.print BinaryTable.parse
      return .binary a s parsed
    let a ← UnaryFunction.compile req ⟨f.definition⟩ header
    let ⟨s, parsed⟩ ← checkedText a.image.toModule TableSwitch.print TableSwitch.parse
    return .lookup a s parsed
  | [leaf, caller] =>
    let a ← CallFunction.compile req ⟨leaf.definition⟩ ⟨caller.definition⟩ header
    let ⟨s, parsed⟩ ← checkedText ⟨a.image.toModule⟩ ForwardCall.print ForwardCall.parse
    return .forwarding a s parsed
  | _ => none

private def supported {α : Type} (o : Option α) : Except Diagnostic α :=
  o.elim (.error {code := "E_UNSUPPORTED", message :=
    "checked module is outside the LLVM preview (closed exact integer main, assembled Bool branch, closed finite program, static storage program, boxed integer program or library, unary or binary table lookup, or static forwarder)"}) .ok

/-- Look only in the root module of the root package. A dependency or a
nested module may publish a function named main without making the root an executable. -/
def declaresEntry (p : ResourceSource.Program) : Bool :=
  p.packages.any fun pkg => pkg.id.source == p.root && pkg.modules.any fun m =>
    m.pureModule.module.path.isEmpty && (m.pureModule.functions.any (·.name == "main") ||
      m.functions.any (·.name == "main"))

private def checkInput {json : Json} {p : ResourceSource.Program} (decoded : Wire.program json = .ok p)
    (header : TargetHeader) (requireExecutable : Bool) : Except Diagnostic (Output json header) := do
  if declaresEntry p then
    let req ← Wire.checkDecoded decoded true
    return ← supported (app req header)
  let req ← Wire.checkDecoded decoded false
  if requireExecutable then throw {code := "E_MAIN", message := "entry point must have signature fn main() -> Int"}
  supported (library req header)

def check (json : Json) (header : TargetHeader) (requireExecutable : Bool) : Except Diagnostic (Output json header) :=
  match decoded : Wire.program json with
  | .error message => .error {code := "E_PROTOCOL", message}
  | .ok _ => checkInput decoded header requireExecutable

private theorem check_of_decoded {json : Json} {p : ResourceSource.Program} (decoded : Wire.program json = .ok p)
    (header : TargetHeader) (requireExecutable : Bool) :
    check json header requireExecutable = checkInput decoded header requireExecutable := by
  unfold check
  split
  · rename_i _ h
    simp [decoded] at h
  · rename_i _ h
    cases Except.ok.inj (h.symm.trans decoded)
    rfl

/-- Both commands apply the executable entry rule before considering any LLVM
profile. This covers diagnostics as well as a successful source-bound output. -/
theorem check_build_entry {json : Json} {p : ResourceSource.Program} (decoded : Wire.program json = .ok p)
    (entry : declaresEntry p = true) (header : TargetHeader) :
    check json header false = check json header true := by
  rw [check_of_decoded decoded, check_of_decoded decoded]
  simp [checkInput, entry]

/-- A successful executable build can be replayed by the public check action. -/
theorem check_of_build {json : Json} {header : TargetHeader} {o : Output json header}
    (built : check json header true = .ok o) : check json header false = .ok o := by
  unfold check at built
  split at built
  · contradiction
  · rename_i input decoded
    cases entry : declaresEntry input with
    | true => exact (check_build_entry decoded entry header).trans (by rwa [check_of_decoded decoded])
    | false =>
      simp [checkInput, entry, bind, Except.bind] at built
      split at built <;> contradiction

/-- A checked singleton literal uses the executable branch and returns exactly
the UTF-8 string accepted by its parser. This proof applies to the current wire
result without reducing a concrete program's manifest, Core or revision. -/
theorem check_literal {json : Json} {header : TargetHeader} {req : Wire.CheckedInput json true} {requireExecutable : Bool}
    (accepted : Wire.check json true = .ok req) (declared : declaresEntry req.input = true)
    (a : ExitFunction.Artifact req header) (compiled : ExitFunction.compile req header = some a)
    (pureEntry : req.input.entry.isSome = false)
    (noFamilies : req.checked.pureProgram.dispatcher.families.isEmpty = true)
    (literal : (ExitFunction.literalBody a.source.body).isSome = true)
    (text : String) (parsed : ExitMain.parse text.toUTF8.data.toList = some a.toModule) :
    check json header requireExecutable = .ok (.executable a text parsed) := by
  have rendered : String.fromUTF8? ⟨(ExitMain.print a.toModule).toArray⟩ = some text := by
    rw [← (ExitMain.parse_iff _ _).mp parsed]
    change String.fromUTF8? text.toByteArray = some text
    simp [String.fromUTF8?, text.isValidUTF8]
    rfl
  have parseBytes : ExitMain.parse text.toByteArray.data.toList = some a.toModule := parsed
  rw [Wire.check_of_decoded req.decoded] at accepted
  rw [check_of_decoded req.decoded]
  simp [checkInput, declared, accepted, app, pureEntry, scalarApp, noFamilies, a.onlyCore, literal,
    compiled, checkedText, rendered, parseBytes, supported, bind, Except.bind, Option.bind]

end VastitasKernel.LLVM.Emission
