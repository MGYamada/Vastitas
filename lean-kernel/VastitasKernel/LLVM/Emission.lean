import VastitasKernel.LLVM.ExactProgram
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
  | .storage _ s _ | .exactProgram _ s _ | .exactLibrary _ s _ | .lookup _ s _ | .binary _ s _ | .forwarding _ s _ | .executable _ s _ | .folded _ s _ | .dispatch _ s _ | .finite _ s _ => s

def Output.kind {json header} : Output json header → String
  | .storage .. => "storage-program"
  | .exactProgram .. => "boxed-exact-program"
  | .exactLibrary .. => "boxed-exact-library"
  | .lookup .. => "unary-lookup"
  | .binary .. => "binary-lookup"
  | .forwarding .. => "static-call"
  | .executable .. | .folded .. => "entry-status"
  | .dispatch .. => "assembled-bool"
  | .finite .. => "finite-program"

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
    let ⟨s, parsed⟩ ← checkedText a.model StorageModule.Code.print StorageModule.parse
    return .storage a s parsed
  else scalarApp req header <|> (do
    let a ← FiniteProgram.compile req header
    let ⟨s, parsed⟩ ← checkedText a.model FiniteModule.print FiniteModule.parse
    return .finite a s parsed) <|> do
    let a ← ExactProgram.compile req header
    let ⟨s, parsed⟩ ← checkedText a.model ExactProgram.Code.print ExactProgram.parse
    return .exactProgram a s parsed

private def library {json} (req : Wire.CheckedInput json false) (header : TargetHeader) :
    Option (Output json header) := do
  match (UnaryFunction.checkedCore req).functions with
  | [f] =>
    if f.returnType == .pure .int || f.returnType == .pure .nat then
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

def check (json : Json) (header : TargetHeader) (requireExecutable : Bool) : Except Diagnostic (Output json header) := do
  if requireExecutable then return ← supported (app (← Wire.check json true) header)
  let req ← Wire.check json false
  if req.input.entry.isSome || (UnaryFunction.checkedCore req).main.isSome then return ← supported (app req header)
  supported (library req header)

end VastitasKernel.LLVM.Emission
