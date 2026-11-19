import VastitasOracle.ExitFunction
import VastitasKernel.LLVM.Emission

set_option autoImplicit false

/-! Per-input certificate target for the public executable preview. The
frontend supplies a wire value and a proposed artifact. These are data,
including the exact nominal identities and every byte of the proposed file. -/
namespace VastitasQualification.OfficialExit
open Lean VastitasKernel VastitasKernel.LLVM

/-- Inspect the returned source decoder's real function declarations. This
auxiliary stage checks only the literal spelling and its nominal owner. -/
def decodedLiteral (wire : Json) : Option (Namespace.Owner × Int) := do
  let p ← (ResourceSource.Wire.program wire).toOption
  let [(owner, f)] := p.packages.flatMap (fun pkg => pkg.modules.flatMap fun m =>
    m.pureModule.functions.map fun f => (Namespace.Owner.mk ⟨pkg.id, m.pureModule.module.path⟩ f.name, f))
    | none
  guard (owner.scope.package.source == p.root && owner.scope.path.isEmpty && owner.name == "main" &&
    f.params.isEmpty && f.finiteBinders.isEmpty)
  let .data (.pure .int) := f.result | none
  let .mk [] expr _ := f.body | none
  let (negate, digits, span) ← match expr with
    | .integer digits span => some (false, digits, span)
    | .unary "-" (.integer digits span) _ => some (true, digits, span)
    | _ => none
  let (.integer v, _) ← ((Indexed.Source.Bodies.integerLiteral digits span (some (.pure .int))).run {}).toOption
    | none
  return (owner, if negate then -v else v)

structure Current (wire : Json) (target : TargetHeader) (bytes : List UInt8) where
  mode : Bool
  request : ResourceSource.Wire.CheckedInput wire mode
  linked : ExitFunction.Artifact request target
  text : String
  parsed : ExitMain.parse text.toUTF8.data.toList = some linked.toModule
  returned : Emission.check wire target true = .ok (.executable linked text parsed)
  complete : text.toUTF8.data.toList = bytes

def witness (wire : Json) (target : TargetHeader) (bytes : List UInt8) :
    Option (Current wire target bytes) :=
  match returned : Emission.check wire target true with
  | .ok (.executable (main := mode) (req := request) linked text parsed) =>
    if same : text.toUTF8.data.toList = bytes then
      some ⟨mode, request, linked, text, parsed, returned, same⟩
    else none
  | _ => none

/-- This statement names the exact successful public operation as well as its
returned Core, both module observations, artifact revision and saved bytes. -/
def Observes (wire : Json) (target : TargetHeader) (bytes : List UInt8) (v : Int) : Prop :=
  ∃ c : Current wire target bytes,
    c.linked.literal.value = v ∧
    c.linked.exe.revision = ResourceSource.FunctionRevision.artifact
      (ResourceSource.Wire.revisionInput wire) c.request.checked ∧
    bytes = ExitMain.print c.linked.toModule ∧
    (∀ fuel, VastitasOracle.ExitFunction.coreEntry (ExitFunction.core c.request) (fuel + 3) =
      some (.integer v)) ∧
    VastitasOracle.ExitFunction.midEntry c.linked.opt = some (.integer v) ∧
    VastitasOracle.ExitFunction.midEntry c.linked.exe = some (.integer v) ∧
    (ExitMain.evaluate c.linked.toModule).toNat = (v % 256).toNat

def validate (wire : Json) (target : TargetHeader) (bytes : List UInt8) (v : Int) : Bool :=
  (witness wire target bytes).any fun c => c.linked.literal.value == v

theorem of_validate {wire : Json} {target : TargetHeader} {bytes : List UInt8} {v : Int}
    (h : validate wire target bytes v = true) : Observes wire target bytes v := by
  cases found : witness wire target bytes with
  | none => simp [validate,found] at h
  | some c =>
    have value : c.linked.literal.value = v := by simpa [validate,found] using h
    subst v
    have parsed := c.complete ▸ c.parsed
    have all := VastitasOracle.ExitFunction.correspondence c.linked bytes parsed
    obtain ⟨printed, _, opt, exe, status, _⟩ := all 0
    exact ⟨c, rfl, c.linked.revision, printed, fun fuel => (all fuel).2.1, opt, exe, status⟩

end VastitasQualification.OfficialExit
