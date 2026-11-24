import VastitasKernel.LLVM.Emission

set_option autoImplicit false

namespace VastitasOracle.Emission
open VastitasKernel VastitasKernel.LLVM

/-- Both public actions produce the same source-bound output for a successful
build. Parsing a candidate as that model characterizes every byte handed off. -/
theorem executable_readback {wire : Lean.Json} {header : TargetHeader} {o : LLVM.Emission.Output wire header}
    (built : LLVM.Emission.check wire header true = .ok o) (bytes : List UInt8) :
    LLVM.Emission.check wire header false = .ok o ∧
      (o.Decodes bytes ↔ bytes = o.text.toUTF8.data.toList) :=
  ⟨LLVM.Emission.check_of_build built, o.decodes_iff bytes⟩

/-- For a declared entry, checking alone authorizes the same build artifact
and has the same diagnostic if the wire or lowering is rejected. -/
theorem executable_actions {wire : Lean.Json} {p : ResourceSource.Program}
    (decoded : ResourceSource.Wire.program wire = .ok p) (entry : LLVM.Emission.declaresEntry p = true)
    (header : TargetHeader) :
    LLVM.Emission.check wire header false = LLVM.Emission.check wire header true :=
  LLVM.Emission.check_build_entry decoded entry header

end VastitasOracle.Emission
