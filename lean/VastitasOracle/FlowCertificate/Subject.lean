import VastitasOracle.CertificatePackages
import VastitasKernel.LLVM.ExactFlowExecution
import VastitasKernel.LLVM.ExactFlowPrint
import VastitasKernel.PhysicalSources

set_option autoImplicit false

/-! The concrete proof subject for the boxed execution-to-bytes stage. Its
wire, revision, target, complete module and mathematical value are explicit
data. The compiled checker supplies the linked source artifact separately. -/
namespace VastitasOracle.FlowCertificate
open VastitasKernel VastitasKernel.LLVM

structure Subject where
  wire : Lean.Json
  revision : Lean.Json
  sources : PhysicalSources.Layout
  packages : CertificatePackages.Graph
  header : TargetHeader
  code : ExactFlow.Code
  bytes : List UInt8
  value : Int

/-- A stage certificate never turns an unchecked wire into an accepted program. -/
structure Valid (s : Subject) : Prop where
  input : s.revision.getObjVal? "input" = .ok s.wire
  physical : PhysicalSources.layout s.wire = .ok s.sources
  owners : CertificatePackages.read s.wire = .ok s.packages
  target : s.code.header = s.header
  typed : s.code.valid = true
  evaluated : s.code.entryValue = some s.value
  printed : s.code.print = s.bytes

/-- Check the two printed header lines and the remaining text separately,
then recover equality of every octet, including both terminal newlines. -/
theorem printedLines (c : LLVM.ExactFlow.Code) (header : List UInt8) (lines : List String)
    (h : c.header.print = header) (l : c.bodyLines = lines) :
    c.print = header ++ ("\n" ++ String.intercalate "\n" lines ++ "\n").toUTF8.data.toList := by
  unfold LLVM.ExactFlow.Code.print
  rw [h, l]

end VastitasOracle.FlowCertificate
