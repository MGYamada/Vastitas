import VastitasStorageTest.NumericalFixture
import VastitasKernel.StorageMetric

namespace VastitasKernel.Storage.MetricRegression
open NumericalFixture Numerical

private def ensure (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError s!"diagonal metric: {label}")

private def setup : List Functions.Statement := [
  .numerical (.space 0 (id "Real") 2), .numerical (.basis 1 0),
  .numerical (.space 2 (id "Real") 3), .numerical (.basis 3 2),
  .numerical (.involution 4 0), .numerical (.metric 5 1 4 (.diagonal [2,-4])),
  .numerical (.metric 6 3 4 (.diagonal [3,5,-2])),
  .numerical (.conjugateSpace 7 0 4), .numerical (.derivedBasis 8 1 7),
  .action (.allocate 10 .f64 6), .action (.allocate 11 .f64 6),
  .action (.borrow 20 (.owner 10) (layout 3 2) .write), .action (.fill 20 (.f64 0)), .action (.release 20),
  .action (.borrow 21 (.owner 10) (layout 3 2) .read),
  .action (.borrow 22 (.owner 11) (layout 2 3) .write),
  .numerical (.map 30 21 1 3), .numerical (.map 31 22 3 1)]
private def adjoint : Functions.Statement := .numerical (.adjointInto 30 31 5 6 .nativeFast)
private def cleanup : List Functions.Statement := [
  .action (.release 21), .action (.release 22), .action (.drop 10), .action (.drop 11)]

#eval show IO Unit from do
  for entry in [1,-1,2,3,-4,9007199254740992,-9007199254740992] do
    let some bits := diagonalBits entry | throw (IO.userError "representable integer rejected")
    ensure "independent exact integer decoding" (diagonalInteger bits == some entry)
  for entry in [0,9007199254740993,-9007199254740993] do
    ensure "zero/unrepresentable entries rejected" (diagonalBits entry).isNone
  for bits in [0,9223372036854775808,9218868437227405312,9221120237041090560,4609434218613702656] do
    ensure "forged noninteger/nonfinite/zero bits rejected" (diagonalInteger bits).isNone
  let .ok declarations := Indexed.Source.checkDeclarations source | throw (IO.userError "declarations rejected")
  let env := declarations.resolved.declarations.indexed
  let .ok checked := Functions.check (program (setup ++ [adjoint] ++ cleanup)) env
    | throw (IO.userError "materialized adjoint rejected")
  ensure "real actual receipt retained" (checked.context.adjoints.size == 1)
  let .ok native := Native.compile checked.statements | throw (IO.userError "native lowering rejected")
  ensure "standalone adjoint has no GEMM dependency" (!native.needsNumerical)
  ensure "one direct pass, no extra allocation/copy" (native.instructions.countP (fun op => match op with
    | .allocate .. => true | _ => false) == 2 && native.instructions.countP (fun op => match op with
    | .diagonalAdjoint .. => true | _ => false) == 1 && !native.instructions.any (fun op => match op with
    | .copy .. | .gemm .. => true | _ => false))
  let forged := native.instructions.map fun instruction => match instruction with
    | .diagonalAdjoint input inputView output outputView source target flag policy =>
      .diagonalAdjoint input inputView output outputView source target (!flag) policy
    | other => other
  ensure "forged native conjugation rejected" (!(Native.generate {native with instructions := forged}).isOk)
  let forged := native.instructions.map fun instruction => match instruction with
    | .diagonalAdjoint input inputView output outputView _ target flag policy =>
      .diagonalAdjoint input inputView output outputView Diagonal.one target flag policy
    | other => other
  ensure "forged native Gram coefficients rejected" (!(Native.generate {native with instructions := forged}).isOk)
  let .ok branched := Functions.check (program (setup ++ [.branch false [adjoint] [adjoint]] ++ cleanup)) env
    | throw (IO.userError "adjoint branches rejected")
  ensure "both original branch receipts retained" (branched.context.adjoints.size == 2)
  let invalid := .numerical (.adjointInto 30 31 6 5 .nativeFast)
  ensure "unselected wrong metric branch rejected" (!(Functions.check (program (setup ++ [.branch true [adjoint] [invalid]] ++ cleanup)) env).isOk)

  let raw : List Storage.Statement := ([.allocate 0 .f64 1, .allocate 1 .f64 1, .allocate 6 .f64 1,
    .borrow 2 (.owner 0) (layout 1 1) .write, .fill 2 (.f64 0), .release 2,
    .borrow 3 (.owner 0) (layout 1 1) .read, .borrow 4 (.owner 1) (layout 1 1) .write,
    .fill 4 (.f64 0), .captureDependency 5 3 4] : List Action).map .action
  let .ok state := run 4096 {} raw | throw (IO.userError "dependency fixture rejected")
  let pair : DiagonalPair := ⟨3,3,4,6,layout 1 1,7,8,9,Diagonal.one,false,false,.nativeFast⟩
  for operation in [Action.diagonalAdjoint ⟨3,4,Diagonal.one,Diagonal.one,true,.nativeFast⟩,
      .diagonalScale ⟨3,4,Diagonal.one,false,.nativeFast⟩, .diagonalPair pair] do
    let .ok after := checkAction state operation | throw (IO.userError "diagonal write rejected")
    ensure "actual diagonal writes invalidate dependencies" (!(checkAction after (.requireDependency 5)).isOk)
    ensure "caller loans restored" (after.loans == state.loans)
  let .ok after := checkAction state (.diagonalPair pair) | throw (IO.userError "compound pairing rejected")
  ensure "scratch and scalar versions advance exactly once" ((after.owner? 6).map Allocation.version == some 1 &&
    (after.owner? 1).map Allocation.version == some 2)
  ensure "temporary names remain consumed" ([7,8,9].all after.used.contains)
  ensure "scratch no outstanding loans" (!(after.loans.any (·.allocation == 2)))
  ensure "forged internal temporary identity rejected" (!(checkAction state (.diagonalPair {pair with writeLoan := 3})).isOk)
  ensure "malformed coefficient bits rejected before writes" (!(checkAction state (.diagonalAdjoint
    ⟨3,4,⟨true,[0]⟩,Diagonal.one,true,.nativeFast⟩)).isOk)
  ensure "owner scratch cannot be replaced by a borrowed input" (!(checkAction state (.diagonalPair {pair with scratch := 0})).isOk)

end VastitasKernel.Storage.MetricRegression
