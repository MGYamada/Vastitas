import VastitasStorageTest.NumericalFixture

namespace VastitasKernel.Storage.DependencyRegression
open NumericalFixture Numerical

private def ensure (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError s!"storage dependency: {label}")

private def rawSetup : List Storage.Statement := ([
  .allocate 0 .f64 1, .allocate 1 .f64 1,
  .borrow 2 (.owner 0) (layout 1 1) .write, .fill 2 (.f64 0), .release 2,
  .borrow 3 (.owner 0) (layout 1 1) .read,
  .borrow 4 (.owner 1) (layout 1 1) .write, .fill 4 (.f64 0),
  .captureDependency 5 3 4] : List Action).map .action

private def setup : List Functions.Statement := [
  .numerical (.space 0 (id "Real") 1), .numerical (.basis 1 0),
  .numerical (.dualSpace 2 0), .numerical (.derivedBasis 3 1 2),
  .action (.allocate 10 .f64 1), .action (.allocate 11 .f64 1), .action (.allocate 12 .f64 1),
  .action (.borrow 20 (.owner 10) (layout 1 1) .write), .action (.fill 20 (.f64 0)), .action (.release 20),
  .action (.borrow 21 (.owner 10) (layout 1 1) .read),
  .action (.borrow 22 (.owner 11) (layout 1 1) .write),
  .action (.borrow 23 (.owner 12) (layout 1 1) .write),
  .tensor (.view 30 21 [1, 3, 1] Tensor.unpacked),
  .tensor (.view 31 22 [1, 3, 1] Tensor.packed),
  .tensor (.view 32 21 [1, 3] Tensor.matrix),
  .tensor (.view 33 23 [1, 1, 3] Tensor.boundary)]
private def capture : Functions.Statement := .tensor (.cachedPack 40 30 31)
private def readPacked : List Functions.Statement := [
  .action (.release 22), .action (.borrow 24 (.owner 11) (layout 1 1) .read),
  .tensor (.view 34 24 [1, 3, 1] Tensor.packed)]
private def useCache : Functions.Statement := .tensor (.cachedContract3 40 34 32 33 .nativeFast)
private def cleanup : List Functions.Statement := [
  .action (.release 24), .action (.release 23), .action (.release 21),
  .action (.drop 10), .action (.drop 11), .action (.drop 12)]

#eval show IO Unit from do
  let .ok state := run 4096 {} rawSetup | throw (IO.userError "raw capture rejected")
  ensure "capture usable without a read destination loan" ((checkAction state (.requireDependency 5)).isOk)
  let some ⟨_, some dep⟩ := state.dependency? 5 | throw (IO.userError "capture missing")
  ensure "both actual current epochs captured" (dep.source.version == 1 && dep.target.version == 1)
  for action in [Action.fill 4 (.f64 0), .store 4 0 0 (.f64 0), .copy 3 4,
      .pack3 3 4 1 1 1, .gemm ⟨3, 3, 4, false, false, .overwrite, .nativeFast, none, none⟩] do
    let .ok written := checkAction state action | throw (IO.userError "write fixture rejected")
    ensure "every actual write invalidates the dependency" (!(checkAction written (.requireDependency 5)).isOk)
    ensure "invalidation does not lose lexical cleanup" ((checkAction written (.forgetDependency 5)).isOk)
  let .ok released := checkAction state (.release 3) | throw (IO.userError "release rejected")
  let .ok moved := checkAction released (.move 0 8) | throw (IO.userError "move rejected")
  ensure "move preserves captured allocation/version" ((checkAction moved (.requireDependency 5)).isOk)
  let .ok dropped := checkAction moved (.drop 8) | throw (IO.userError "drop rejected")
  ensure "drop invalidates rather than retains allocation" (!(checkAction dropped (.requireDependency 5)).isOk)
  let .ok joined := join state state | throw (IO.userError "join rejected")
  ensure "even no-write join conservatively invalidates" (!(checkAction joined (.requireDependency 5)).isOk)
  ensure "forged current epoch fails independent audit" (!auditState {state with
    dependencies := [⟨5, some {dep with source := {dep.source with version := 99}}⟩]})
  let shared : List Storage.Statement := ([.allocate 0 .f64 2,
    .borrow 1 (.owner 0) ⟨0, 1, 1, 1, false⟩ .write, .fill 1 (.f64 0), .release 1,
    .borrow 2 (.owner 0) ⟨0, 1, 1, 1, false⟩ .read,
    .borrow 3 (.owner 0) ⟨8, 1, 1, 1, false⟩ .write,
    .pack3 2 3 1 1 1, .captureDependency 4 2 3, .requireDependency 4] : List Action).map .action
  let .ok shared := run 4096 {} shared | throw (IO.userError "same allocation post-pack capture rejected")
  let some ⟨_, some sharedDep⟩ := shared.dependency? 4 | throw (IO.userError "shared capture missing")
  ensure "same-allocation disjoint packing captures both post-write epochs" (sharedDep.source.version == 2 && sharedDep.target.version == 2)
  let .ok declarations := Indexed.Source.checkDeclarations source | throw (IO.userError "declarations rejected")
  let env := declarations.resolved.declarations.indexed
  let body := setup ++ [capture] ++ readPacked ++ [useCache, useCache] ++ cleanup
  let .ok result := Functions.check (program body) env | throw (IO.userError "cached contraction rejected")
  ensure "actual receipts exclude probes and keep both consumers" (result.context.cacheCaptures.size == 1 && result.context.cachedContractions.size == 2)
  ensure "lexical dependency cleanup closes the actual plan" result.resources.finalState.dependencies.isEmpty
  let .ok native := Native.compile result.statements | throw (IO.userError "native compile rejected")
  ensure "one pack and two products with no bookkeeping instructions" (native.instructions.countP (fun i => match i with | .pack3 .. => true | _ => false) == 1 &&
    native.instructions.countP (fun i => match i with | .gemm .. => true | _ => false) == 2)
  let changed := result.statements.filter fun statement => match statement with
    | .action (.captureDependency ..) => false | _ => true
  ensure "forged native plan cannot discard capture" (!(Native.generate {native with input := changed}).isOk)
  let raw := setup ++ [.action (.fill 22 (.f64 0)), .action (.captureDependency 40 21 22)] ++ readPacked ++ [useCache] ++ cleanup
  ensure "raw capture grants no packing certificate" (!(Functions.check (program raw) env).isOk)
  for condition in [false, true] do
    let .ok branched := Functions.check (program [.branch condition body body]) env
      | throw (IO.userError "branch-local caches rejected")
    ensure "both branch cache receipts retained" (branched.context.cacheCaptures.size == 2 && branched.context.cachedContractions.size == 4)
  IO.println "storage dependency: actual write invalidation, post-pack stamps, affine lifetime, lexical cleanup, replay, native erasure and nominal cache provenance passed"

end VastitasKernel.Storage.DependencyRegression
