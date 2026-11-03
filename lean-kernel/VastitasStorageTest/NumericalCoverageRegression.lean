import VastitasKernel.NumericalCoverage
import VastitasStorageTest.NumericalFixture

namespace VastitasKernel.Storage.NumericalCoverageRegression
open NumericalFixture

private def check (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError s!"numerical occurrence coverage failed: {label}")

private def network : Functions.Statement :=
  .network ⟨[⟨"a", 30⟩, ⟨"b", 31⟩], [⟨⟨"a", .input⟩, ⟨"b", .output⟩⟩],
    [⟨"b", .input⟩], [⟨"a", .output⟩]⟩ 32 .nativeFast

#eval show IO Unit from do
  let .ok declarations := Indexed.Source.checkDeclarations source | throw (IO.userError "declarations")
  let branch := Functions.Statement.branch true [multiply, .branch false [multiply] [network]] [multiply]
  let callee : Functions.Function := ⟨1, [], [], setup .f64 "Real" ++ [branch] ++ cleanup, none⟩
  let p : Functions.Program := ⟨[⟨0, [], [], [.call 1 [] [], .call 1 [] []], none⟩, callee], 0⟩
  let .ok result := Functions.check p declarations.resolved.declarations.indexed
    | throw (IO.userError "actual repeated call/branch expansion failed")
  let c := result.context
  let accepts := NumericalCoverage.audit p.functions p.entry
  check "both calls, nested arms and both network products" (accepts c && c.products.size == 8 && c.networks.size == 2)
  check "physical addresses determine order" (accepts {c with products := c.products.reverse, networks := c.networks.reverse})
  let some first := c.products[0]? | throw (IO.userError "first arm")
  let some other := c.products[3]? | throw (IO.userError "other arm")
  let some later := c.products[4]? | throw (IO.userError "second call")
  check "identical action in the other arm" (first.checked.product.request first.mode first.policy ==
    other.checked.product.request other.mode other.policy && first.location.start == other.location.start &&
    first.location.block != other.location.block)
  check "distinct call sites for one callee statement" (first.location.source == later.location.source &&
    first.location.callers != later.location.callers)
  check "missing product" (!accepts {c with products := c.products.pop})
  check "duplicate product" (!accepts {c with products := c.products.push first})
  check "one occurrence cannot replace another" (!accepts {c with products := c.products.set! 3 first})
  let wrongArm := {first with location := {first.location with block := other.location.block}}
  check "wrong arm at the same offset" (!accepts {c with products := c.products.set! 0 wrongArm})
  let wrongCaller := {first with location := {first.location with callers := later.location.callers}}
  check "wrong caller of the same source function" (!accepts {c with products := c.products.set! 0 wrongCaller})
  check "network cannot lose the graph receipt" (!accepts {c with networks := #[]})
  check "network cannot lose its shared product receipt"
    (!accepts {c with products := c.products.filter fun r => !r.networkProduct})
  check "unrelated or absent source entry" (!NumericalCoverage.audit p.functions 1 c &&
    !NumericalCoverage.audit p.functions 2 c)
  check "actual code required" (!accepts {c with code := #[]})
  check "erasing both schedule and receipts still disagrees with the source calls"
    (!accepts {c with code := #[], products := #[], networks := #[]})

end VastitasKernel.Storage.NumericalCoverageRegression
