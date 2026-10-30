import VastitasKernel.StorageProtocol

namespace VastitasKernel.Storage.Regression

private def check (name : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError s!"storage regression failed: {name}")
private def actions (items : List Action) : List Statement := items.map .action
private def accepts (items : List Action) : Bool := (checkPlan (actions items)).isOk
private def rejects (code : String) (items : List Action) : Bool :=
  match checkPlan (actions items) with | .ok _ => false | .error error => error.code == code
private def full : Layout := ⟨0, 2, 2, 2, false⟩
private def padded : Layout := ⟨0, 2, 2, 4, false⟩
private def first : Layout := ⟨0, 1, 1, 1, false⟩
private def second : Layout := ⟨8, 1, 1, 1, false⟩
private def value : Literal := .f64 0x4008000000000000
private def allocate : Action := .allocate 0 .f64 8
private def write (name : Nat) (layout : Layout := full) : Action := .borrow name (.owner 0) layout .write
private def read (name : Nat) (layout : Layout := full) : Action := .borrow name (.owner 0) layout .read

/-- This exact plan is intended for the native integration, not a separate
runtime model. The expected bit pattern remains an executable operation. -/
def paddedFixture : List Statement := actions [allocate, write 1 padded, .fill 1 value,
  .transpose 1, .release 1, read 2 padded.transpose, .expect 2 1 1 value,
  .release 2, .move 0 3, .drop 3]

#eval check "empty plan" (checkPlan []).isOk
#eval check "padded fill, transpose, read and move" (checkPlan paddedFixture).isOk
#eval check "uninitialized read" (rejects "E_RESOURCE_INIT" [allocate, read 1])
#eval check "write-only does not read" (rejects "E_RESOURCE_ACCESS" [allocate, write 1, .fill 1 value, .expect 1 0 0 value])
#eval check "partial write does not initialize full view" (rejects "E_RESOURCE_INIT"
  [allocate, write 1, .store 1 0 0 value, .release 1, read 2])
#eval check "partial write initializes its actual cell" (accepts
  [allocate, write 1, .store 1 0 0 value, .release 1, read 2 first, .expect 2 0 0 value, .release 2, .drop 0])
#eval check "padding is not initialized" (rejects "E_RESOURCE_INIT"
  [allocate, write 1 padded, .fill 1 value, .release 1, read 2 ⟨16, 1, 1, 1, false⟩])
#eval check "read/read sharing" (accepts [allocate, write 1, .fill 1 value, .release 1,
  read 2, read 3, .expect 2 0 0 value, .expect 3 1 1 value, .release 2, .release 3, .drop 0])
#eval check "overlapping writes" (rejects "E_RESOURCE_ALIAS" [allocate, write 1, write 2])
#eval check "disjoint element writes" (accepts [allocate, write 1 first, write 2 second,
  .fill 1 value, .fill 2 value, .release 2, .release 1, .drop 0])
#eval check "transpose does not remove alias" (rejects "E_RESOURCE_ALIAS"
  [allocate, write 1, .transpose 1, write 2])
#eval check "live read conflicts with write" (rejects "E_RESOURCE_ALIAS"
  [allocate, write 1, .fill 1 value, .release 1, read 2, write 3])
#eval check "move revokes old owner" (rejects "E_RESOURCE_MOVE" [allocate, .move 0 1, .drop 0])
#eval check "live loan blocks move" (rejects "E_RESOURCE_LOAN" [allocate, write 1, .move 0 2])
#eval check "live loan blocks drop" (rejects "E_RESOURCE_LOAN" [allocate, write 1, .drop 0])
#eval check "drop revokes owner" (rejects "E_RESOURCE_MOVE" [allocate, .drop 0, .drop 0])
#eval check "released loan is unusable" (rejects "E_RESOURCE_LOAN" [allocate, write 1, .release 1, .fill 1 value])
#eval check "symbols cannot be reissued" (rejects "E_RESOURCE_NAME" [allocate, .move 0 1, .allocate 0 .f64 1])
#eval check "live owner cannot escape plan" (rejects "E_RESOURCE_ESCAPE" [allocate])
#eval check "exclusive child suspends parent" (rejects "E_RESOURCE_LOAN"
  [allocate, write 1, .borrow 2 (.loan 1) first .write, .fill 1 value])
#eval check "shared child also suspends parent" (rejects "E_RESOURCE_LOAN"
  [allocate, write 1, .fill 1 value, .release 1, .borrow 2 (.owner 0) full .readWrite,
    .borrow 3 (.loan 2) first .read, .fill 2 value])
#eval check "write-only parent cannot acquire read access through a child" (rejects "E_RESOURCE_ACCESS"
  [allocate, write 1, .fill 1 value, .borrow 2 (.loan 1) first .read])
#eval check "nested loans return inside out" (rejects "E_RESOURCE_LOAN"
  [allocate, write 1, .borrow 2 (.loan 1) first .write, .release 1])
#eval check "returned child resumes parent" (accepts [allocate, write 1,
  .borrow 2 (.loan 1) first .write, .fill 2 value, .release 2, .fill 1 value, .release 1, .drop 0])
#eval check "child cannot expand parent region" (rejects "E_RESOURCE_REGION"
  [allocate, write 1 first, .borrow 2 (.loan 1) full .write])
#eval check "read child cannot upgrade authority" (rejects "E_RESOURCE_ACCESS"
  [allocate, write 1, .fill 1 value, .release 1, read 2, .borrow 3 (.loan 2) first .write])
#eval check "siblings need disjoint write regions" (rejects "E_RESOURCE_ALIAS"
  [allocate, write 1, .borrow 2 (.loan 1) first .write, .borrow 3 (.loan 1) first .write])
#eval check "split parent into disjoint writes" (accepts [allocate, write 1,
  .borrow 2 (.loan 1) first .write, .borrow 3 (.loan 1) second .write,
  .fill 2 value, .fill 3 value, .release 3, .release 2, .release 1, .drop 0])
#eval check "complex storage cannot accept real scalar" (rejects "E_RESOURCE_TYPE"
  [.allocate 0 .complexF64 4, write 1, .fill 1 value])
#eval check "cell bounds checked before access" (rejects "E_RESOURCE_BOUNDS"
  [allocate, write 1, .store 1 2 0 value])
#eval check "layout bounds" (rejects "E_RESOURCE_LAYOUT" [allocate, write 1 ⟨0, 4, 4, 4, false⟩])
#eval check "dense write injectivity" (rejects "E_RESOURCE_LAYOUT" [allocate, write 1 ⟨0, 3, 2, 2, false⟩])
#eval check "native size overflow" (rejects "E_RESOURCE_OVERFLOW" [.allocate 0 .f64 byteLimit])
#eval check "native leading dimension overflow even when empty" (rejects "E_RESOURCE_LAYOUT"
  [allocate, write 1 ⟨0, 0, 0, dimensionLimit + 1, false⟩])
#eval check "empty storage performs no cell access" (accepts [.allocate 0 .f64 0,
  write 1 ⟨0, 0, 4, 1, false⟩, .fill 1 value, .release 1, .drop 0])
#eval check "empty metadata may have unaligned offset" (accepts [allocate,
  write 1 ⟨3, 0, 4, 1, false⟩, .fill 1 value, .release 1, .drop 0])
#eval check "nonempty offset must align" (rejects "E_RESOURCE_LAYOUT" [allocate, write 1 ⟨3, 1, 1, 1, false⟩])

private def branch (yes no : List Action) (after : List Action := []) : List Statement :=
  actions [allocate, write 1] ++ [.branch true (actions yes) (actions no)] ++ actions after
#eval check "constant conditions do not hide invalid resources" (!(checkPlan
  (branch [.fill 1 value] [.store 1 9 0 value] [.release 1, .drop 0])).isOk)
#eval check "initialization joins intersect both branches" (!(checkPlan
  (branch [.fill 1 value] [] [.release 1, read 2, .release 2, .drop 0])).isOk)
#eval check "join retains common initialized cells" ((checkPlan
  (branch [.fill 1 value] [.store 1 0 0 value]
    [.release 1, read 2 first, .expect 2 0 0 value, .release 2, .drop 0])).isOk)
#eval check "one-branch move cannot revive owner" (!(checkPlan
  (actions [allocate] ++ [.branch false (actions [.move 0 3]) []] ++ actions [.drop 0])).isOk)
#eval check "same move in both branches" ((checkPlan
  (actions [allocate] ++ [.branch false (actions [.move 0 3]) (actions [.move 0 3])] ++ actions [.drop 3])).isOk)
#eval check "branch-local allocations are released with distinct identities" ((checkPlan
  [.branch true (actions [.allocate 0 .f64 1, .drop 0])
    (actions [.allocate 0 .f64 1, .drop 0])]).isOk)

#eval check "repeated unchanged joins reuse initialization history" ((checkPlan
  (actions [allocate, write 1, .fill 1 value] ++ List.replicate 128 (.branch true [] []) ++
    actions [.release 1, read 2, .release 2, .drop 0])).isOk)
#eval check "repeated writes retain bounded initialization metadata" ((checkPlan
  (actions [allocate, write 1] ++ actions (List.replicate 128 (.fill 1 value)) ++
    actions [.release 1, read 2, .release 2, .drop 0])).isOk)
#eval check "global node budget includes both branches" (
  match checkPlan (List.replicate 1400 (.branch true
    (actions [.allocate 0 .f64 1, .drop 0]) (actions [.allocate 1 .f64 1, .drop 1]))) with
  | .error e => e.code == "E_RESOURCE_LIMIT" | _ => false)

private def forged : State := {
  allocations := [⟨0, 0, .f64, 8, .written full .none, 0⟩], used := [0], nextAllocation := 1 }
#eval check "forged initialization layout is independently rejected" (!auditState forged)
#eval check "forged input environment cannot be laundered by drop" (
  match checkAction forged (.drop 0) with | .error e => e.code == "E_RESOURCE_STATE" | _ => false)
#eval check "unknown identity is not allocation provenance" (!auditState {
  loans := [⟨1, 99, first, .write, none⟩], used := [1], nextAllocation := 100 })
#eval check "forged exponentially shared history has a finite audit budget" (!auditState {
  allocations := [⟨0, 0, .f64, 8,
    (List.range 64).foldl (fun history _ => .intersection history history) (.written first .none), 0⟩]
  used := [0], nextAllocation := 1 })
#eval check "join cannot launder a forged branch" (
  match join forged forged with | .error e => e.code == "E_RESOURCE_STATE" | _ => false)

private def cells (layout : Layout) (scalar : Scalar) : List Nat :=
  (List.range layout.logicalRows).flatMap fun row => (List.range layout.logicalColumns).flatMap fun column =>
    (List.range scalar.width).map (layout.address scalar row column + ·)

/-- Small independent byte-set oracle only in tests; the checker never expands
the matrix. Include padded, transposed, shifted and empty rectangles. -/
private def enumerated : IO Unit := do
  let layouts := (List.range 4).flatMap fun rows => (List.range 4).flatMap fun columns =>
    (List.range 5).flatMap fun leading => (List.range 4).flatMap fun offset =>
      [Layout.mk (offset * 8) rows columns leading false,
       Layout.mk (offset * 8) rows columns leading true]
  for scalar in [Scalar.f64, .complexF64] do
    let valid := layouts.filter (checkLayout scalar 256)
    for outer in valid do
      let accessed := cells outer scalar
      check "accepted layout actual byte bounds" (accessed.all (· < 256))
      check "accepted layout actual byte injectivity" (accessed.all fun byte => accessed.count byte == 1)
      for inner in valid do
        if outer.covers inner scalar then
          check "containment covers actual bytes including padding" ((cells inner scalar).all accessed.contains)
        if outer.disjoint inner scalar then
          check "disjoint envelopes imply disjoint actual bytes" (!(cells inner scalar).any accessed.contains)
#eval enumerated
#eval check "huge layouts do not enumerate cells" (checkLayout .f64 byteLimit ⟨0, 1000000000, 1000000000, 1000000000, false⟩)

end VastitasKernel.Storage.Regression
