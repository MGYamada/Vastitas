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

#eval show IO Unit from do
  for scalar in [Scalar.f64, .complexF64] do
    for offset in [0, 8, 16] do
      for transposed in [false, true] do
        for leading in [2, 3] do
          let view : Layout := ⟨offset, 2, 2, leading, transposed⟩
          let valid := scalar == .f64 || offset % 16 == 0
          let plan := [Action.allocate 0 scalar 8, .borrow 1 (.owner 0) view .write,
            .release 1, .drop 0]
          check "typed nonempty views preserve element boundaries" (accepts plan == valid)
          check "empty views retain vacuous element boundaries" (accepts
            [.allocate 0 scalar 8, .borrow 1 (.owner 0) {view with rows := 0} .read,
              .release 1, .drop 0])
  let whole : Layout := ⟨0, 8, 1, 8, false⟩
  let half : Layout := ⟨8, 1, 1, 1, false⟩
  check "contiguous containment cannot justify a half complex element" (!whole.covers half .complexF64)
  check "padded containment cannot justify a half complex element" (!padded.covers half .complexF64)
  check "real element containment is unchanged" (whole.covers half .f64)
  check "reborrow cannot create half complex elements" (rejects "E_RESOURCE_REGION"
    [.allocate 0 .complexF64 8, .borrow 1 (.owner 0) whole .write,
      .borrow 2 (.loan 1) half .write])
  let forged : State := {
    allocations := [⟨0, 0, .complexF64, 128, .written half .none, 0⟩]
    used := [0], nextAllocation := 1 }
  check "forged initialization cannot confer half-element access" (!auditState forged)

-- Self-copy must preserve the complete checked state, not only acceptance or
-- cell values. In particular it cannot invalidate an unchanged cached version.
#eval show IO Unit from do
  for (scalar, literal) in [(Scalar.f64, value), (.complexF64, .complexF64 0 0)] do
    for layout in [padded, padded.transpose, ⟨3,0,4,1,false⟩] do
      let setup := actions [.allocate 0 scalar 8, write 1 layout, .fill 1 literal,
        .release 1, .borrow 2 (.owner 0) layout .readWrite, .captureDependency 3 2 2]
      let .ok before := run 4096 {} setup | throw (IO.userError "self-copy setup failed")
      let .ok after := checkAction before (.copy 2 2) | throw (IO.userError "self-copy rejected")
      check "self-copy preserves initialization, versions and dependencies" (after == before)
      check "self-copy retains dependency validity" (checkAction after (.requireDependency 3)).isOk
      check "self-copy plan closes" (checkPlan (setup ++ actions
        [.copy 2 2, .requireDependency 3, .forgetDependency 3, .release 2, .drop 0])).isOk
#eval check "self-copy requires write access" (rejects "E_RESOURCE_ACCESS"
  [allocate, write 1, .fill 1 value, .release 1, read 2, .copy 2 2])
#eval check "self-copy requires read access even after fill" (rejects "E_RESOURCE_ACCESS"
  [allocate, write 1, .fill 1 value, .copy 1 1])
#eval check "self-copy cannot initialize storage" (rejects "E_RESOURCE_INIT"
  [allocate, .borrow 1 (.owner 0) full .readWrite, .copy 1 1])
#eval check "self-copy cannot access suspended parent" (rejects "E_RESOURCE_LOAN"
  [allocate, write 1, .fill 1 value, .release 1, .borrow 2 (.owner 0) full .readWrite,
    .borrow 3 (.loan 2) first .read, .copy 2 2])
#eval check "self-copy cannot revive returned loan" (rejects "E_RESOURCE_LOAN"
  [allocate, write 1, .fill 1 value, .release 1, .copy 1 1])

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
#eval show IO Unit from do
  for scalar in [Scalar.f64, .complexF64] do
    let literal := if scalar == .f64 then value else Literal.complexF64 0 0
    let shared : Layout := ⟨128 * scalar.width, 1, 1, 1, false⟩
    let initial := actions [.allocate 0 scalar 129,
      .borrow 1 (.owner 0) ⟨0, 1, 129, 1, false⟩ .write, .store 1 0 128 literal]
    let branches := (List.range 64).map fun index => Statement.branch true
      (actions [.store 1 0 (2 * index) literal]) (actions [.store 1 0 (2 * index + 1) literal])
    let .ok state := run 1024 {} (initial ++ branches)
      | throw (IO.userError "sequential disjoint branch writes exceeded history budget")
    check "disjoint branch additions retain the exact common history"
      ((state.allocation? 0).map Allocation.initialization == some (.written shared .none))
    check "common initialized cell remains readable after many joins"
      (checkPlan (initial ++ branches ++ actions [.release 1,
        .borrow 2 (.owner 0) shared .read, .expect 2 0 0 literal, .release 2, .drop 0])).isOk
    check "branch-local writes do not initialize either exclusive cell"
      (!(checkPlan (initial ++ branches ++ actions [.release 1,
        .borrow 2 (.owner 0) ⟨0, 1, 1, 1, false⟩ .read, .release 2, .drop 0])).isOk)

private def longHistory : Initialization :=
  (List.range 2100).foldl (fun previous _ => .written first previous) .none
private def largeJoinState (layout : Layout) : State := {
  allocations := [⟨0, 0, .f64, 64, .written layout longHistory, 0⟩]
  used := [0], nextAllocation := 1 }
#eval check "valid unresolved intersection names its initialization budget"
  (auditState (largeJoinState full) && auditState (largeJoinState first) &&
    match join (largeJoinState full) (largeJoinState first) with
    | .error error => error.code == "E_RESOURCE_LIMIT" &&
        error.message == "branch join initialization metadata budget exceeded"
    | .ok _ => false)
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

private def initializedCells (scalar : Scalar) : Initialization → List Nat
  | .none => []
  | .written layout previous => cells layout scalar ++ initializedCells scalar previous
  | .intersection left right =>
    (initializedCells scalar left).filter (initializedCells scalar right).contains

/- Independent byte enumeration includes overlapping, disjoint, padded,
transposed and empty writes. Exact normalization must neither invent nor lose
common initialized bytes, even when it cannot simplify the intersection. -/
#eval show IO Unit from do
  let layouts := [full, padded, first, second, padded.transpose, ⟨3, 0, 1, 1, false⟩]
  for scalar in [Scalar.f64, .complexF64] do
    for common in [Initialization.none, .written first .none, .intersection
        (.written full .none) (.written padded .none)] do
      for a in layouts do
        for b in layouts do
          let left := Initialization.written a common
          let right := Initialization.written b common
          for pair in [(left, right), (left, common), (common, right), (left, left)] do
            let actual := initializedCells scalar (pair.1.meet pair.2 scalar)
            let leftBytes := initializedCells scalar pair.1
            let rightBytes := initializedCells scalar pair.2
            check "normalized join is the exact byte intersection" ((List.range 160).all fun byte =>
              actual.contains byte == (leftBytes.contains byte && rightBytes.contains byte))

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

private def matrix : Layout := ⟨0, 2, 3, 2, false⟩
private def matrixStores : List Action :=
  [(0,0), (0,1), (0,2), (1,0), (1,1), (1,2)].map fun (row, column) => .store 1 row column value
private def matrixPrefix : List Action := [allocate, write 1 matrix]
private def matrixSuffix : List Action := [.release 1, read 2 matrix.transpose,
  .expect 2 2 1 value, .release 2, .move 0 3, .drop 3]
#eval check "individual unordered stores initialize the complete transposed read" (
  accepts (matrixPrefix ++ matrixStores ++ matrixSuffix))
#eval check "individual stores initialize a padded rectangle without touching gaps" (accepts
  ([.allocate 0 .f64 16, write 1 ⟨8,2,3,4,false⟩] ++ matrixStores ++
    [.release 1, read 2 ⟨8,2,3,4,true⟩, .expect 2 2 1 value, .release 2, .drop 0]))
#eval check "padded cell union still cannot initialize a gap" (rejects "E_RESOURCE_INIT"
  ([.allocate 0 .f64 16, write 1 ⟨8,2,3,4,false⟩] ++ matrixStores ++
    [.release 1, read 2 ⟨24,1,1,1,false⟩]))
#eval check "omitting one store leaves a real hole" (
  rejects "E_RESOURCE_INIT" (matrixPrefix ++ matrixStores.take 5 ++ matrixSuffix))
#eval check "different branch write orders establish the same complete region" ((checkPlan
  (actions matrixPrefix ++ [.branch false (actions matrixStores) (actions matrixStores.reverse)] ++
    actions matrixSuffix)).isOk)
#eval check "complementary incomplete branches do not combine their writes" (!(checkPlan
  (actions matrixPrefix ++ [.branch true (actions (matrixStores.take 3)) (actions (matrixStores.drop 3))] ++
    actions matrixSuffix)).isOk)
#eval check "one incomplete branch cannot initialize a whole read" (!(checkPlan
  (actions matrixPrefix ++ [.branch true (actions matrixStores) (actions (matrixStores.take 5))] ++
    actions matrixSuffix)).isOk)

private def scalarCell (scalar : Scalar) (index : Nat) : Layout := ⟨index * scalar.width, 1, 1, 1, false⟩
private def history (scalar : Scalar) (indices : List Nat) : Initialization :=
  indices.foldl (fun previous index => .written (scalarCell scalar index) previous) .none

/- Independent finite byte-set oracle, including branch intersections and
padding. Enumeration is confined to small tests, never the compiler. -/
#eval show IO Unit from do
  for scalar in [Scalar.f64, .complexF64] do
    let subsets := (List.range 16).map fun mask => (List.range 4).filter fun i => mask / 2^i % 2 == 1
    for left in subsets do
      for right in subsets do
        let combined := history scalar (left ++ right.reverse)
        let common := Initialization.intersection (history scalar left) (history scalar right.reverse)
        for start in List.range 4 do
          for size in List.range (5 - start) do
            let query : Layout := ⟨start * scalar.width, size, 1, max 1 size, false⟩
            let wanted := List.range size |>.map (start + ·)
            check "finite union coverage agrees with cell sets"
              (combined.covers scalar query == wanted.all (fun i => left.contains i || right.contains i))
            check "finite branch coverage agrees with cell intersections"
              (common.covers scalar query == wanted.all (fun i => left.contains i && right.contains i))
        for transposed in [false, true] do
          for offset in [0, scalar.width] do
            let query : Layout := ⟨offset,1,2,2,transposed⟩
            let wanted := cells query scalar |>.map (· / scalar.width)
            check "padded union coverage excludes gaps in both orientations"
              (combined.covers scalar query == wanted.all (fun i => left.contains i || right.contains i))
            check "padded branch coverage uses the actual common cells"
              (common.covers scalar query == wanted.all (fun i => left.contains i && right.contains i))
    let paddedWrite : Layout := ⟨0, 1, 2, 2, false⟩
    let paddedHistory := Initialization.written paddedWrite (history scalar [3])
    check "union never flattens padded writes"
      (!(paddedHistory.covers scalar ⟨0,4,1,4,false⟩))
    check "a union can explicitly fill a padding gap"
      ((Initialization.written ⟨0,1,1,1,false⟩ (history scalar [1,2,3])).covers scalar ⟨0,4,1,4,false⟩)
  let tooLarge := (List.range 64).foldl (fun h _ => .intersection h h) (history .f64 [0])
  check "coverage bounds forged exponential histories before traversal" (!tooLarge.covers .f64 first)
  check "interval work exhaustion does not infer missing initialization"
    (!(history .f64 (List.range 300)).covers .f64 ⟨0,300,1,300,false⟩)
  check "uncovered huge padded requests reject before column enumeration"
    (!(history .f64 [0]).covers .f64 ⟨0,1,1000000000,2,false⟩)
  let large : Layout := ⟨0,1000000000,1000000000,1000000000,false⟩
  let half : Layout := {large with columns := 500000000}
  check "two metadata writes cover a billion-by-billion matrix without enumeration"
    (accepts [.allocate 0 .f64 1000000000000000000,
      write 1 half, .fill 1 value, .release 1,
      write 2 {half with offset := half.endByte .f64}, .fill 2 value, .release 2,
      read 3 large, .release 3, .drop 0])
  IO.println "initialization unions: unordered cells, branch intersection, padding holes, bounded work and huge metadata-only coverage passed"

end VastitasKernel.Storage.Regression
