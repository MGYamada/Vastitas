import VastitasKernel.Graph

namespace VastitasKernel.Graph.Regression
open Indexed

private def id (name : String) : DeclId := ⟨⟨⟨"/graph-fixture", "graph-fixture", "1"⟩, []⟩, name⟩
private def env : Environment := [
  ⟨id "QQ", .marker⟩, ⟨id "OtherBase", .marker⟩,
  ⟨id "Line", .implementation (id "QQ") .affineDescriptor []⟩ ]
private def declarations : CheckedEnvironment := ⟨env, by decide⟩
private def object (n : Nat) : ObjectRef := .local ⟨id "Line", id "QQ"⟩ n

private def profile : Profile := {
  tensorGeneric := id "tensor", method := id "lineTensor", implementationRevision := "revision-1"
  identity := id "lineProfile", category := id "GradedLines", coefficient := id "QQ"
  tensorModel := id "tensorModel", unit := id "unit", associator := id "associator"
  leftUnitor := id "leftUnitor", rightUnitor := id "rightUnitor", braiding := some (id "braiding") }

/-- Deliberately synthetic authorization. This fixture tests the checker, not
the existence of a categorical proof or tensor-method implementation. -/
private def FixtureLaws (_ : Profile) (_ : Capability) : Prop := True
private def context (cap : Capability := .braided) (p : Profile := profile) : Context FixtureLaws := {
  declarations, inScope := (List.range 5).map object
  canonicalTensor := id "tensor", selected := p
  authority := ⟨⟨p, cap, id "fixture-evidence"⟩, trivial⟩ }

private def shape : Nat → Shape
  | 0 => .empty
  | 1 => .leaf
  | n+2 => .tensor .leaf (shape (n+1))

private def boundary (degrees : List Int) : Boundary :=
  ⟨17, shape degrees.length, degrees.zipIdx |>.map fun (degree, n) => ⟨n, object n, degree⟩⟩

private def word (degrees : List Int) (ops : List Op) (p : Profile := profile) : Core :=
  (build p (boundary degrees) ops).getD default

private def positive (i : Nat) : Op := ⟨i, .positive⟩
private def negative (i : Nat) : Op := ⟨i, .negative⟩
private def accept (core : Core) (ctx : Context FixtureLaws := context) : Bool :=
  (checkCore ctx core).isOk

private def proposal (core : Core) (rule : Rule) (offset : Nat := 0)
    (ctx : Context FixtureLaws := context) : Request :=
  let ops := core.ops.take offset ++ rule.rhs ++ core.ops.drop (offset + rule.lhs.length)
  ⟨ctx.authority.reference, offset, rule, (build core.profile core.source ops).getD default⟩

private def rewrite (core : Core) (rule : Rule) (offset : Nat := 0)
    (ctx : Context FixtureLaws := context) : Bool :=
  (checkRewrite ctx core (proposal core rule offset ctx)).isOk

private def check (name : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError s!"graph regression failed: {name}")

#eval check "empty monoidal word" (accept (word [1, 1] []) (context .monoidal))
#eval check "empty tensor word" (accept (word [] []) (context .monoidal))
#eval check "plain monoidal rejects both crossing directions" (
  !accept (word [1, 1] [positive 0]) (context .monoidal) &&
  !accept (word [1, 1] [negative 0]) (context .monoidal))
#eval check "braided preserves nontrivial same-direction double crossing" (
  accept (word [1, 1] [positive 0, positive 0]) &&
  !rewrite (word [1, 1] [positive 0, positive 0]) (.inverse 0 .positive) &&
  !rewrite (word [1, 1] [positive 0, positive 0]) (.symmetric 0 .positive))
#eval check "zero degrees do not supply symmetric evidence" (
  !rewrite (word [0, 0] [positive 0, positive 0]) (.symmetric 0 .positive))

#eval do
  let degrees : List Int := [-2, -1, 0, 1, 2]
  for a in degrees do
    for b in degrees do
      for d in [Direction.positive, .negative] do
        check "inverse: all 25 pairs, both signs"
          (rewrite (word [a, b] [⟨0, d⟩, ⟨0, d.inverse⟩]) (.inverse 0 d))
        check "symmetric: all 25 pairs, both signs"
          (rewrite (word [a, b] [⟨0, d⟩, ⟨0, d⟩]) (.symmetric 0 d) 0 (context .symmetric))
      for c in degrees do
        for d in [Direction.positive, .negative] do
          for reverse in [false, true] do
            let rule := Rule.braid 0 d reverse
            check "braid: all 125 triples, both signs and directions"
              (rewrite (word [a, b, c] rule.lhs) rule)

#eval do
  for a in [Direction.positive, .negative] do
    for b in [Direction.positive, .negative] do
      let rule := Rule.far ⟨0, a⟩ ⟨2, b⟩
      check "far commutation, every sign pair" (rewrite (word [1, 2, 3, 4] rule.lhs) rule)
      let reverse := Rule.far ⟨2, b⟩ ⟨0, a⟩
      check "far commutation reverse" (rewrite (word [1, 2, 3, 4] reverse.lhs) reverse)

#eval check "adjacent crossings do not commute" (
  !rewrite (word [0, 0, 0] [positive 0, positive 1]) (.far (positive 0) (positive 1)))
#eval check "mixed-sign braid pattern not silently generalized" (
  !rewrite (word [1, 2, 3] [positive 0, negative 1, positive 0]) (.braid 0 .positive false))
#eval check "inverse preserves prefix and suffix" (
  rewrite (word [1, 2, 3] [negative 1, positive 0, negative 0, positive 1]) (.inverse 0 .positive) 1)
#eval check "braid preserves prefix and suffix" (
  rewrite (word [1, 2, 3, 4] [negative 2, positive 0, positive 1, positive 0, positive 2])
    (.braid 0 .positive false) 1)
#eval check "invalid offset" (!rewrite (word [1, 1] [positive 0, negative 0]) (.inverse 0 .positive) 4)

#eval do
  let core := word [1, 1] [positive 0, negative 0]
  let request := proposal core (.inverse 0 .positive)
  let other := { profile with identity := id "other-profile" }
  check "evidence from another profile" (!(checkRewrite context core
    { request with evidence := { request.evidence with profile := other } }).isOk)
  check "frontend capability cannot upgrade authority" (!(checkRewrite context core
    { request with evidence := { request.evidence with capability := .symmetric } }).isOk)
  check "wrong evidence certificate" (!(checkRewrite context core
    { request with evidence := { request.evidence with certificate := id "other-certificate" } }).isOk)
  for changed in [
      { profile with tensorGeneric := id "user-tensor" },
      { profile with method := id "other-method" },
      { profile with implementationRevision := "stale" },
      other, { profile with category := id "other-category" },
      { profile with coefficient := id "OtherBase" },
      { profile with tensorModel := id "other-tensor" },
      { profile with unit := id "other-unit" },
      { profile with associator := id "other-associator" },
      { profile with leftUnitor := id "other-left-unitor" },
      { profile with rightUnitor := id "other-right-unitor" },
      { profile with braiding := some (id "other-braiding") }] do
    check "every profile component is bound" (!(checkRewrite context core
      { request with evidence := { request.evidence with profile := changed } }).isOk)
    check "different selection cannot borrow authority" (!accept core { context with selected := changed })
  check "canonical identity cannot be spoofed" (!accept core { context with canonicalTensor := id "user-tensor" })
  check "source requires admitted base" (!accept
    (word [1, 1] [] { profile with coefficient := id "OtherBase" })
    (context .braided { profile with coefficient := id "OtherBase" }))
  check "braided profile requires chosen braiding" (!accept
    (word [1, 1] [] { profile with braiding := none })
    (context .braided { profile with braiding := none }))

#eval do
  let core := word [1, 1] [positive 0, positive 0]
  let first := core.crossings.head!
  check "stale ports with equal degrees" (!accept { core with crossings := [first, first] })
  check "wrong crossing degree" (!accept { core with crossings :=
    { first with left := { first.left with degree := 2 } } :: core.crossings.tail })
  check "wrong crossing occurrence ID" (!accept { core with crossings :=
    { first with left := { first.left with occurrence := 9 } } :: core.crossings.tail })
  check "wrong nominal object ID" (!accept { core with crossings :=
    { first with left := { first.left with object := object 3 } } :: core.crossings.tail })
  check "wrong crossing profile" (!accept { core with crossings :=
    { first with profile := { profile with identity := id "other" } } :: core.crossings.tail })
  check "out-of-bounds crossing" (!accept { core with crossings :=
    { first with op := positive 9 } :: core.crossings.tail })
  check "wrong target ports" (!accept { core with target := core.target.reverse })
  let duplicate := { core.source with strands := [first.left, first.left] }
  check "duplicate occurrence IDs" (!accept (build profile duplicate []).get!)
  check "out of scope nominal reference" (!accept core { context with inScope := [object 0] })
  let sameObject := { core.source with strands := [first.left, { first.right with object := first.left.object }] }
  check "same object and degree keep separate occurrences" (accept (build profile sameObject [positive 0]).get!)

#eval do
  let core := word [0, 1] [positive 0, negative 0]
  let request := proposal core (.inverse 0 .positive)
  let double := word [0, 1] [positive 0, positive 0]
  check "same permutation and even same reference scalar are insufficient" (
    !(checkRewrite context core { request with after := double }).isOk)
  check "nominal presentation cannot change" (!(checkRewrite context core
    { request with after := { request.after with source := { request.after.source with presentation := 99 } } }).isOk)
  let triple := word [1, 2, 3] [positive 0, negative 0]
  let tripleRequest := proposal triple (.inverse 0 .positive)
  let reassociated := { tripleRequest.after with source :=
    { tripleRequest.after.source with shape := .tensor (.tensor .leaf .leaf) .leaf } }
  check "reassociation is not nominal equality" (!(checkRewrite context triple
    { tripleRequest with after := reassociated }).isOk)
  let contextWord := word [1, 1, 1] [positive 0, positive 1, positive 0, positive 1]
  let braidRequest := proposal contextWord (.braid 0 .positive false)
  check "orientation erased in unchanged context" (!(checkRewrite context contextWord
    { braidRequest with after := word [1, 1, 1] [positive 1, positive 0, positive 1, negative 1] }).isOk)

#eval do
  let initial := word [1, 2] [positive 0, negative 0, negative 0, positive 0]
  let first := proposal initial (.inverse 0 .positive)
  let second := proposal first.after (.inverse 0 .negative)
  check "trace accepts exact returned Core" ((checkTrace context initial [first, second] second.after).isOk)
  check "trace rejects intermediate return" (!(checkTrace context initial [first, second] first.after).isOk)
  check "trace rejects reordered steps" (!(checkTrace context initial [second, first] second.after).isOk)
  check "trace rejects skipped steps" (!(checkTrace context initial [] second.after).isOk)

end VastitasKernel.Graph.Regression
