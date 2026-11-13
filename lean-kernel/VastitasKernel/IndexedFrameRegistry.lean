import VastitasKernel.IndexedFrameContracts
import VastitasKernel.IndexedPrimitiveDescriptors

set_option autoImplicit false

/-! The registry entries of the frame bindings (Stage 4, #759).

`PrimitiveBinding.contract` (`IndexedPrimitiveRegistry`) takes the entry of
each frame binding from here, one definition per constructor, named as the
constructor and built from the binding's own data. Each entry is a `simp`
lemma, so that the proofs that case on every binding see the entry through
`PrimitiveBinding.contract`.

The contracts are those of `IndexedFrameContracts`. The shapes keep frames
static: an array names its frame and a map its two frames as indices
(`Slot.frameVar`, `Slot.fixedFrame`), so applying a map to an array in
another frame, composing maps whose middle frames differ, or pairing arrays
of two frames is a mismatch of the call's operands, not a run-time failure
(`Relation.sameFrame`). A component or an entry is checked against the
dimension of the frame it reads (`Relation.frameBound`). Points are checked at
run time: an array over another point, or two maps whose middle points
differ, give the failure value.

The evaluators read the embedded frame data only, never the environment,
except that `frame_vector` reads the variance of its array family, as
`fiber_vector` reads the variance of its fiber family. The logical evaluator
keeps the frame arrays apart from the fibers (`IndexedValue.frameArray`); the
erased evaluator and the lowering apply the operations of `FrameRuntime` and
`SmoothRuntime` that generated programs link, on the frame matrices `P` and
`Q` that the binding embeds. A generated module declares each such matrix
once (`SharedLiteral.frame`). `frame_equal` compares maps or arrays by the
representation of its family, which the lowering reads from the module
(`RenderContext.frameMaps`). No frame binding has a derivative rule of its
own: `frame_matrix` runs the recomputing reverse pass inside its call. -/
namespace VastitasKernel.Indexed.Core.Semantics

/-- An array of `coords` at `point` from integer components. Its variance is
the declared variance of `coords`. -/
def frameVectorValue (env : Indexed.Environment) (coords : DeclId) (point : SmoothRuntime.Program)
    (values : List Value) : Option Value := do
  let variance ← frameFiberVariance? env coords
  let components ← values.mapM Value.integer?
  pure (.indexed (.frameArray variance (SmoothRuntime.vector point components)))

end VastitasKernel.Indexed.Core.Semantics

namespace VastitasKernel.Indexed

/-- How the role table names an operand of this variance. -/
def Variance.role : Variance → String
  | .tangent => "vector"
  | .cotangent => "covector"

/-- The runtime operation that encodes an operand of this variance. -/
def Variance.encodeName : Variance → String
  | .tangent => "encodeTangent"
  | .cotangent => "encodeCotangent"

/-- The runtime operation that decodes an array of this variance. -/
def Variance.decodeName : Variance → String
  | .tangent => "decodeTangent"
  | .cotangent => "decodeCotangent"

end VastitasKernel.Indexed

namespace VastitasKernel.Indexed.FrameRegistry
open VastitasKernel.Indexed.Core.Semantics (frameVectorValue fiberVectorRuntime)
open VastitasKernel.Indexed.Lowering (application frame smooth renderFrame arityMismatch)

/-- The entry of `frameEncode`: a vector or covector over the frame's object
to its array in the frame. -/
@[simp] def frameEncode (variance : Variance) (fiber coords : DeclId) (frameRef : FrameRef) :
    PrimitiveDescriptor :=
  .ofBool
    { operands := [.indexed variance.role fiber [.fixed (.global frameRef.object) "object" "the frame's object"]],
      result := .constant ⟨coords, [.frame frameRef.frame]⟩ }
    (fun env => frameEncodeValid env variance fiber coords frameRef)
    (fun _ values => match values with
      | [.indexed (.fiber _ value)] => some (.indexed (.frameArray variance (frameRef.encode variance value)))
      | _ => none)
    (fun values => match values with
      | [.fiber value] => some (.fiber (frameRef.encode variance value))
      | _ => none)
    (fun ctx args => match args with
      | [value] => .ok (application (frame variance.encodeName) [renderFrame ctx (frameRef.encodeMatrix variance), value])
      | _ => arityMismatch)
    .none
    (literals := [.frame (frameRef.encodeMatrix variance)])

/-- The entry of `frameDecode`: an array in the frame to its vector or covector
over the frame's object. -/
@[simp] def frameDecode (variance : Variance) (coords fiber : DeclId) (frameRef : FrameRef) :
    PrimitiveDescriptor :=
  .ofBool
    { operands := [.indexed "array" coords [.fixedFrame frameRef.frame "frame" "the primitive's frame"]],
      result := .indexed fiber [.fixed (.global frameRef.object)] }
    (fun env => frameDecodeValid env variance coords fiber frameRef)
    (fun _ values => match values with
      | [.indexed (.frameArray _ value)] => some (.indexed (.fiber variance (frameRef.decode variance value)))
      | _ => none)
    (fun values => match values with
      | [.fiber value] => some (.fiber (frameRef.decode variance value))
      | _ => none)
    (fun ctx args => match args with
      | [value] => .ok (application (frame variance.decodeName) [renderFrame ctx (frameRef.decodeMatrix variance), value])
      | _ => arityMismatch)
    .none
    (literals := [.frame (frameRef.decodeMatrix variance)])

/-- The entry of `frameVector`: an array in the frame `frameId` on `object`,
from a point of `object` and `dim object` integers. -/
@[simp] def frameVector (coords smoothFamily object frameId : DeclId) : PrimitiveDescriptor :=
  .ofBool
    { operands := [.indexed "point" smoothFamily [.var "source", .fixed (.global object) "target" "the frame's object"]],
      tail := some fun env => smoothArity env object, relations := [.pointDimension ⟨0, 0⟩ 0],
      result := .constant ⟨coords, [.frame frameId]⟩ }
    (fun env => frameVectorValid env coords smoothFamily object frameId)
    (fun env values => match values with
      | .indexed (.smooth point) :: components => frameVectorValue env coords point components
      | _ => none)
    (fun values => match values with
      | .smooth point :: components => fiberVectorRuntime point components
      | _ => none)
    (fun _ args => match args with
      | point :: components => .ok (application (smooth "vector") [point, s!"[{String.intercalate ", " components}]"])
      | _ => arityMismatch)
    .none

/-- The entry of `frameMatrix`: the matrix of the tangent map of a map `X → Y`
at a point of `X`, in the frame `source` on `X` and `target` on `Y`. -/
@[simp] def frameMatrix (smoothFamily map : DeclId) (source target : FrameRef) : PrimitiveDescriptor :=
  .ofBool
    { operands := [
        .indexed "map" smoothFamily [.fixed (.global source.object) "source" "the source frame's object",
          .fixed (.global target.object) "target" "the target frame's object"],
        .indexed "point" smoothFamily [.var "source", .fixed (.global source.object) "target" "the source frame's object"]],
      relations := [.pointDimension ⟨1, 0⟩ 0],
      result := .constant ⟨map, [.frame source.frame, .frame target.frame]⟩ }
    (fun env => frameMatrixValid env smoothFamily map source target)
    (fun _ values => match values with
      | [.indexed (.smooth function), .indexed (.smooth point)] =>
        some (.indexed (.frameMatrix (FrameRuntime.frameMatrix function point source.matrix target.inverse)))
      | _ => none)
    (fun values => match values with
      | [.smooth function, .smooth point] =>
        some (.frameMatrix (FrameRuntime.frameMatrix function point source.matrix target.inverse))
      | _ => none)
    (fun ctx args => match args with
      | [function, point] =>
        .ok (application (frame "frameMatrix")
          [function, point, renderFrame ctx source.matrix, renderFrame ctx target.inverse])
      | _ => arityMismatch)
    .none
    (literals := [.frame source.matrix, .frame target.inverse])

/-- The entry of `frameTransition`: the change from the frame `source` to the
frame `target` of one object at a point. -/
@[simp] def frameTransition (smoothFamily map : DeclId) (source target : FrameRef) : PrimitiveDescriptor :=
  .ofBool
    { operands := [.indexed "point" smoothFamily [.var "source", .fixed (.global source.object) "target" "the frames' object"]],
      relations := [.pointDimension ⟨0, 0⟩ 0],
      result := .constant ⟨map, [.frame source.frame, .frame target.frame]⟩ }
    (fun env => frameTransitionValid env smoothFamily map source target)
    (fun _ values => match values with
      | [.indexed (.smooth point)] =>
        some (.indexed (.frameMatrix (FrameRuntime.transition point source.matrix target.inverse)))
      | _ => none)
    (fun values => match values with
      | [.smooth point] => some (.frameMatrix (FrameRuntime.transition point source.matrix target.inverse))
      | _ => none)
    (fun ctx args => match args with
      | [point] =>
        .ok (application (frame "transition") [point, renderFrame ctx source.matrix, renderFrame ctx target.inverse])
      | _ => arityMismatch)
    .none
    (literals := [.frame source.matrix, .frame target.inverse])

/-- The entry of `frameApply`: `FrameMap<b, c>` applied to `Coords<b>`. -/
@[simp] def frameApply (map coords : DeclId) : PrimitiveDescriptor :=
  .ofBool
    { operands := [.indexed "map" map [.frameVar "source frame", .frameVar "target frame"],
        .indexed "array" coords [.frameVar "frame"]],
      relations := [.sameFrame ⟨0, 0⟩ ⟨1, 0⟩],
      result := .indexed coords [.frameIndex ⟨0, 1⟩] }
    (fun env => frameApplyValid env map coords)
    (fun _ values => match values with
      | [.indexed (.frameMatrix matrix), .indexed (.frameArray _ value)] =>
        some (.indexed (.frameArray .tangent (FrameRuntime.apply matrix value)))
      | _ => none)
    (fun values => match values with
      | [.frameMatrix matrix, .fiber value] => some (.fiber (FrameRuntime.apply matrix value))
      | _ => none)
    (fun _ args => match args with
      | [matrix, value] => .ok (application (frame "apply") [matrix, value])
      | _ => arityMismatch)
    .none

/-- The entry of `frameCoapply`: the transpose of `FrameMap<b, c>` applied to
`CoCoords<c>`. -/
@[simp] def frameCoapply (map cocoords : DeclId) : PrimitiveDescriptor :=
  .ofBool
    { operands := [.indexed "map" map [.frameVar "source frame", .frameVar "target frame"],
        .indexed "array" cocoords [.frameVar "frame"]],
      relations := [.sameFrame ⟨0, 1⟩ ⟨1, 0⟩],
      result := .indexed cocoords [.frameIndex ⟨0, 0⟩] }
    (fun env => frameCoapplyValid env map cocoords)
    (fun _ values => match values with
      | [.indexed (.frameMatrix matrix), .indexed (.frameArray _ value)] =>
        some (.indexed (.frameArray .cotangent (FrameRuntime.coapply matrix value)))
      | _ => none)
    (fun values => match values with
      | [.frameMatrix matrix, .fiber value] => some (.fiber (FrameRuntime.coapply matrix value))
      | _ => none)
    (fun _ args => match args with
      | [matrix, value] => .ok (application (frame "coapply") [matrix, value])
      | _ => arityMismatch)
    .none

/-- The entry of `frameCompose`: `FrameMap<c, d>` after `FrameMap<b, c>`. -/
@[simp] def frameCompose (map : DeclId) : PrimitiveDescriptor :=
  .ofBool
    { operands := [.indexed "first map" map [.frameVar "source frame", .frameVar "target frame"],
        .indexed "second map" map [.frameVar "source frame", .frameVar "target frame"]],
      relations := [.sameFrame ⟨0, 0⟩ ⟨1, 1⟩],
      result := .indexed map [.frameIndex ⟨1, 0⟩, .frameIndex ⟨0, 1⟩] }
    (fun env => frameComposeValid env map)
    (fun _ values => match values with
      | [.indexed (.frameMatrix after), .indexed (.frameMatrix before)] =>
        some (.indexed (.frameMatrix (FrameRuntime.compose after before)))
      | _ => none)
    (fun values => match values with
      | [.frameMatrix after, .frameMatrix before] => some (.frameMatrix (FrameRuntime.compose after before))
      | _ => none)
    (fun _ args => match args with
      | [after, before] => .ok (application (frame "compose") [after, before])
      | _ => arityMismatch)
    .none

/-- The entry of `framePairing`: `CoCoords<b>` paired with `Coords<b>`. -/
@[simp] def framePairing (cocoords coords : DeclId) : PrimitiveDescriptor :=
  .ofBool
    { operands := [.indexed "covector array" cocoords [.frameVar "frame"],
        .indexed "vector array" coords [.frameVar "frame"]],
      relations := [.sameFrame ⟨0, 0⟩ ⟨1, 0⟩], result := .integerPair }
    (fun env => framePairingValid env cocoords coords)
    (fun _ values => match values with
      | [.indexed (.frameArray _ covector), .indexed (.frameArray _ vector)] =>
        let (numerator, denominator) := SmoothRuntime.pairing covector vector
        some (.pairInt numerator denominator)
      | _ => none)
    (fun values => match values with
      | [.fiber covector, .fiber vector] =>
        let (numerator, denominator) := SmoothRuntime.pairing covector vector
        some (.pairInt numerator denominator)
      | _ => none)
    (fun _ args => match args with
      | [covector, vector] => .ok (application (smooth "pairing") [covector, vector])
      | _ => arityMismatch)
    .none

/-- The entry of `frameComponent`: component `index` of an array, below the
dimension of its frame. -/
@[simp] def frameComponent (family : DeclId) (index : Nat) : PrimitiveDescriptor :=
  .ofBool
    { operands := [.indexed "array" family [.frameVar "frame"]],
      relations := [.frameBound ⟨0, 0⟩ index "component"], result := .integerPair }
    (fun env => frameComponentValid env family)
    (fun _ values => match values with
      | [.indexed (.frameArray _ value)] =>
        let (numerator, denominator) := SmoothRuntime.component value index
        some (.pairInt numerator denominator)
      | _ => none)
    (fun values => match values with
      | [.fiber value] =>
        let (numerator, denominator) := SmoothRuntime.component value index
        some (.pairInt numerator denominator)
      | _ => none)
    (fun _ args => match args with
      | [value] => .ok (application (smooth "component") [value, toString index])
      | _ => arityMismatch)
    .none

/-- The entry of `frameEntry`: the entry in row `row` and column `column` of a
map, below the dimensions of its target and source frames. -/
@[simp] def frameEntry (map : DeclId) (row column : Nat) : PrimitiveDescriptor :=
  .ofBool
    { operands := [.indexed "map" map [.frameVar "source frame", .frameVar "target frame"]],
      relations := [.frameBound ⟨0, 1⟩ row "row", .frameBound ⟨0, 0⟩ column "column"], result := .integerPair }
    (fun env => frameEntryValid env map)
    (fun _ values => match values with
      | [.indexed (.frameMatrix matrix)] =>
        let (numerator, denominator) := FrameRuntime.entry matrix row column
        some (.pairInt numerator denominator)
      | _ => none)
    (fun values => match values with
      | [.frameMatrix matrix] =>
        let (numerator, denominator) := FrameRuntime.entry matrix row column
        some (.pairInt numerator denominator)
      | _ => none)
    (fun _ args => match args with
      | [matrix] => .ok (application (frame "entry") [matrix, toString row, toString column])
      | _ => arityMismatch)
    .none

/-- The entry of `frameEqual`: equality of two arrays, or of two maps, of one
type. The failure value equals nothing. -/
@[simp] def frameEqual (family : DeclId) : PrimitiveDescriptor :=
  .ofBool
    { operands := [.application "first operand" family, .application "second operand" family],
      relations := [.sameApplication 0 1 []], result := .boolean }
    (fun env => frameEqualValid env family)
    (fun _ values => match values with
      | [.indexed (.frameArray _ left), .indexed (.frameArray _ right)] =>
        some (.boolean (SmoothRuntime.fiberEqual left right))
      | [.indexed (.frameMatrix left), .indexed (.frameMatrix right)] =>
        some (.boolean (FrameRuntime.matrixEqual left right))
      | _ => none)
    (fun values => match values with
      | [.fiber left, .fiber right] => some (.boolean (SmoothRuntime.fiberEqual left right))
      | [.frameMatrix left, .frameMatrix right] => some (.boolean (FrameRuntime.matrixEqual left right))
      | _ => none)
    (fun ctx args => match args with
      | [left, right] =>
        .ok (application (if ctx.frameMaps.contains family then frame "matrixEqual" else smooth "fiberEqual")
          [left, right])
      | _ => arityMismatch)
    .none

/-- The entry of `frameAt`: whether an array lies over a point of its frame's
object. -/
@[simp] def frameAt (family smoothFamily : DeclId) : PrimitiveDescriptor :=
  .ofBool
    { operands := [.indexed "array" family [.frameVar "frame"],
        .indexed "point" smoothFamily [.var "source", .var "target"]],
      relations := [.frameObject ⟨0, 0⟩ ⟨1, 1⟩ "the object of the array's frame", .pointDimension ⟨1, 0⟩ 0],
      result := .boolean }
    (fun env => frameAtValid env family smoothFamily)
    (fun _ values => match values with
      | [.indexed (.frameArray _ value), .indexed (.smooth point)] =>
        some (.boolean (SmoothRuntime.fiberAt value point))
      | _ => none)
    (fun values => match values with
      | [.fiber value, .smooth point] => some (.boolean (SmoothRuntime.fiberAt value point))
      | _ => none)
    (fun _ args => match args with
      | [value, point] => .ok (application (smooth "fiberAt") [value, point])
      | _ => arityMismatch)
    .none

end VastitasKernel.Indexed.FrameRegistry
