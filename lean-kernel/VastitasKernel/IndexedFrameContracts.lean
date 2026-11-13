import VastitasKernel.IndexedPrimitiveBinding
import VastitasKernel.FrameRuntime

set_option autoImplicit false

/-! The validity contracts of the frame bindings (Stage 4, #759), next to the
bindings as `IndexedSmoothContracts` holds those of the smooth bindings: the
checks that the entries of `IndexedFrameRegistry` name.

A frame-array family `Coords(b)` or `CoCoords(b)` is sealed: its one index is
a frame declaration, and its runtime value is the coordinates of a vector or
covector in that frame, at a point, or the failure value. A frame-map family
`FrameMap(b, c)` is sealed in the same way, with two frame indices. The
contracts below name the families of each operand, so a vector array where a
covector array is required, or an array where a map is required, fails the
binding.

The bindings that apply a frame embed it as a `FrameRef`: the frame
declaration, its smooth object, its matrix `P` and its inverse `Q`. The
contract requires every embedded copy to equal the declaration exactly
(`frameDeclared`), so a forged object, matrix or inverse fails the
declaration audit. The declaration audit checks the declaration itself once
(`FrameDeclarations.checkFrame`); the contracts do not repeat its products.
No contract consults a metric declaration, a base chain or a descriptor
capability. -/
namespace VastitasKernel.Indexed

/-- The variance of a family declared with the sealed `frame_vector`
(`tangent`) or `frame_covector` (`cotangent`) representation. -/
def frameFiberVariance? (env : Environment) (family : DeclId) : Option Variance :=
  match lookup env family with
  | some (.family contract) => match contract.representation with
    | .frameFiber variance => some variance
    | _ => none
  | _ => none

/-- The family is declared with the sealed `frame_map` representation. -/
def isFrameMapFamily (env : Environment) (family : DeclId) : Bool :=
  match lookup env family with
  | some (.family contract) => contract.representation == .frameMap
  | _ => false

/-- The embedded frame is its declaration: `frame.frame` is a frame
declaration on `frame.object` with exactly the embedded matrix and inverse. -/
def frameDeclared (env : Environment) (frame : FrameRef) : Bool :=
  match frameData? env frame.frame with
  | some (_, object, matrix, inverse) =>
    object == frame.object && matrix == frame.matrix && inverse == frame.inverse
  | none => false

/-- `frame_encode(F, C, frame = b)`: a vector (`tangent`) or covector
(`cotangent`) of the fiber family `F` over the frame's object to its array in
the frame, of the frame-array family `C`. Both families have the binding's
variance, and both types the binding fixes are valid. -/
def frameEncodeValid (env : Environment) (variance : Variance) (fiber coords : DeclId) (frame : FrameRef) :
    Bool :=
  frameDeclared env frame && fiberVariance? env fiber == some variance &&
    frameFiberVariance? env coords == some variance &&
    validApplication env ⟨fiber, [.object (.global frame.object)]⟩ &&
    validApplication env ⟨coords, [.frame frame.frame]⟩

/-- `frame_decode(C, F, frame = b)`: the inverse of `frame_encode`, from an
array of `C` in the frame to a vector or covector of `F`. -/
def frameDecodeValid (env : Environment) (variance : Variance) (coords fiber : DeclId) (frame : FrameRef) :
    Bool :=
  frameDeclared env frame && frameFiberVariance? env coords == some variance &&
    fiberVariance? env fiber == some variance &&
    validApplication env ⟨coords, [.frame frame.frame]⟩ &&
    validApplication env ⟨fiber, [.object (.global frame.object)]⟩

/-- `frame_vector(C, S, frame = b)`: an array of `C` in the frame `b` on
`object`, from a point of `object` in the smooth family `S` and `dim object`
integers. -/
def frameVectorValid (env : Environment) (coords smooth object frame : DeclId) : Bool :=
  (frameFiberVariance? env coords).isSome && isSmoothFamily env smooth && frameObject? env frame == some object &&
    (smoothDimension? env object).isSome && validApplication env ⟨coords, [.frame frame]⟩

/-- `frame_matrix(S, M, source = b, target = c)`: the matrix of the tangent map
of a map `X → Y` in `S` at a point, in the frame `b` on `X` and the frame `c`
on `Y`, of the frame-map family `M`. -/
def frameMatrixValid (env : Environment) (smooth map : DeclId) (source target : FrameRef) : Bool :=
  isSmoothFamily env smooth && isFrameMapFamily env map && frameDeclared env source &&
    frameDeclared env target && validApplication env ⟨map, [.frame source.frame, .frame target.frame]⟩

/-- `frame_transition(S, M, source = b, target = b′)`: the change from the frame
`b` to the frame `b′`, two frames of one object, at a point in `S`. -/
def frameTransitionValid (env : Environment) (smooth map : DeclId) (source target : FrameRef) : Bool :=
  isSmoothFamily env smooth && isFrameMapFamily env map && frameDeclared env source &&
    frameDeclared env target && source.object == target.object &&
    validApplication env ⟨map, [.frame source.frame, .frame target.frame]⟩

/-- `frame_apply(M, C)`: a map of `M` applied to a vector array of `C`. -/
def frameApplyValid (env : Environment) (map coords : DeclId) : Bool :=
  isFrameMapFamily env map && frameFiberVariance? env coords == some .tangent

/-- `frame_coapply(M, D)`: the transpose of a map of `M` applied to a covector
array of `D`. -/
def frameCoapplyValid (env : Environment) (map cocoords : DeclId) : Bool :=
  isFrameMapFamily env map && frameFiberVariance? env cocoords == some .cotangent

/-- `frame_compose(M)`: the composite of two maps of `M`. -/
def frameComposeValid (env : Environment) (map : DeclId) : Bool := isFrameMapFamily env map

/-- `frame_pairing(D, C)`: the pairing of a covector array of `D` with a vector
array of `C` in one frame. -/
def framePairingValid (env : Environment) (cocoords coords : DeclId) : Bool :=
  frameFiberVariance? env cocoords == some .cotangent && frameFiberVariance? env coords == some .tangent

/-- `frame_component(C, i)`: component `i` of an array of `C`. The call checks
`i` against the dimension of the array's frame. -/
def frameComponentValid (env : Environment) (family : DeclId) : Bool := (frameFiberVariance? env family).isSome

/-- `frame_entry(M, i, j)`: an entry of a map of `M`. The call checks `i` and
`j` against the dimensions of the map's frames. -/
def frameEntryValid (env : Environment) (map : DeclId) : Bool := isFrameMapFamily env map

/-- `frame_equal(F)`: equality of two arrays, or of two maps, of `F`. -/
def frameEqualValid (env : Environment) (family : DeclId) : Bool :=
  (frameFiberVariance? env family).isSome || isFrameMapFamily env family

/-- `frame_at(C, S)`: whether an array of `C` lies over a point in `S`. -/
def frameAtValid (env : Environment) (family smooth : DeclId) : Bool :=
  (frameFiberVariance? env family).isSome && isSmoothFamily env smooth

/-! ## The runtime operations of encoding and decoding

The erased and logical evaluators, and the lowering, of `frame_encode` and
`frame_decode` select one runtime operation by the binding's variance and
pass it the matrix of the frame that it reads. -/

/-- The array of a vector, `Q(p) v`, or of a covector, `P(p)ᵀ α`. -/
def FrameRef.encode (frame : FrameRef) : Variance → SmoothRuntime.FiberValue → SmoothRuntime.FiberValue
  | .tangent => FrameRuntime.encodeTangent frame.inverse
  | .cotangent => FrameRuntime.encodeCotangent frame.matrix

/-- The vector of an array, `P(p) a`, or the covector, `Q(p)ᵀ a`. -/
def FrameRef.decode (frame : FrameRef) : Variance → SmoothRuntime.FiberValue → SmoothRuntime.FiberValue
  | .tangent => FrameRuntime.decodeTangent frame.matrix
  | .cotangent => FrameRuntime.decodeCotangent frame.inverse

/-- The matrix that `encode` reads: `Q` for a vector, `P` for a covector. -/
def FrameRef.encodeMatrix (frame : FrameRef) : Variance → PolyMatrix
  | .tangent => frame.inverse
  | .cotangent => frame.matrix

/-- The matrix that `decode` reads: `P` for a vector, `Q` for a covector. -/
def FrameRef.decodeMatrix (frame : FrameRef) : Variance → PolyMatrix
  | .tangent => frame.matrix
  | .cotangent => frame.inverse

end VastitasKernel.Indexed
