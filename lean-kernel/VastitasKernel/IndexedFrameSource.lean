import VastitasKernel.IndexedMetricSource
import VastitasKernel.FrameDeclarations
import VastitasKernel.IndexedFrameContracts

set_option autoImplicit false

/-! Source elaboration of frames (Stage 4, #759; ADR 0001 §11).

A frame `Frame<X>` is declared at a family with the `frame` representation
and one smooth object `X` of dimension `n`, by its columns in the coordinate
frame, `columns((p₁₁, p₂₁, …), (p₁₂, …), …)`, or as `coordinates`, the
coordinate frame `P = I`. `resolveBody` resolves its paths and leaves its
matrix and its inverse empty; this pass elaborates them, after the metrics
and before the relative morphisms:

* `columns` has exactly `n` columns of `n` entries. Each entry is expanded
  in the coordinates of `X` with the Stage 2 polynomial resolver, as the
  images of a smooth map are, all entries of one frame, its declared inverse
  included, within one `algebraWork` budget. Column `j` becomes column `j` of
  `P`, which is stored as rows.
* A constant frame declares no inverse. Its entries and the whole matrix are
  within the bounds of a Gram matrix (`metricEntryBits`, `metricMatrixBits`),
  checked before the kernel computes the inverse with
  `SmoothDeclarations.invert?`; a singular frame is rejected. The inverse is
  stored as constant polynomials. It never comes from the wire: the wire has
  no field for it, and a declared inverse is rejected.
* A frame polynomial in the point declares `inverse = columns(…)`, of the
  same shape, and `P·Q = I` and `Q·P = I` must hold as identities of
  canonical polynomials.

The pass ends with `FrameDeclarations.checkMatrices`, the check that the
declaration audit (`checkFrame`) repeats, so a frame that the pass accepts
is accepted by the audit. Its rejections are `E_FRAME`, at the declaration,
naming the frame and its object; limits are `E_LIMIT`, and an unknown
coordinate or a zero denominator in an entry is `E_AFFINE_COORDINATE`, as in
the entries of a smooth map or a Gram matrix. Messages name declarations by
their full path, `package::module::name`.

Once the frames are elaborated, the pass gives every frame binding the frames
it names (`elaborateFrameBindings`): the declaration's object, `P` and `Q`,
and for an encoding or a decoding the variance of its fiber family. -/
namespace VastitasKernel.Indexed.Source

open AlgebraRuntime FrameDeclarations

def frameProblem {α : Type} (span : Span) (reason : String) : Namespace.Result α :=
  Namespace.problem span "E_FRAME" reason

private def frameSpan (sources : List (DeclId × Span × Body)) (id : DeclId) : Span :=
  ((sources.find? (·.1 == id)).map (·.2.1)).getD {}

private def frameBody (sources : List (DeclId × Span × Body)) (id : DeclId) : Option Body :=
  (sources.find? (·.1 == id)).map (·.2.2)

/-- The rows of `P` from its `n` columns: the entry in row `i`, column `j` is
entry `i` of column `j`. -/
def rowsOfColumns (n : Nat) (columns : List (List Poly)) : PolyMatrix :=
  (List.range n).map fun i => columns.map fun column => column.getD i []

/-- How a message names a frame and its object. -/
private structure FrameNames where
  frame : String
  object : String
  dimension : Nat

/-- `n` columns of `n` entries: the columns of the frame, or with `inverse`
its declared inverse. -/
private def checkColumns (span : Span) (names : FrameNames) (inverse : Bool)
    (columns : List (List PolyExpr)) : Namespace.Result Unit := do
  let n := names.dimension
  let found? : Option String :=
    if columns.length != n then some s!"{columns.length} columns"
    else (columns.zipIdx.find? (·.1.length != n)).map fun (column, j) =>
      s!"column {j + 1} has {column.length} entries"
  let some found := found? | pure ()
  if inverse then
    frameProblem span <| s!"the declared inverse of the frame `{names.frame}` on the {n}-dimensional object " ++
      s!"`{names.object}` must have the shape of the frame, {n} columns of {n} entries, but {found}"
  else if columns.length != n then
    frameProblem span <| s!"the frame `{names.frame}` on the {n}-dimensional object `{names.object}` needs " ++
      s!"{n} columns, one for each frame vector, but it has {columns.length}"
  else
    frameProblem span <| s!"the frame `{names.frame}` on the {n}-dimensional object `{names.object}` needs " ++
      s!"{n} entries in each column, but {found}"

/-- Expand the entries of `columns` in the object's coordinates, continuing
the work budget after `used` units, and return the rows with the units used. -/
private def expandColumns (span : Span) (names : FrameNames) (coordinates : List String)
    (columns : List (List PolyExpr)) (used : Nat) : Namespace.Result (PolyMatrix × Nat) :=
  let expand : AlgebraBasis.Work (List (List Poly)) :=
    columns.mapM fun (column : List PolyExpr) => column.mapM (·.evaluate coordinates)
  match expand.run used with
  | .error error =>
    Namespace.problem span error.code s!"the frame `{names.frame}` on `{names.object}`: {error.message}"
  | .ok (polys, used) => pure (rowsOfColumns names.dimension polys, used)

/-- The diagnostic of a failure of `checkMatrices`. `declared` tells whether
`Q` is the declared inverse of a polynomial frame or the computed inverse of
a constant frame. -/
private def failureProblem {α : Type} (span : Span) (names : FrameNames) (declared : Bool) :
    Failure → Namespace.Result α
  | .dimension =>
    Namespace.problem span "E_LIMIT" <| s!"the frame `{names.frame}` is on `{names.object}`, which has more " ++
      s!"than {Limits.algebraGenerators} coordinates"
  | .entry i j =>
    Namespace.problem span "E_LIMIT" <| s!"entry {i + 1} of column {j + 1} of the constant frame " ++
      s!"`{names.frame}` on `{names.object}` has more than {Limits.metricEntryBits} bits in its numerator " ++
      "or denominator"
  | .matrix =>
    Namespace.problem span "E_LIMIT" <| s!"the constant frame `{names.frame}` on `{names.object}` exceeds " ++
      "the matrix limit: the product of the norms of its rows, cleared of denominators, and of its largest " ++
      s!"row denominator has more than {Limits.metricMatrixBits} bits"
  | .work error =>
    Namespace.problem span "E_LIMIT" <| s!"checking the declared inverse of the frame `{names.frame}` on " ++
      s!"`{names.object}`: {error.message}"
  | .leftInverse =>
    if declared then
      frameProblem span <| s!"the declared inverse Q of the frame `{names.frame}` on `{names.object}` is " ++
        "not its inverse: P·Q ≠ I, where column j of P is frame vector j"
    else
      frameProblem span s!"the computed inverse of the constant frame `{names.frame}` failed its check: P·Q ≠ I"
  | .rightInverse =>
    if declared then
      frameProblem span <| s!"the declared inverse Q of the frame `{names.frame}` on `{names.object}` is " ++
        "not its inverse: Q·P ≠ I, where column j of P is frame vector j"
    else
      frameProblem span s!"the computed inverse of the constant frame `{names.frame}` failed its check: Q·P ≠ I"
  | .shape _ | .constantInverse =>
    -- Not reached: the pass builds both matrices in canonical form, and a
    -- constant frame gets a constant inverse.
    frameProblem span s!"the elaborated matrices of the frame `{names.frame}` are not well formed"

/-- The matrix `P` and the inverse `Q` of the frame `name`, declared at
`family` on `object`, from its columns (`none` for `coordinates`) and its
declared inverse. -/
def elaborateFrame (span : Span) (env : Environment) (name family object : DeclId)
    (columns declared : Option (List (List PolyExpr))) : Namespace.Result (PolyMatrix × PolyMatrix) := do
  unless isFrameFamily env family do
    frameProblem span <| s!"the frame `{qualified name}` on `{qualified object}` is declared at " ++
      s!"`{qualified family}`, which is not a family with the representation `frame`"
  let some coordinates := smoothCoordinates? env object
    | frameProblem span <| s!"the frame `{qualified name}` is on `{qualified object}`, which is not a smooth " ++
        "object; a frame needs a smooth object declared with `Affine(n)[…]`"
  let names : FrameNames := ⟨qualified name, qualified object, coordinates.length⟩
  let n := names.dimension
  if n > Limits.algebraGenerators then failureProblem span names false .dimension
  unless validApplication env ⟨family, [.object (.global object)]⟩ do
    frameProblem span <| s!"the frame `{names.frame}` is on `{names.object}`, which its family " ++
      s!"`{qualified family}` does not accept"
  let (matrix, used) ← match columns with
    | none => pure (polyIdentity n, 0)
    | some columns => do
      checkColumns span names false columns
      expandColumns span names coordinates columns 0
  if constantMatrix matrix then
    if declared.isSome then
      frameProblem span <| s!"the frame `{names.frame}` on `{names.object}` is constant, so the kernel computes " ++
        "its inverse; a constant frame declares no `inverse = …`"
    let values := FrameDeclarations.values n matrix
    match checkBounds values with
    | .error failure => failureProblem span names false failure
    | .ok () => pure ()
    let some inverse := SmoothDeclarations.invert? n values
      | frameProblem span <| s!"the constant frame `{names.frame}` on `{names.object}` is singular: its " ++
          "columns are not a basis of the tangent fibers"
    let inverse := constants n inverse
    match checkMatrices n matrix inverse with
    | .error failure => failureProblem span names false failure
    | .ok () => pure (matrix, inverse)
  else
    let some declared := declared
      | frameProblem span <| s!"the frame `{names.frame}` on `{names.object}` depends on the point, so it " ++
          "needs its inverse, declared with `inverse = columns(…)`"
    checkColumns span names true declared
    let (inverse, _) ← expandColumns span names coordinates declared used
    match checkMatrices n matrix inverse with
    | .error failure => failureProblem span names true failure
    | .ok () => pure (matrix, inverse)

/-! ## The frames of the frame bindings

`resolveBody` builds every frame binding with placeholder frames, the frame's
own ID as its object and empty matrices (`FrameRef.placeholder`), and
`frame_encode` and `frame_decode` with the variance `tangent`. Once the frame
declarations are elaborated, each frame that a binding names is replaced by
its declaration: its object, its matrix `P` and its inverse `Q`. A name that
is not a frame declaration is `E_FRAME`. The variance of an encoding or a
decoding is that of its fiber family; a fiber family and an array family of
different variances are `E_FRAME`. A transition between frames of two objects
is `E_ENDPOINT`, naming both frames and both objects. A family that is not a
fiber, array, map or smooth family is left to the declaration audit, which
checks every embedded frame against its declaration again
(`IndexedFrameContracts`). -/

private def varianceWord : Variance → String
  | .tangent => "vector"
  | .cotangent => "covector"

/-- The declaration of a frame that a binding names, as an embedded frame. -/
private def bindingFrame (span : Span) (env : Environment) (operation field : String) (frame : DeclId) :
    Namespace.Result FrameRef := do
  let some (_, object, matrix, inverse) := frameData? env frame
    | frameProblem span <| s!"the {field} of `{operation}` must be a frame, but `{qualified frame}` is not a " ++
        "frame declaration"
  pure ⟨frame, object, matrix, inverse⟩

/-- The variance of an encoding or a decoding: that of its fiber family, or
that of its array family when the fiber family is not one. -/
private def bindingVariance (span : Span) (env : Environment) (operation : String) (fiber coords : DeclId) :
    Namespace.Result Variance := do
  match fiberVariance? env fiber, frameFiberVariance? env coords with
  | some variance, some arrays =>
    unless variance == arrays do
      frameProblem span <| s!"`{operation}` relates the {varianceWord variance} family `{qualified fiber}` to " ++
        s!"`{qualified coords}`, which holds the arrays of {varianceWord arrays}s; both families must hold " ++
        "vectors, or both covectors"
    pure variance
  | some variance, none => pure variance
  | none, some arrays => pure arrays
  | none, none => pure .tangent

/-- Give every frame binding the declarations of the frames it names. Every
other binding is unchanged. -/
def elaborateFrameBindings (sources : List (DeclId × Span × Body)) (env : Environment)
    (primitives : List Core.NamedPrimitive) : Namespace.Result (List Core.NamedPrimitive) :=
  primitives.mapM fun entry => do
    let span := frameSpan sources entry.id
    match entry.binding with
    | .frameEncode _ fiber coords frame =>
      let frame ← bindingFrame span env "frame_encode" "frame" frame.frame
      let variance ← bindingVariance span env "frame_encode" fiber coords
      pure ⟨entry.id, .frameEncode variance fiber coords frame⟩
    | .frameDecode _ coords fiber frame =>
      let frame ← bindingFrame span env "frame_decode" "frame" frame.frame
      let variance ← bindingVariance span env "frame_decode" fiber coords
      pure ⟨entry.id, .frameDecode variance coords fiber frame⟩
    | .frameVector coords smooth _ frame =>
      let embedded ← bindingFrame span env "frame_vector" "frame" frame
      pure ⟨entry.id, .frameVector coords smooth embedded.object frame⟩
    | .frameMatrix smooth map source target =>
      let source ← bindingFrame span env "frame_matrix" "source frame" source.frame
      let target ← bindingFrame span env "frame_matrix" "target frame" target.frame
      pure ⟨entry.id, .frameMatrix smooth map source target⟩
    | .frameTransition smooth map source target =>
      let source ← bindingFrame span env "frame_transition" "source frame" source.frame
      let target ← bindingFrame span env "frame_transition" "target frame" target.frame
      unless source.object == target.object do
        Namespace.problem span "E_ENDPOINT" <| s!"`frame_transition` changes between two frames of one object, " ++
          s!"but the source frame `{qualified source.frame}` is on `{qualified source.object}` and the target " ++
          s!"frame `{qualified target.frame}` is on `{qualified target.object}`"
      pure ⟨entry.id, .frameTransition smooth map source target⟩
    | _ => pure entry

/-- Elaborate every frame declaration, then give every frame binding the
frames it names. A program without frame declarations or frame bindings is
unchanged. -/
def elaborateFrames (sources : List (DeclId × Span × Body)) (env : Core.Declarations) :
    Namespace.Result Core.Declarations := do
  let indexed ← env.indexed.mapM fun entry => do
    match entry.declaration, frameBody sources entry.id with
    | .frame family object _ _, some (.frame _ _ columns declared) =>
      let (matrix, inverse) ← elaborateFrame (frameSpan sources entry.id) env.indexed entry.id family object
        columns declared
      pure ⟨entry.id, .frame family object matrix inverse⟩
    | _, _ => pure entry
  let primitives ← elaborateFrameBindings sources indexed env.primitives
  pure { env with indexed, primitives }

end VastitasKernel.Indexed.Source
