import VastitasKernel.FrameRuntime
import VastitasKernel.SmoothDeclarations
import Lean.Data.Json
import VastitasKernel.RegressionSupport

set_option autoImplicit false

/-! Cross-check of the kernel's exact frame runtime (`FrameRuntime`) against the
independent Python reference fixture `tests/fixtures/frames.json`
(`scripts/frame_reference.py`) (Stage 4, #759). These are executable
regressions, not proofs.

The module reads the `encodings`, `transitions`, `matrices` and `grams`
sections. The `frames` and `invalidFrames` sections are the frame declaration
checks' (`VastitasKernel.FrameDeclarationRegression`); this module does not
read them. It takes the frames that the cases name from the table below,
transcribed from the reference model, and checks the transcription at every
point of a case: `P(p) Q(p) = Q(p) P(p) = I`.

The reference covers only the plane: frames of `ℝ²`, maps `ℝ² → ℝ²` and
`2 × 2` Gram matrices. Higher and zero dimensions are checked in
`VastitasKernel.FrameRuntimeRegression`, not here. -/
namespace VastitasAlgebraTest.FrameReferenceRegression

open VastitasKernel VastitasKernel.AlgebraRuntime VastitasKernel.SmoothRuntime
  VastitasKernel.FrameRuntime Lean

private def check := RegressionSupport.check "frame reference regression failed"

/-! ## The frames that the cases name

Each frame is written as in a program, by its columns, with the columns of its
inverse: `B`, `B_PRIME`, `C`, `C_PRIME`, `R` with `R_INVERSE` and `S` with
`S_INVERSE` of `scripts/frame_reference.py`. The inverses of the constant
frames are those the model computes. -/

private def x : Poly := Poly.var 2 0
private def y : Poly := Poly.var 2 1
private def k (value : Rat) : Poly := Poly.const 2 value

/-- `P` as rows from its columns: column `j` of `P` is `columns[j]`. -/
private def rowsOf (columns : List (List Poly)) : List (List Poly) :=
  (List.range columns.length).map fun i => columns.map fun column => column.getD i []

/-- A frame `P` and its inverse `Q`, as rows. -/
private structure Frame where
  matrix : List (List Poly)
  inverse : List (List Poly)

private def frame (columns inverseColumns : List (List Poly)) : Frame :=
  ⟨rowsOf columns, rowsOf inverseColumns⟩

private def frames : List (String × Frame) := [
  ("coordinates", frame [[k 1, k 0], [k 0, k 1]] [[k 1, k 0], [k 0, k 1]]),
  ("b", frame [[k 1, k 0], [k 1, k 2]] [[k 1, k 0], [k (-1/2), k (1/2)]]),
  ("b'", frame [[k 2, k 1], [k (-1), k 3]] [[k (3/7), k (-1/7)], [k (1/7), k (2/7)]]),
  ("c", frame [[k 1, k 1], [k 0, k 3]] [[k 1, k (-1/3)], [k 0, k (1/3)]]),
  ("c'", frame [[k 1, k (-1)], [k 2, k 1]] [[k (1/3), k (1/3)], [k (-2/3), k (1/3)]]),
  ("r", frame [[k 1, k 0], [x, k 2]] [[k 1, k 0], [Poly.scale (-1/2) x, k (1/2)]]),
  ("s", frame [[k 1, y], [k 0, k 1]] [[k 1, Poly.neg y], [k 0, k 1]])]

private def lookupFrame (name : String) : IO Frame :=
  match frames.lookup name with
  | some found => pure found
  | none => throw (IO.userError s!"frame reference regression: no frame {name}")

private def identity2 : Matrix := [[1, 0], [0, 1]]

/-- The transcription of a frame is a two-sided inverse pair at `point`. -/
private def checkFrameAt (label name : String) (point : List Rat) : IO Frame := do
  let found ← lookupFrame name
  let pAt := matrixAt found.matrix point
  let qAt := matrixAt found.inverse point
  check s!"{label}: P Q = Q P = I for the frame {name} at the point"
    (matrixProduct 2 pAt qAt == identity2 && matrixProduct 2 qAt pAt == identity2)
  pure found

/-! ## Reading the fixture -/

private def rational (text : String) : Except String Rat :=
  match text.splitOn "/" with
  | [n] => match n.toInt? with
    | some value => pure value
    | none => throw s!"bad rational {text}"
  | [n, d] => match n.toInt?, d.toNat? with
    | some num, some den => if den == 0 then throw "zero denominator" else pure (mkRat num den)
    | _, _ => throw s!"bad rational {text}"
  | _ => throw s!"bad rational {text}"

private def rationals (json : Json) : Except String (List Rat) := do
  (← json.getArr?).toList.mapM fun value => do rational (← value.getStr?)

private def matrix (json : Json) : Except String Matrix := do
  (← json.getArr?).toList.mapM rationals

private def term (json : Json) : Except String AlgebraRuntime.Term := do
  let #[exponents, coefficient] ← json.getArr? | throw "term must be a pair"
  let exponents ← (← exponents.getArr?).toList.mapM fun e => e.getNat?
  pure ⟨exponents, ← rational (← coefficient.getStr?)⟩

/-- The terms exactly as written; `canonical` checks and normalizes them. -/
private def poly (json : Json) : Except String Poly := do
  (← json.getArr?).toList.mapM term

private def polys (json : Json) : Except String (List Poly) := do
  (← json.getArr?).toList.mapM poly

private def field (json : Json) (key : String) : Except String Json := json.getObjVal? key

private def text (json : Json) (key : String) : Except String String := do (← field json key).getStr?

structure EncodingCase where
  frame : String
  variance : String
  point : List Rat
  components : List Rat
  expected : List Rat

structure TransitionCase where
  source : String
  target : String
  point : List Rat
  expected : Matrix

structure MatrixCase where
  map : String
  images : List Poly
  source : String
  target : String
  point : List Rat
  expected : Matrix

structure GramCase where
  metric : String
  gram : Matrix
  frame : String
  point : List Rat
  expected : Matrix

structure Fixture where
  encodings : List EncodingCase
  transitions : List TransitionCase
  matrices : List MatrixCase
  grams : List GramCase

private def decodeEncoding (json : Json) : Except String EncodingCase := do
  pure {
    frame := ← text json "frame"
    variance := ← text json "variance"
    point := ← rationals (← field json "point")
    components := ← rationals (← field json "components")
    expected := ← rationals (← field json "expected") }

private def decodeTransition (json : Json) : Except String TransitionCase := do
  pure {
    source := ← text json "source"
    target := ← text json "target"
    point := ← rationals (← field json "point")
    expected := ← matrix (← field json "expected") }

private def decodeMatrix (json : Json) : Except String MatrixCase := do
  pure {
    map := ← text json "map"
    images := ← polys (← field json "images")
    source := ← text json "source"
    target := ← text json "target"
    point := ← rationals (← field json "point")
    expected := ← matrix (← field json "expected") }

private def decodeGram (json : Json) : Except String GramCase := do
  pure {
    metric := ← text json "metric"
    gram := ← matrix (← field json "gram")
    frame := ← text json "frame"
    point := ← rationals (← field json "point")
    expected := ← matrix (← field json "expected") }

private def decodeCases {α : Type} (json : Json) (key : String)
    (decode : Json → Except String α) : Except String (List α) := do
  (← (← field json key).getArr?).toList.mapM decode

private def fixture : Except String Fixture := do
  let json ← Json.parse (include_str "../../tests/fixtures/frames.json")
  unless (← text json "order") == "degLex" do throw "unexpected monomial order"
  pure {
    encodings := ← decodeCases json "encodings" decodeEncoding
    transitions := ← decodeCases json "transitions" decodeTransition
    matrices := ← decodeCases json "matrices" decodeMatrix
    grams := ← decodeCases json "grams" decodeGram }

/-- Check that a fixture polynomial is already canonical in arity 2, and return
its `Poly.ofTerms` normalization. -/
private def canonical (label : String) (raw : Poly) : IO Poly := do
  check s!"{label}: fixture polynomial is canonical" (Poly.canonical 2 raw)
  let normalized := Poly.ofTerms raw
  check s!"{label}: normalization leaves the fixture polynomial unchanged" (normalized == raw)
  pure normalized

private def planeMap (label : String) (images : List Poly) : IO Map := do
  let map : Map := ⟨2, [], ← images.mapM (canonical label)⟩
  check s!"{label}: well-formed ℝ² → ℝ² smooth map" (SmoothRuntime.wellFormed 2 2 map)
  check s!"{label}: the declaration check accepts the map" (SmoothDeclarations.checkMap 2 2 map).isOk
  pure map

private def unitVectors : List (List Rat) := [[1, 0], [0, 1]]

/-- The matrix with these columns. -/
private def ofColumns (columns : List (List Rat)) : Matrix :=
  (List.range 2).map fun i => columns.map fun column => column.getD i 0

/-! ## Encodings -/

#eval show IO Unit from do
  let data ← IO.ofExcept fixture
  check "fixture has encoding cases" (data.encodings.length ≥ 24)
  check "fixture encodes vectors and covectors"
    (data.encodings.any (·.variance == "tangent") && data.encodings.any (·.variance == "cotangent"))
  check "fixture encodes in polynomial frames" (data.encodings.any fun c => c.frame == "r" || c.frame == "s")
  for c in data.encodings do
    let label := s!"encoding of a {c.variance} in {c.frame} at {c.point}"
    let found ← checkFrameAt label c.frame c.point
    let value : FiberValue := some ⟨c.point, c.components⟩
    let array : FiberValue := some ⟨c.point, c.expected⟩
    match c.variance with
    | "tangent" =>
      check s!"{label}: encodeTangent agrees with the reference" (encodeTangent found.inverse value == array)
      check s!"{label}: decodeTangent recovers the vector" (decodeTangent found.matrix array == value)
    | "cotangent" =>
      check s!"{label}: encodeCotangent agrees with the reference" (encodeCotangent found.matrix value == array)
      check s!"{label}: decodeCotangent recovers the covector" (decodeCotangent found.inverse array == value)
    | other => throw (IO.userError s!"frame reference regression: unknown variance {other}")

/-! ## Transitions -/

#eval show IO Unit from do
  let data ← IO.ofExcept fixture
  check "fixture has transition cases" (data.transitions.length ≥ 18)
  check "fixture has the identity transition" (data.transitions.any fun c => c.source == c.target)
  for c in data.transitions do
    let label := s!"transition {c.source} → {c.target} at {c.point}"
    let source ← checkFrameAt label c.source c.point
    let target ← checkFrameAt label c.target c.point
    check s!"{label}: transition agrees with the reference"
      (transition (ratPoint c.point) source.matrix target.inverse == some ⟨c.point, c.point, c.expected⟩)

/-! ## Matrices of maps

Each case is one map as a primitive program. The composite case
`square after shear` is also run on the `compose` node of the two programs,
as checked Core builds it. -/

/-- Coapply in frames, decoded, is the pullback of every unit covector at the
image point, in both modes. -/
private def coapplyAgrees (program point : Program) (source target : Frame) (image : List Rat) : Bool :=
  unitVectors.all fun alpha =>
    let covector : FiberValue := some ⟨image, alpha⟩
    let inFrames := decodeCotangent source.inverse
      (coapply (frameMatrix program point source.matrix target.inverse) (encodeCotangent target.matrix covector))
    inFrames == pullback .recomputed program point covector && inFrames == pullback .saved program point covector

#eval show IO Unit from do
  let data ← IO.ofExcept fixture
  check "fixture has matrix cases" (data.matrices.length ≥ 48)
  let imagesOf (name : String) : IO (List Poly) :=
    match data.matrices.find? (·.map == name) with
    | some c => pure c.images
    | none => throw (IO.userError s!"frame reference regression: no map {name}")
  let square ← planeMap "square" (← imagesOf "square")
  let shear ← planeMap "shear" (← imagesOf "shear")
  let node : Program := .compose (.primitive square) (.primitive shear)
  check "the compose node is well typed" (node.wellTyped 2 2)
  let composites := data.matrices.filter (·.map == "square after shear")
  check "fixture has composite cases" (composites.length ≥ 12)
  for c in data.matrices do
    let label := s!"matrix of {c.map} in ({c.source}, {c.target}) at {c.point}"
    let map ← planeMap label c.images
    let image := SmoothRuntime.apply map c.point
    let source ← checkFrameAt label c.source c.point
    let target ← checkFrameAt label c.target image
    let point := ratPoint c.point
    let expected : FrameMatrixValue := some ⟨c.point, image, c.expected⟩
    check s!"{label}: frameMatrix agrees with the reference"
      (frameMatrix (.primitive map) point source.matrix target.inverse == expected)
    check s!"{label}: coapply in frames equals the pullback"
      (coapplyAgrees (.primitive map) point source target image)
    if c.map == "square after shear" then
      check s!"{label}: the compose node denotes the reference composite"
        (SmoothRuntime.same node (.primitive map) && node.eval c.point == image)
      check s!"{label}: frameMatrix on the compose node agrees with the reference"
        (frameMatrix node point source.matrix target.inverse == expected)
      check s!"{label}: coapply in frames on the compose node equals the pullback"
        (coapplyAgrees node point source target image)

/-! ## Gram matrices in a frame

The Gram matrix of a metric `G` in the frame `P` at `p` is computed as a
composite, without a frame-Gram operation: column `j` is
`encodeCotangent (flat G (decodeTangent eⱼ))` for the unit array `eⱼ`. -/

#eval show IO Unit from do
  let data ← IO.ofExcept fixture
  check "fixture has Gram cases" (data.grams.length ≥ 18)
  check "fixture has an indefinite metric" (data.grams.any (·.metric == "lorentz"))
  for c in data.grams do
    let label := s!"Gram of {c.metric} in {c.frame} at {c.point}"
    let found ← checkFrameAt label c.frame c.point
    let columns := unitVectors.map fun unit =>
      encodeCotangent found.matrix (flat c.gram (decodeTangent found.matrix (some ⟨c.point, unit⟩)))
    check s!"{label}: every column lies over the point" (columns.all fun column => fiberAt column (ratPoint c.point))
    let entries := ofColumns (columns.map fun column => (column.map (·.components)).getD [])
    check s!"{label}: encode ∘ flat ∘ decode agrees with the reference" (entries == c.expected)

end VastitasAlgebraTest.FrameReferenceRegression
