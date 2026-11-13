import VastitasKernel.ResourceProtocol
import VastitasKernel.IndexedAcceptance

set_option autoImplicit false

/-! Frame declarations and the frame families (Stage 4, #759; ADR 0001 §11)
through the public wire decoders, the source checker and the declaration
audit. These are executable regressions, not proofs.

Protocol 9 decodes each wire shape of a frame declaration, of a frame family
representation and of a frame parameter; protocols 7 and 8 reject each with
`E_PROTOCOL`. The frame families are data-model rules. The source checker
elaborates every frame: a constant frame gets its inverse from the kernel, a
frame polynomial in the point declares its inverse, and every rule of
`IndexedFrameSource` has its diagnostic. The declaration audit
(`FrameDeclarations.checkFrame`) checks every stored frame again, and rejects
tampered entries. -/
namespace VastitasKernel.Indexed.FrameDeclarationRegression

open Lean AlgebraRuntime

private def check (label : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError s!"frame declaration regression failed: {label}")

/-! ## Wire records -/

private def span : Json := Json.mkObj [
  ("start", toJson (0 : Nat)), ("end", toJson (0 : Nat)), ("line", toJson (1 : Nat)), ("column", toJson (1 : Nat))]
private def pathJson (name : String) : Json := Json.mkObj [("path", toJson [name]), ("span", span)]
private def decl (kind name : String) (fields : List (String × Json)) : Json :=
  Json.mkObj ([("kind", toJson kind), ("name", toJson name), ("public", toJson true), ("span", span)] ++ fields)
private def natural (value : Nat) : Json := Json.mkObj [("op", toJson "natural"), ("value", toJson (toString value))]
private def coordinate (name : String) : Json := Json.mkObj [("op", toJson "coordinate"), ("name", toJson name)]
private def negJson (operand : Json) : Json := Json.mkObj [("op", toJson "neg"), ("operand", operand)]
private def fraction (numerator : Int) (denominator : Nat) : Json := Json.mkObj [("op", toJson "fraction"),
  ("numerator", toJson (toString numerator)), ("denominator", toJson (toString denominator))]
private def productJson (factors : List Json) : Json := Json.mkObj [("op", toJson "product"), ("factors", toJson factors)]
private def objectParameter : Json := Json.mkObj [("kind", toJson "object"), ("domain", pathJson "CInfAffine")]
private def frameParameter (family : String) : Json :=
  Json.mkObj [("kind", toJson "frame"), ("family", pathJson family)]
private def canonical (object : Nat) : Json := Json.mkObj [("kind", toJson "canonical"), ("object", toJson object)]
private def family (name : String) (parameters constraints : List Json) (representation : String) : Json :=
  decl "family" name [("parameters", toJson parameters), ("constraints", toJson constraints),
    ("representation", toJson representation)]

/-- `columns(…)`: the frame vectors, each a list of entries. -/
private def columns (vectors : List (List Json)) : Json :=
  Json.mkObj [("kind", toJson "columns"), ("columns", toJson (vectors.map toJson))]
private def coordinates : Json := Json.mkObj [("kind", toJson "coordinates")]

private def frame (name : String) (columns inverse : Json) (object := "Plane") (fam := "Frame") : Json :=
  decl "frame" name [("family", pathJson fam), ("indices", toJson [pathJson object]),
    ("columns", columns), ("inverse", inverse)]

/-- A constant frame with `P ≠ Pᵀ` and `det P = 2`, a frame polynomial in the
point with its declared inverse, and the coordinate frame. -/
private def constantFrame : Json := frame "b" (columns [[natural 1, natural 0], [natural 1, natural 2]]) .null
private def pointFrame : Json :=
  frame "bx" (columns [[natural 1, natural 0], [coordinate "x", natural 1]])
    (columns [[natural 1, natural 0], [negJson (coordinate "x"), natural 1]])
private def coordinateFrame : Json := frame "e" coordinates .null

private def smoothBase : List Json := [
  decl "marker" "CInfReal" [],
  decl "implementation" "SmoothR" [("marker", pathJson "CInfReal"), ("representation", toJson "smooth_affine"),
    ("capabilities", toJson ([] : List Json))],
  decl "classification" "CInfAffine" [("parents", toJson ([] : List Json)), ("domain", toJson [pathJson "SmoothR"])],
  decl "smooth_affine" "Pt" [("implementation", pathJson "SmoothR"), ("dimension", toJson "0"),
    ("coordinates", toJson ([] : List String))],
  decl "smooth_affine" "Plane" [("implementation", pathJson "SmoothR"), ("dimension", toJson "2"),
    ("coordinates", toJson ["x", "y"])]]

private def frameFamilies : List Json := [
  family "Frame" [objectParameter] [canonical 0] "frame",
  family "Coords" [frameParameter "Frame"] [] "frame_vector",
  family "CoCoords" [frameParameter "Frame"] [] "frame_covector",
  family "FrameMap" [frameParameter "Frame", frameParameter "Frame"] [] "frame_map"]

private def mod (declarations : List Json) : Json := Json.mkObj [
  ("path", toJson ([] : List String)), ("public", toJson true), ("span", span),
  ("imports", toJson ([] : List Json)), ("generics", toJson ([] : List Json)),
  ("methods", toJson ([] : List Json)), ("functions", toJson ([] : List Json)),
  ("indexed_declarations", toJson declarations)]

private def request (version : Nat) (declarations : List Json) : Json := Json.mkObj [
  ("version", toJson version), ("input", toJson "package"), ("file", toJson "frames.vast"),
  ("root", toJson "/frames/Vastitas.toml"),
  ("packages", toJson [Json.mkObj [
    ("source", toJson "/frames/Vastitas.toml"), ("name", toJson "frames"), ("version", toJson "0.1.0"),
    ("dependencies", toJson ([] : List Json)), ("modules", toJson [mod declarations])]])]

/-- The code of a public request, or `accepted`: protocols 8 and 9 through
`ResourceSource.Wire`, protocol 7 through `Indexed.Wire`. -/
private def outcome (version : Nat) (declarations : List Json) : String × String :=
  let json := request version declarations
  let result := if version == 7 then (Indexed.Wire.check json false).map fun _ => ()
    else (ResourceSource.Wire.check json false).map fun _ => ()
  match result with
  | .ok () => ("accepted", "")
  | .error diagnostic => (diagnostic.code, diagnostic.message)

private def mentions (text part : String) : Bool := (text.splitOn part).length > 1

private def decodes (j : Json) (algebraic : Bool) : Bool :=
  (Wire.declarationBody j (numerical := true) (algebraic := algebraic)).isOk

/-- The request of `version` with `declarations` is rejected with `code` and a
message that contains `text`. -/
private def rejectsWith (version : Nat) (declarations : List Json) (code text : String) : Bool :=
  (outcome version declarations).1 == code && mentions (outcome version declarations).2 text

/-- Protocols 7 and 8 reject a request whose one declaration is `j`, with
`E_PROTOCOL` and the protocol-9 message of its decoder. -/
private def rejectedBefore9 (j : Json) : Bool :=
  [7, 8].all fun version => rejectsWith version [j] "E_PROTOCOL" "frame declarations require protocol 9"

/-! ## The frame families are data-model rules -/

#eval check "protocol 9 accepts the frame families"
  ((outcome 9 (smoothBase ++ frameFamilies)).1 == "accepted")
#eval check "protocol 9 accepts a token family with a frame parameter"
  ((outcome 9 (smoothBase ++ frameFamilies ++ [family "Tagged" [frameParameter "Frame"] [] "token"])).1 ==
    "accepted")
#eval check "protocols 7 and 8 reject each frame family representation with E_PROTOCOL"
  (["frame", "frame_vector", "frame_covector", "frame_map"].all fun representation =>
    rejectedBefore9 (family "F" [] [] representation))
#eval check "protocols 7 and 8 reject a frame parameter with E_PROTOCOL"
  (rejectedBefore9 (family "Tagged" [frameParameter "Frame"] [] "token"))

private def rejectsFamily (families : List Json) (text : String) : Bool :=
  rejectsWith 9 (smoothBase ++ families) "E_TYPE" text

#eval check "a frame family has one object parameter and the constraint canonical(0)"
  (rejectsFamily [family "Frame" [objectParameter, objectParameter] [canonical 0] "frame"]
      "exactly one parameter, of the form `object(…)`" &&
    rejectsFamily [family "Frame" [objectParameter] [] "frame"] "exactly the constraint `canonical(0)`")
#eval check "a frame-array family has one frame parameter and no constraint"
  (rejectsFamily [family "Frame" [objectParameter] [canonical 0] "frame",
      family "Coords" [objectParameter] [canonical 0] "frame_vector"] "exactly one parameter, of the form `frame(…)`" &&
    rejectsFamily [family "Frame" [objectParameter] [canonical 0] "frame",
      family "Coords" [frameParameter "Frame", frameParameter "Frame"] [] "frame_covector"]
      "exactly one parameter, of the form `frame(…)`")
#eval check "a frame-map family has two frame parameters and no constraint"
  (rejectsFamily [family "Frame" [objectParameter] [canonical 0] "frame",
      family "FrameMap" [frameParameter "Frame"] [] "frame_map"] "exactly two parameters, both `frame(…)`")
#eval check "a frame parameter names a frame family"
  (rejectsFamily [family "Frame" [objectParameter] [canonical 0] "frame",
      family "Other" [objectParameter] [canonical 0] "metric_form",
      family "Coords" [frameParameter "Other"] [] "frame_vector"]
      "must name a family with the representation `frame`")

/-! ## Frame declarations on the wire: protocol 9 only -/

/-- Each frame declaration shape, with the name it declares. -/
private def frames : List (String × Json) :=
  [("b", constantFrame), ("bx", pointFrame), ("e", coordinateFrame)]

#eval check "protocol 9 decodes each frame declaration shape"
  (frames.all fun (_, j) => decodes j true)
#eval check "protocols 7 and 8 do not decode a frame declaration"
  (frames.all fun (_, j) => !decodes j false)
#eval check "protocols 7 and 8 reject each frame declaration with E_PROTOCOL"
  (frames.all fun (_, j) => rejectedBefore9 j)
#eval check "the public checker accepts each frame declaration shape, alone and together"
  (frames.all (fun (_, j) => (outcome 9 (smoothBase ++ frameFamilies ++ [j])).1 == "accepted") &&
    (outcome 9 (smoothBase ++ frameFamilies ++ frames.map (·.2))).1 == "accepted")
#eval check "a frame names one object"
  (rejectsWith 9 (smoothBase ++ frameFamilies ++
      [decl "frame" "b" [("family", pathJson "Frame"), ("indices", toJson [pathJson "Plane", pathJson "Pt"]),
        ("columns", coordinates), ("inverse", .null)]])
    "E_FRAME" "a frame names one object, as in `Frame<X>`, but 2 are given")

#eval check "a frame declaration takes exactly its fields"
  (!decodes (Json.mkObj ((constantFrame.getObj?.toOption.getD {}).toArray.toList ++ [("matrix", toJson ([] : List Json))]))
      true &&
    !decodes (decl "frame" "b" [("family", pathJson "Frame"), ("indices", toJson [pathJson "Plane"]),
      ("columns", coordinates)]) true &&
    !decodes (frame "b" (Json.mkObj [("kind", toJson "coordinates"), ("columns", toJson ([] : List Json))]) .null)
      true &&
    !decodes (frame "b" (Json.mkObj [("kind", toJson "rows"), ("columns", toJson ([] : List Json))]) .null) true &&
    !decodes (frame "b" coordinates coordinates) true &&
    !decodes (frame "b" coordinates (Json.mkObj [("kind", toJson "columns"), ("columns", toJson ([] : List Json)),
      ("certificate", toJson true)])) true)

/-! The inverse of a constant frame never comes from the wire: the decoder
has no field for a computed inverse, and the one `inverse` field, which a
frame polynomial in the point fills, is rejected on a constant frame. The
inverse here is the correct one, `P⁻¹` of `b`. -/
#eval check "a wire inverse on a constant frame is E_FRAME, even when it is the correct inverse"
  (rejectsWith 9 (smoothBase ++ frameFamilies ++ [frame "b" (columns [[natural 1, natural 0], [natural 1, natural 2]])
      (columns [[natural 1, natural 0], [fraction (-1) 2, fraction 1 2]])]) "E_FRAME"
      "the frame `frames::b` on `frames::Plane` is constant, so the kernel computes its inverse" &&
    rejectsWith 9 (smoothBase ++ frameFamilies ++ [frame "e" coordinates
      (columns [[natural 1, natural 0], [natural 0, natural 1]])]) "E_FRAME"
      "the frame `frames::e` on `frames::Plane` is constant, so the kernel computes its inverse")
#eval check "a wrong declared inverse on the wire is E_FRAME"
  (rejectsWith 9 (smoothBase ++ frameFamilies ++ [frame "bx" (columns [[natural 1, natural 0], [coordinate "x", natural 1]])
      (columns [[natural 1, natural 0], [coordinate "x", natural 1]])]) "E_FRAME" "P·Q ≠ I")
#eval check "the wire frame polynomial in the point takes a product in its inverse"
  ((outcome 9 (smoothBase ++ frameFamilies ++ [frame "r" (columns [[natural 1, natural 0], [coordinate "x", natural 2]])
      (columns [[natural 1, natural 0], [productJson [fraction (-1) 2, coordinate "x"], fraction 1 2]])])).1 ==
    "accepted")

/-! ## Frames through the source checker -/

private def pkg : Namespace.PackageId := ⟨"/frames/Vastitas.toml", "frames", "0.1.0"⟩
private def id (name : String) : DeclId := ⟨⟨pkg, []⟩, name⟩
private def path (name : String) : Source.Path := ⟨[name], {}⟩
private def sdecl (name : String) (body : Source.Body) : Source.Declaration := ⟨name, body, true, {}⟩
private def n (value : Nat) : Source.PolyExpr := .natural value
private def c (name : String) : Source.PolyExpr := .coordinate name
private def neg (e : Source.PolyExpr) : Source.PolyExpr := .neg e
private def frac (numerator : Int) (denominator : Nat) : Source.PolyExpr := .fraction numerator denominator

private def space (name : String) (coordinates : List String) : Source.Declaration :=
  sdecl name (.smoothAffine (path "SmoothR") coordinates.length coordinates)

/-- `indexed frame name: family<object> = columns(…) [inverse = columns(…)]`,
or `= coordinates` for `none`. -/
private def frameDecl (name : String) (columns : Option (List (List Source.PolyExpr)))
    (inverse : Option (List (List Source.PolyExpr)) := none) (object := "Plane") (family := "Frame") :
    Source.Declaration :=
  sdecl name (.frame (path family) [path object] columns inverse)

/-- Smooth objects of dimension 0, 1 and 2, the frame family, a family of
another representation, and a presented object for contrast. -/
private def base : List Source.Declaration := [
  sdecl "CInfReal" .marker,
  sdecl "SmoothR" (.implementation (path "CInfReal") .smoothAffine []),
  sdecl "CInfAffine" (.classification [] [path "SmoothR"]),
  sdecl "Frame" (.family ⟨[.object (path "CInfAffine")], [.canonical 0], .frame⟩),
  sdecl "MetricForm" (.family ⟨[.object (path "CInfAffine")], [.canonical 0], .metricForm⟩),
  space "Pt" [],
  space "Line" ["t"],
  space "Plane" ["x", "y"],
  sdecl "QQ" .marker,
  sdecl "AffineQQ" (.implementation (path "QQ") (.presentedAffine .rational) []),
  sdecl "SpecQQ" (.affine (path "AffineQQ") [] [] none []),
  sdecl "QLine" (.affine (path "AffineQQ") ["t"] [] (some (path "SpecQQ")) []) ]

/-- The frames of the reference model (`frames()` in
`scripts/frame_reference.py`, branch `claude/stage4-reference`), by the
columns it declares them with. Source names cannot contain `'`, so `b'` and
`c'` are `b_prime` and `c_prime`; the fixture's `coordinates` frame, written
with explicit columns, is `coordinate_frame`, and `e` is the `coordinates`
form. -/
private def referenceFrames : List Source.Declaration := [
  frameDecl "coordinate_frame" (some [[n 1, n 0], [n 0, n 1]]),
  frameDecl "b" (some [[n 1, n 0], [n 1, n 2]]),
  frameDecl "b_prime" (some [[n 2, n 1], [neg (n 1), n 3]]),
  frameDecl "c" (some [[n 1, n 1], [n 0, n 3]]),
  frameDecl "c_prime" (some [[n 1, neg (n 1)], [n 2, n 1]]),
  frameDecl "r" (some [[n 1, n 0], [c "x", n 2]]) (some [[n 1, n 0], [.product [frac (-1) 2, c "x"], frac 1 2]]),
  frameDecl "s" (some [[n 1, c "y"], [n 0, n 1]]) (some [[n 1, neg (c "y")], [n 0, n 1]]),
  frameDecl "e" none,
  -- Dimension 0: `columns()` and `coordinates`; dimension 1.
  frameDecl "point_frame" (some []) (object := "Pt"),
  frameDecl "point_coordinates" none (object := "Pt"),
  frameDecl "line_frame" (some [[n 3]]) (object := "Line") ]

private def declarations : List Source.Declaration := base ++ referenceFrames

private def program (ds := declarations) : Source.Program := {
  file := "frames", root := pkg.source,
  packages := [⟨pkg, [], [{
    module := {path := [], isPublic := true, imports := [], functions := [], generics := [], methods := [], span := {}}
    declarations := ds }], none⟩] }

private def with' (extra : List Source.Declaration) : Source.Program := program (declarations ++ extra)

private def code (p : Source.Program) : String :=
  match Source.checkDeclarations p with
  | .ok _ => "accepted"
  | .error e => e.code

private def message (p : Source.Program) : String :=
  match Source.checkDeclarations p with
  | .ok _ => ""
  | .error e => e.message

/-- `p` is rejected with `expected` and a message that contains `text`. -/
private def rejects (p : Source.Program) (expected text : String) : Bool :=
  code p == expected && mentions (message p) text

private def resolvedOf (p : Source.Program) : Option Core.Declarations :=
  match Source.checkDeclarations p with
  | .ok checked => some checked.resolved.declarations
  | .error _ => none

private def resolved : Option Core.Declarations := resolvedOf program

private def lookupIn (name : String) : Option Indexed.Declaration := resolved.bind (lookup ·.indexed (id name))

private def q (numerator : Int) (denominator : Nat := 1) : Rat := mkRat numerator denominator
/-- A polynomial in `(x, y)` from its terms, `(exponents, coefficient)`, as
`tests/fixtures/frames.json` writes them. -/
private def p2 (terms : List (List Nat × Rat)) : Poly := terms.map fun (m, value) => ⟨m, value⟩
/-- The constant `numerator / denominator` in `(x, y)`. -/
private def k (numerator : Int) (denominator : Nat := 1) : Poly := p2 [([0, 0], q numerator denominator)]
private def z : Poly := []

/-- The `rows` and `inverse` of each frame of the `frames` section of
`tests/fixtures/frames.json` (branch `claude/stage4-reference`, written by
`scripts/frame_reference.py`), transcribed by hand: the fixture name, the
source name, `P` as rows and `Q` as rows. The fixture records the columns
too; a transposing reader fails on `b`, `c`, `r` and `s`, whose `P` is not
symmetric. -/
private def expected : List (String × String × PolyMatrix × PolyMatrix) := [
  ("coordinates", "coordinate_frame", [[k 1, z], [z, k 1]], [[k 1, z], [z, k 1]]),
  ("b", "b", [[k 1, k 1], [z, k 2]], [[k 1, k (-1) 2], [z, k 1 2]]),
  ("b'", "b_prime", [[k 2, k (-1)], [k 1, k 3]], [[k 3 7, k 1 7], [k (-1) 7, k 2 7]]),
  ("c", "c", [[k 1, z], [k 1, k 3]], [[k 1, z], [k (-1) 3, k 1 3]]),
  ("c'", "c_prime", [[k 1, k 2], [k (-1), k 1]], [[k 1 3, k (-2) 3], [k 1 3, k 1 3]]),
  ("r", "r", [[k 1, p2 [([1, 0], 1)]], [z, k 2]], [[k 1, p2 [([1, 0], q (-1) 2)]], [z, k 1 2]]),
  ("s", "s", [[k 1, z], [p2 [([0, 1], 1)], k 1]], [[k 1, z], [p2 [([0, 1], -1)], k 1]])]

#eval check "the source checker accepts the reference frames and the frames of dimension 0 and 1"
  (code program == "accepted")
#eval check "declaration order independent" (code (program declarations.reverse) == "accepted")
#eval check "each reference frame stores P as rows and its inverse, as the fixture records them"
  (expected.all fun (_, name, rows, inverse) =>
    lookupIn name == some (.frame (id "Frame") (id "Plane") rows inverse))
#eval check "coordinates is the identity, with the identity as its inverse"
  (lookupIn "e" == some (.frame (id "Frame") (id "Plane") [[k 1, z], [z, k 1]] [[k 1, z], [z, k 1]]))
#eval check "Frame<Pt> = columns() and Frame<Pt> = coordinates are the empty frame"
  (lookupIn "point_frame" == some (.frame (id "Frame") (id "Pt") [] []) &&
    lookupIn "point_coordinates" == some (.frame (id "Frame") (id "Pt") [] []))
#eval check "a frame of a line has polynomials of arity 1"
  (lookupIn "line_frame" ==
    some (.frame (id "Frame") (id "Line") [[Poly.const 1 3]] [[Poly.const 1 (q 1 3)]]))
#eval check "the checked environment holds every frame and passes the declaration audit"
  (resolved.any fun env => validEnvironment env.indexed &&
    (referenceFrames.all fun d => (frameData? env.indexed (id d.name)).isSome))

/-! ### The invalid frames of the reference model

The `invalidFrames` section of `tests/fixtures/frames.json` records each
case with the model's reason; each is `E_FRAME` here, with its own message. -/

/-- The fixture's case name, its reason, the frame and the expected message. -/
private def invalidFrames : List (String × String × Source.Declaration × String) := [
  ("singular constant frame", "SINGULAR", frameDecl "bad" (some [[n 1, n 2], [n 2, n 4]]),
    "the constant frame `frames::bad` on `frames::Plane` is singular"),
  ("inverse declared for a constant frame", "INVERSE_OF_CONSTANT",
    frameDecl "bad" (some [[n 1, n 0], [n 1, n 2]]) (some [[n 1, n 0], [frac (-1) 2, frac 1 2]]),
    "the frame `frames::bad` on `frames::Plane` is constant, so the kernel computes its inverse"),
  ("polynomial frame without an inverse", "MISSING_INVERSE", frameDecl "bad" (some [[n 1, n 0], [c "x", n 2]]),
    "the frame `frames::bad` on `frames::Plane` depends on the point, so it needs its inverse"),
  ("wrong polynomial inverse", "WRONG_INVERSE",
    frameDecl "bad" (some [[n 1, n 0], [c "x", n 2]]) (some [[n 1, n 0], [.product [frac 1 2, c "x"], frac 1 2]]),
    "the declared inverse Q of the frame `frames::bad` on `frames::Plane` is not its inverse: P·Q ≠ I"),
  ("singular at the origin", "WRONG_INVERSE",
    frameDecl "bad" (some [[c "x", n 0], [n 0, n 1]]) (some [[n 1, n 0], [n 0, n 1]]),
    "the declared inverse Q of the frame `frames::bad` on `frames::Plane` is not its inverse: P·Q ≠ I"),
  ("wrong number of entries", "WRONG_SIZE", frameDecl "bad" (some [[n 1, n 0], [n 1]]),
    "the frame `frames::bad` on the 2-dimensional object `frames::Plane` needs 2 entries in each column, " ++
      "but column 2 has 1 entries") ]

#eval check "every invalid frame of the reference model is E_FRAME with its own message"
  (invalidFrames.all fun (_, _, d, text) => rejects (with' [d]) "E_FRAME" text)
#eval check "the messages of the invalid frames are distinct, except the two wrong inverses"
  ((invalidFrames.map fun (_, _, d, _) => message (with' [d])).eraseDups.length == invalidFrames.length - 1)
#eval check "columns((x, 0), (0, 1)) is not a frame, with or without a declared inverse"
  (rejects (with' [frameDecl "bad" (some [[c "x", n 0], [n 0, n 1]])]) "E_FRAME" "depends on the point" &&
    rejects (with' [frameDecl "bad" (some [[c "x", n 0], [n 0, n 1]]) (some [[n 0, n 0], [n 0, n 1]])])
      "E_FRAME" "P·Q ≠ I")

/-! ### The other rules -/

#eval check "a wrong number of columns is E_FRAME"
  (rejects (with' [frameDecl "bad" (some [[n 1, n 0]])]) "E_FRAME"
      "the frame `frames::bad` on the 2-dimensional object `frames::Plane` needs 2 columns, one for each frame vector, but it has 1" &&
    rejects (with' [frameDecl "bad" (some [[n 1, n 0], [n 0, n 1], [n 1, n 1]])]) "E_FRAME" "but it has 3" &&
    rejects (with' [frameDecl "bad" (some [[n 1]]) (object := "Pt")]) "E_FRAME"
      "the frame `frames::bad` on the 0-dimensional object `frames::Pt` needs 0 columns" &&
    rejects (with' [frameDecl "bad" (some []) (object := "Line")]) "E_FRAME" "needs 1 columns")
#eval check "a column of the wrong length is E_FRAME"
  (rejects (with' [frameDecl "bad" (some [[n 1, n 0, n 0], [n 0, n 1]])]) "E_FRAME" "but column 1 has 3 entries" &&
    rejects (with' [frameDecl "bad" (some [[]]) (object := "Line")]) "E_FRAME" "but column 1 has 0 entries")
#eval check "a declared inverse of the wrong shape is E_FRAME"
  (rejects (with' [frameDecl "bad" (some [[n 1, n 0], [c "x", n 2]]) (some [[n 1, n 0]])]) "E_FRAME"
      ("the declared inverse of the frame `frames::bad` on the 2-dimensional object `frames::Plane` must have " ++
        "the shape of the frame, 2 columns of 2 entries, but 1 columns") &&
    rejects (with' [frameDecl "bad" (some [[n 1, n 0], [c "x", n 2]]) (some [[n 1, n 0], [n 0, n 1, n 0]])])
      "E_FRAME" "must have the shape of the frame, 2 columns of 2 entries, but column 2 has 3 entries")
#eval check "a frame at a family of another representation is E_FRAME"
  (rejects (with' [frameDecl "bad" none (family := "MetricForm")]) "E_FRAME"
      ("the frame `frames::bad` on `frames::Plane` is declared at `frames::MetricForm`, which is not a family " ++
        "with the representation `frame`") &&
    rejects (with' [frameDecl "bad" none (family := "Plane")]) "E_FRAME" "is declared at `frames::Plane`")
#eval check "a frame of an object that is not a smooth affine object is E_FRAME"
  (rejects (with' [frameDecl "bad" (some [[n 1]]) (object := "QLine")]) "E_FRAME"
      ("the frame `frames::bad` is on `frames::QLine`, which is not a smooth object; a frame needs a smooth " ++
        "object declared with `Affine(n)[…]`") &&
    rejects (with' [frameDecl "bad" none (object := "CInfAffine")]) "E_FRAME"
      "the frame `frames::bad` is on `frames::CInfAffine`, which is not a smooth object")
#eval check "a frame of a smooth object outside its family's domain is E_FRAME"
  (rejects (with' [sdecl "SmoothS" (.implementation (path "CInfReal") .smoothAffine []),
      sdecl "OtherAffine" (.classification [] [path "SmoothS"]),
      sdecl "OtherFrame" (.family ⟨[.object (path "OtherAffine")], [.canonical 0], .frame⟩),
      frameDecl "bad" none (family := "OtherFrame")]) "E_FRAME"
    "the frame `frames::bad` is on `frames::Plane`, which its family `frames::OtherFrame` does not accept")
#eval check "an unknown coordinate or a zero denominator in an entry is E_AFFINE_COORDINATE, naming the frame"
  (rejects (with' [frameDecl "bad" (some [[c "z", n 0], [n 0, n 1]])]) "E_AFFINE_COORDINATE"
      "the frame `frames::bad` on `frames::Plane`: unknown coordinate z" &&
    rejects (with' [frameDecl "bad" (some [[c "x", n 0], [n 0, n 1]]) (some [[n 1, n 0], [n 0, c "t"]])])
      "E_AFFINE_COORDINATE" "unknown coordinate t" &&
    rejects (with' [frameDecl "bad" (some [[frac 1 0, n 0], [n 0, n 1]])]) "E_AFFINE_COORDINATE"
      "a fraction has a zero denominator")
#eval check "a constant expression in the coordinates is constant"
  (code (with' [frameDecl "zero" (some [[.sum [c "x", neg (c "x"), n 1], n 0], [n 0, n 1]])]) == "accepted" &&
    rejects (with' [frameDecl "bad" (some [[.sum [c "x", neg (c "x"), n 1], n 0], [n 0, n 1]])
      (some [[n 1, n 0], [n 0, n 1]])]) "E_FRAME" "is constant")
#eval check "a frame whose determinant is a constant other than 1 is accepted with its declared inverse"
  (code (with' [frameDecl "shear" (some [[n 2, n 0], [.pow (c "x") 3, n 3]])
      (some [[frac 1 2, n 0], [.product [frac (-1) 6, .pow (c "x") 3], frac 1 3]])]) == "accepted")

/-! ### Limits

A constant frame has the entry and matrix bounds of a Gram matrix, checked
before its inverse is computed. The entries of every frame have the bounds
of Stage 2 polynomial syntax, and the identities of a polynomial frame are
checked within the algebra work and term limits. -/

/-- `2^512 = ((2^16)^16)^2`. -/
private def power512 : Source.PolyExpr := .pow (.pow (.pow (n 2) 16) 16) 2

#eval check "an entry of a constant frame beyond 2^512 is E_LIMIT, at the edge it is accepted"
  (rejects (with' [frameDecl "bad" (some [[power512, n 0], [n 0, n 1]])]) "E_LIMIT"
      s!"entry 1 of column 1 of the constant frame `frames::bad` on `frames::Plane` has more than {Limits.metricEntryBits} bits" &&
    rejects (with' [frameDecl "bad" (some [[n 1, n 0], [power512, n 1]])]) "E_LIMIT"
      "entry 1 of column 2 of the constant frame" &&
    code (with' [frameDecl "edge" (some [[.sum [power512, neg (n 1)], n 0], [n 0, n 1]])]) == "accepted")
#eval check "a singular constant frame beyond the entry bound is E_LIMIT, not E_FRAME"
  (rejects (with' [frameDecl "bad" (some [[power512, n 0], [n 0, n 0]])]) "E_LIMIT" "has more than" &&
    rejects (with' [frameDecl "bad" (some [[n 2, n 0], [n 0, n 0]])]) "E_FRAME" "is singular")
#eval check "an entry beyond the polynomial limits is E_LIMIT, naming the frame"
  (rejects (with' [frameDecl "bad" (some [[.pow (c "x") (Limits.algebraDegree + 1), n 0], [n 0, n 1]])])
    "E_LIMIT" "the frame `frames::bad` on `frames::Plane`: algebraic degree limit exceeded")

/-- The smooth object `Affine(16)[c0, …, c15]`. -/
private def bigSpace : Source.Declaration := space "Big" ((List.range 16).map fun i => s!"c{i}")

/-- The entries, as numerator and denominator, of a dense 16 × 16 matrix with
pairwise distinct denominators, as in the metric regression: the entry in
row `i` and column `j ≥ i` has the denominator `d = base + 2 (16 i + j) + 1`,
and is `(9 d + 1) / d` on the diagonal and `1 / d` elsewhere, so the matrix is
diagonally dominant. With `singular`, row and column 15 repeat row and
column 0. The matrix is symmetric, so its columns are its rows. -/
private def distinctEntries (base : Nat) (singular : Bool) : List (List (Nat × Nat)) :=
  let fold := fun i => if singular && i == 15 then 0 else i
  (List.range 16).map fun i => (List.range 16).map fun j =>
    let low := min (fold i) (fold j)
    let high := max (fold i) (fold j)
    let d := base + 2 * (16 * low + high) + 1
    (if low == high then 9 * d + 1 else 1, d)

private def distinctFrame (name : String) (base : Nat) (singular := false) : Source.Declaration :=
  frameDecl name (some ((distinctEntries base singular).map (·.map fun (a, d) => frac (Int.ofNat a) d)))
    (object := "Big")

#eval check "a dense constant frame with distinct 3-digit denominators gets its inverse"
  (match resolvedOf (with' [bigSpace, distinctFrame "dense" 100]) with
    | some env => match lookup env.indexed (id "dense") with
      | some (.frame _ _ matrix inverse) =>
        matrix.length == 16 && inverse.length == 16 &&
          (FrameDeclarations.checkMatrices 16 matrix inverse).isOk
      | _ => false
    | none => false)
#eval check "a dense constant frame with distinct 63-digit denominators is E_LIMIT, also when singular"
  (rejects (with' [bigSpace, distinctFrame "dense" (10 ^ 62)]) "E_LIMIT"
      ("the constant frame `frames::dense` on `frames::Big` exceeds the matrix limit: the product of the norms " ++
        s!"of its rows, cleared of denominators, and of its largest row denominator has more than {Limits.metricMatrixBits} bits") &&
    rejects (with' [bigSpace, distinctFrame "dense" (10 ^ 62) true]) "E_LIMIT" "exceeds the matrix limit" &&
    rejects (with' [bigSpace, distinctFrame "dense" 100 true]) "E_FRAME" "is singular")

/-- `columns` of `dimension` unit vectors, with `entries` placed at
`(row, column)`. -/
private def unitColumns (dimension : Nat) (entries : List ((Nat × Nat) × Source.PolyExpr)) :
    List (List Source.PolyExpr) :=
  (List.range dimension).map fun j => (List.range dimension).map fun i =>
    match entries.find? (·.1 == (i, j)) with
    | some (_, e) => e
    | none => n (if i == j then 1 else 0)

/-- `(x + y + 1)^16`: 153 terms of degree at most 16. -/
private def dense16 : Source.PolyExpr := .pow (.sum [c "x", c "y", n 1]) 16

/-- `K (c0 + … + c11 + 1)^3` with `K = (10^63 + 7) / (10^63 + 9)`: 455 terms,
each of weight 7 in the work measure, so one product of two of them costs
more than the whole `algebraWork` budget. -/
private def heavy : Source.PolyExpr :=
  .product [frac (Int.ofNat (10 ^ 63 + 7)) (10 ^ 63 + 9), .pow (.sum ((List.range 12).map (fun i => c s!"c{i}") ++ [n 1])) 3]

#eval check "the identities of a polynomial frame beyond the term limit are E_LIMIT, before the comparison"
  -- `P = [[1, f], [0, 1]]` and `Q = [[1, 0], [0, f]]`: `P·Q` needs `f·f`, of 561 terms.
  (rejects (with' [frameDecl "bad" (some (unitColumns 2 [((0, 1), dense16)]))
      (some (unitColumns 2 [((1, 1), dense16)]))]) "E_LIMIT"
    "checking the declared inverse of the frame `frames::bad` on `frames::Plane`: algebraic term limit exceeded")
#eval check "the identities of a polynomial frame beyond the work budget are E_LIMIT, before the comparison"
  (rejects (with' [bigSpace, frameDecl "bad" (some (unitColumns 16 [((0, 1), heavy)]))
      (some (unitColumns 16 [((1, 1), heavy)])) (object := "Big")]) "E_LIMIT"
    "checking the declared inverse of the frame `frames::bad` on `frames::Big`: algebraic work limit exceeded")
#eval check "a polynomial frame with large entries and a cheap identity is accepted"
  -- `P = [[1, f], [0, 1]]` and `Q = [[1, -f], [0, 1]]` multiply `f` only by constants.
  (code (with' [frameDecl "unipotent" (some (unitColumns 2 [((0, 1), dense16)]))
      (some (unitColumns 2 [((0, 1), neg dense16)]))]) == "accepted")

/-! ## The declaration audit

`checkFrame` reads only the declaration, its family and its object. A
tampered entry fails the audit; so does every stored shape that the source
checker cannot produce. -/

private def env : Indexed.Environment := (resolved.map (·.indexed)).getD []

/-- `env` with the declaration of `name` replaced. -/
private def tampered (name : String) (declaration : Indexed.Declaration) : Indexed.Environment :=
  env.map fun entry => if entry.id == id name then ⟨entry.id, declaration⟩ else entry

/-- The audit of `env` with the declaration of `name` replaced: the entry
check and the whole environment. -/
private def audits (name : String) (declaration : Indexed.Declaration) : Bool :=
  let changed := tampered name declaration
  validEntry changed (classRanks changed) ⟨id name, declaration⟩ && validEnvironment changed

private def bRows : PolyMatrix := [[k 1, k 1], [z, k 2]]
private def bInverse : PolyMatrix := [[k 1, k (-1) 2], [z, k 1 2]]
private def rRows : PolyMatrix := [[k 1, p2 [([1, 0], 1)]], [z, k 2]]
private def rInverse : PolyMatrix := [[k 1, p2 [([1, 0], q (-1) 2)]], [z, k 1 2]]
private def onPlane (matrix inverse : PolyMatrix) : Indexed.Declaration := .frame (id "Frame") (id "Plane") matrix inverse

#eval check "the audit accepts the stored frames as they are" (validEnvironment env &&
  audits "b" (onPlane bRows bInverse) && audits "r" (onPlane rRows rInverse))
#eval check "the audit rejects a wrong stored inverse of a constant frame"
  (!audits "b" (onPlane bRows bRows) &&
    -- The inverse as columns instead of rows.
    !audits "b" (onPlane bRows [[k 1, z], [k (-1) 2, k 1 2]]) &&
    !audits "b" (onPlane bRows [[k 1, k (-1) 2], [z, k 1 3]]) &&
    -- A constant `P` with a `Q` that is not constant.
    !audits "b" (onPlane bRows rInverse))
#eval check "the audit rejects a wrong stored inverse of a polynomial frame"
  (!audits "r" (onPlane rRows [[k 1, p2 [([1, 0], q 1 2)]], [z, k 1 2]]) &&
    !audits "r" (onPlane rRows bInverse) && !audits "r" (onPlane rRows rRows))
#eval check "the audit rejects a frame that is not two square canonical matrices of the object's arity"
  (!audits "b" (onPlane [[k 1, k 1]] bInverse) && !audits "b" (onPlane bRows [[k 1, k (-1) 2]]) &&
    !audits "b" (onPlane [[k 1, k 1, z], [z, k 2, z]] bInverse) &&
    -- A zero coefficient, the wrong arity, and two terms out of order.
    !audits "b" (onPlane [[k 1, k 1], [p2 [([0, 0], 0)], k 2]] bInverse) &&
    !audits "b" (onPlane [[[⟨[0], 1⟩], k 1], [z, k 2]] bInverse) &&
    !audits "r" (onPlane [[k 1, p2 [([0, 0], 1), ([1, 0], 1)]], [z, k 2]] rInverse))
#eval check "the audit rejects a frame of another object, family or dimension"
  (!audits "b" (.frame (id "Frame") (id "QLine") bRows bInverse) &&
    !audits "b" (.frame (id "Frame") (id "CInfAffine") bRows bInverse) &&
    !audits "b" (.frame (id "MetricForm") (id "Plane") bRows bInverse) &&
    !audits "b" (.frame (id "Frame") (id "Line") bRows bInverse) &&
    !audits "point_frame" (.frame (id "Frame") (id "Pt") [[k 1]] [[k 1]]) &&
    audits "point_frame" (.frame (id "Frame") (id "Pt") [] []))
#eval check "the audit checks the entry bound of a constant frame, and accepts the edge"
  (let big : Rat := q (Int.ofNat (2 ^ 512))
   let edge : Rat := q (Int.ofNat (2 ^ 512 - 1))
   !audits "b" (onPlane [[p2 [([0, 0], big)], z], [z, k 1]] [[p2 [([0, 0], big⁻¹)], z], [z, k 1]]) &&
    audits "b" (onPlane [[p2 [([0, 0], edge)], z], [z, k 1]] [[p2 [([0, 0], edge⁻¹)], z], [z, k 1]]))
#eval check "the declaration audit rejects a frame entry without its family and object"
  (!validEntry [] [] ⟨id "b", .frame (id "b") (id "b") [] []⟩ &&
    !validEnvironment [⟨id "b", .frame (id "b") (id "b") [] []⟩])

/-! ## `checkMatrices`

Each failure of the check that the audit and the source checker share. `P·Q =
I` implies `Q·P = I` for square matrices over a commutative ring, so
`rightInverse` is not reached for matrices that pass the shape check; both
identities are checked all the same. -/

/-- The failure of a check, or `none` when it passes. -/
private def failure? (result : Except FrameDeclarations.Failure Unit) : Option FrameDeclarations.Failure :=
  match result with
  | .error failure => some failure
  | .ok () => none

#eval check "checkMatrices names each failure"
  (failure? (FrameDeclarations.checkMatrices (Limits.algebraGenerators + 1) [] []) == some .dimension &&
    failure? (FrameDeclarations.checkMatrices 2 [[k 1, k 1]] bInverse) == some (.shape false) &&
    failure? (FrameDeclarations.checkMatrices 2 bRows [[k 1]]) == some (.shape true) &&
    failure? (FrameDeclarations.checkMatrices 2 bRows rInverse) == some .constantInverse &&
    failure? (FrameDeclarations.checkMatrices 2 [[p2 [([0, 0], q (Int.ofNat (2 ^ 512)))], z], [z, k 1]] bInverse) ==
      some (.entry 0 0) &&
    failure? (FrameDeclarations.checkMatrices 2 bRows bRows) == some .leftInverse &&
    failure? (FrameDeclarations.checkMatrices 2 rRows rRows) == some .leftInverse &&
    failure? (FrameDeclarations.checkMatrices 2 rRows rInverse) == none &&
    failure? (FrameDeclarations.checkMatrices 2 bRows bInverse) == none &&
    failure? (FrameDeclarations.checkMatrices 0 [] []) == none)
#eval check "checkMatrices bounds the whole of a constant frame, as a Gram matrix is bounded"
  (let matrix := (distinctEntries (10 ^ 62) false).map (·.map fun (a, d) => q (Int.ofNat a) d)
   failure? (FrameDeclarations.checkBounds matrix) == some .matrix &&
    failure? (FrameDeclarations.checkBounds ((distinctEntries 100 false).map (·.map fun (a, d) => q (Int.ofNat a) d)))
      == none &&
    failure? (FrameDeclarations.checkMatrices 16 (FrameDeclarations.constants 16 matrix)
      (FrameDeclarations.constants 16 matrix)) == some .matrix)
/-- An `n × n` identity of polynomials of arity `n` with `entries` placed at
`(row, column)`. -/
private def placed (dimension : Nat) (entries : List ((Nat × Nat) × Poly)) : PolyMatrix :=
  (List.range dimension).map fun i => (List.range dimension).map fun j =>
    match entries.find? (·.1 == (i, j)) with
    | some (_, p) => p
    | none => if i == j then Poly.one dimension else []

/-- An expression expanded in `coordinates`, or `[]` if it is beyond a limit. -/
private def expanded (coordinates : List String) (e : Source.PolyExpr) : Poly :=
  match AlgebraBasis.run (e.evaluate coordinates) with
  | .ok p => p
  | .error _ => []

#eval check "the work and term limits of a polynomial frame are failures of checkMatrices"
  (let f := expanded ["x", "y"] dense16
   let g := expanded ((List.range 16).map fun i => s!"c{i}") heavy
   f.length == 153 && g.length == 455 &&
    failure? (FrameDeclarations.checkMatrices 2 (placed 2 [((0, 1), f)]) (placed 2 [((1, 1), f)])) ==
      some (.work (.limit "term")) &&
    failure? (FrameDeclarations.checkMatrices 16 (placed 16 [((0, 1), g)]) (placed 16 [((1, 1), g)])) ==
      some (.work (.limit "work")) &&
    failure? (FrameDeclarations.checkMatrices 2 (placed 2 [((0, 1), f)]) (placed 2 [((0, 1), Poly.neg f)])) == none)
#eval check "Failure.code is E_LIMIT for the limits and E_FRAME otherwise"
  ([FrameDeclarations.Failure.dimension, .entry 0 0, .matrix, .work (.limit "work")].all (·.code == "E_LIMIT") &&
    [FrameDeclarations.Failure.shape false, .shape true, .constantInverse, .leftInverse, .rightInverse].all
      (·.code == "E_FRAME"))

end VastitasKernel.Indexed.FrameDeclarationRegression
