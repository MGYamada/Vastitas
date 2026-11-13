import VastitasKernel.ResourceProtocol
import VastitasKernel.IndexedAcceptance

set_option autoImplicit false

/-! Frame declarations and the frame families (Stage 4, #759) through the
public wire decoders and the source checker. These are executable regressions,
not proofs.

Protocol 9 decodes each wire shape of a frame declaration, of a frame family
representation and of a frame parameter; protocols 7 and 8 reject each with
`E_PROTOCOL`. The frame families are data-model rules and are checked in
full. Frame declarations are not implemented yet: the source checker rejects
every one with `E_FRAME`, and the declaration audit rejects a frame entry. -/
namespace VastitasKernel.Indexed.FrameDeclarationRegression

open Lean

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
    (columns [[natural 1, natural 0], [.mkObj [("op", toJson "neg"), ("operand", coordinate "x")], natural 1]])
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

/-! ## Frame declarations: protocol 9 only, rejected until implemented -/

/-- Each frame declaration shape, with the name it declares. -/
private def frames : List (String × Json) :=
  [("b", constantFrame), ("bx", pointFrame), ("e", coordinateFrame)]

#eval check "protocol 9 decodes each frame declaration shape"
  (frames.all fun (_, j) => decodes j true)
#eval check "protocols 7 and 8 do not decode a frame declaration"
  (frames.all fun (_, j) => !decodes j false)
#eval check "protocols 7 and 8 reject each frame declaration with E_PROTOCOL"
  (frames.all fun (_, j) => rejectedBefore9 j)
#eval check "the source checker rejects each frame declaration with E_FRAME until it is implemented"
  (frames.all fun (name, j) => rejectsWith 9 (smoothBase ++ frameFamilies ++ [j]) "E_FRAME"
    s!"the frame `frames::{name}` is not implemented yet")
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

/-! ## A frame entry is invalid in the declaration audit

A checked environment never holds a frame: `Entry.Valid` calls the frame
check, which rejects every frame until it is implemented. -/

private def pkg : Namespace.PackageId := ⟨"/frames/Vastitas.toml", "frames", "0.1.0"⟩
private def frameId : DeclId := ⟨⟨pkg, []⟩, "b"⟩

#eval check "the declaration audit rejects a frame entry"
  (!validEntry [] [] ⟨frameId, .frame frameId frameId [] []⟩ &&
    !validEnvironment [⟨frameId, .frame frameId frameId [] []⟩])

end VastitasKernel.Indexed.FrameDeclarationRegression
