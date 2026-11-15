import VastitasKernel.ResourceProtocol
import VastitasKernel.IndexedAcceptance
import VastitasKernel.RegressionSupport

set_option autoImplicit false

/-! The spectral declarations, families, invariants and observations (Stage 5,
#806; `std::linalg::spectral`) through the public wire decoders, the source
checker and the declaration audit. These are executable regressions, not
proofs.

Protocol 9 decodes each wire shape of a free module, an endomorphism, a
spectrum and a branch, of the four family representations, of the morphism
definitions `trace_power` and `char_coefficient`, and of the five observation
primitives; protocols 7 and 8 reject each with `E_PROTOCOL`. No shape has a
field for a certificate. The spectral families are data-model rules and are
checked in full. Nothing else is implemented yet: the source checker rejects
every spectral declaration, invariant and observation with `E_SPECTRAL`, and
the declaration audit rejects every spectral entry. -/
namespace VastitasKernel.Indexed.SpectralDeclarationRegression

open Lean

private def check := RegressionSupport.check "spectral declaration regression failed"

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
private def sumJson (terms : List Json) : Json := Json.mkObj [("op", toJson "sum"), ("terms", toJson terms)]
private def productJson (factors : List Json) : Json := Json.mkObj [("op", toJson "product"), ("factors", toJson factors)]
private def powJson (base : Json) (exponent : Nat) : Json :=
  Json.mkObj [("op", toJson "pow"), ("base", base), ("exponent", toJson (toString exponent))]
private def objectParameter : Json := Json.mkObj [("kind", toJson "object"), ("domain", pathJson "CInfAffine")]
private def canonical (object : Nat) : Json := Json.mkObj [("kind", toJson "canonical"), ("object", toJson object)]
private def family (name : String) (parameters constraints : List Json) (representation : String) : Json :=
  decl "family" name [("parameters", toJson parameters), ("constraints", toJson constraints),
    ("representation", toJson representation)]

private def smoothBase : List Json := [
  decl "marker" "CInfReal" [],
  decl "implementation" "SmoothR" [("marker", pathJson "CInfReal"), ("representation", toJson "smooth_affine"),
    ("capabilities", toJson ([] : List Json))],
  decl "classification" "CInfAffine" [("parents", toJson ([] : List Json)), ("domain", toJson [pathJson "SmoothR"])],
  decl "smooth_affine" "Pt" [("implementation", pathJson "SmoothR"), ("dimension", toJson "0"),
    ("coordinates", toJson ([] : List String))],
  decl "smooth_affine" "Line" [("implementation", pathJson "SmoothR"), ("dimension", toJson "1"),
    ("coordinates", toJson ["s"])],
  decl "smooth_affine" "Plane" [("implementation", pathJson "SmoothR"), ("dimension", toJson "2"),
    ("coordinates", toJson ["x", "y"])],
  family "Smooth" [objectParameter, objectParameter] [canonical 0, canonical 1] "smooth",
  family "Cotangent" [objectParameter] [canonical 0] "cotangent"]

/-- The four spectral representations and the families of `std::linalg::spectral`. -/
private def representations : List (String × String) := [
  ("FreeModule", "free_module"), ("Endomorphism", "endomorphism"), ("Spectrum", "spectrum"), ("Branch", "branch")]

private def spectralFamilies : List Json :=
  representations.map fun (name, representation) => family name [objectParameter] [canonical 0] representation

/-! ### The declarations of the Stage 5 example

`H = rows((x, y), (y, -x))` on `V = basis(e1, e2)`, `S = eigen(H, t)` and
`B = simple(S, localize = x^2 + y^2, witness = frac(1, 2) * t, exponent = 1)`. -/

private def freeModule (name : String) (basis : List String) (indices : List String := ["Plane"]) : Json :=
  decl "free_module" name [("family", pathJson "FreeModule"), ("indices", toJson (indices.map pathJson)),
    ("basis", toJson basis)]
private def endomorphism (name module : String) (rows : List (List Json)) (symmetric : Bool) : Json :=
  decl "endomorphism" name [("family", pathJson "Endomorphism"), ("indices", toJson [pathJson "Plane"]),
    ("module", pathJson module), ("rows", toJson (rows.map toJson)), ("symmetric", toJson symmetric)]
private def spectrum (name endo fiber : String) : Json :=
  decl "spectrum" name [("family", pathJson "Spectrum"), ("indices", toJson [pathJson "Plane"]),
    ("endomorphism", pathJson endo), ("fiber", toJson fiber)]
private def branch (name spec : String) (localize witness : Json) (exponent : String) : Json :=
  decl "branch" name [("family", pathJson "Branch"), ("indices", toJson [pathJson "Plane"]),
    ("spectrum", pathJson spec), ("localize", localize), ("witness", witness), ("exponent", toJson exponent)]

private def moduleV : Json := freeModule "V" ["e1", "e2"]
private def endoH : Json :=
  endomorphism "H" "V" [[coordinate "x", coordinate "y"], [coordinate "y", negJson (coordinate "x")]] true
private def spectrumS : Json := spectrum "S" "H" "t"
private def branchB : Json :=
  branch "B" "S" (sumJson [powJson (coordinate "x") 2, powJson (coordinate "y") 2])
    (productJson [fraction 1 2, coordinate "t"]) "1"

/-- `morphism name : Smooth<Plane, Line> = definition`. -/
private def invariant (name : String) (definition : Json) : Json :=
  decl "morphism" name [("family", pathJson "Smooth"), ("indices", toJson [pathJson "Plane", pathJson "Line"]),
    ("definition", definition)]
private def tracePower (endo : String) (power : String) : Json :=
  Json.mkObj [("kind", toJson "trace_power"), ("endomorphism", pathJson endo), ("power", toJson power)]
private def charCoefficient (spec : String) (index : String) : Json :=
  Json.mkObj [("kind", toJson "char_coefficient"), ("spectrum", pathJson spec), ("index", toJson index)]

/-- `indexed primitive name = op(fields…)`. -/
private def primitive (name op : String) (fields : List (String × Json)) : Json :=
  decl "primitive" name [("binding", Json.mkObj ([("op", toJson op)] ++ fields))]
/-- `t - 2`, an element of `A[t]`. -/
private def shifted : Json := sumJson [coordinate "t", negJson (natural 2)]

/-- The five observations, each with its name and op. They name the spectrum
`spec` or the branch `branch`. -/
private def observations (spec branch : String) : List (String × String × Json) := [
  ("ann", "annihilates", primitive "ann" "annihilates" [("map_family", pathJson "Smooth"),
    ("spectrum", pathJson spec), ("element", shifted)]),
  ("entry", "action_entry", primitive "entry" "action_entry" [("map_family", pathJson "Smooth"),
    ("spectrum", pathJson spec), ("element", shifted), ("row", toJson "e1"), ("column", toJson "e2")]),
  ("on", "on_branch", primitive "on" "on_branch" [("map_family", pathJson "Smooth"), ("line", pathJson "Line"),
    ("branch", pathJson branch)]),
  ("dlam", "branch_differential", primitive "dlam" "branch_differential" [("map_family", pathJson "Smooth"),
    ("cotangent", pathJson "Cotangent"), ("line", pathJson "Line"), ("branch", pathJson branch)]),
  ("proj", "branch_projector", primitive "proj" "branch_projector" [("map_family", pathJson "Smooth"),
    ("line", pathJson "Line"), ("branch", pathJson branch), ("row", toJson "e1"), ("column", toJson "e2")])]

/-! ### Requests -/

private def mod (declarations : List Json) : Json := Json.mkObj [
  ("path", toJson ([] : List String)), ("public", toJson true), ("span", span),
  ("imports", toJson ([] : List Json)), ("generics", toJson ([] : List Json)),
  ("methods", toJson ([] : List Json)), ("functions", toJson ([] : List Json)),
  ("indexed_declarations", toJson declarations)]

private def request (version : Nat) (declarations : List Json) : Json := Json.mkObj [
  ("version", toJson version), ("input", toJson "package"), ("file", toJson "spectral.vast"),
  ("root", toJson "/spectral/Vastitas.toml"),
  ("packages", toJson [Json.mkObj [
    ("source", toJson "/spectral/Vastitas.toml"), ("name", toJson "spectral"), ("version", toJson "0.1.0"),
    ("dependencies", toJson ([] : List Json)), ("modules", toJson [mod declarations])]])]

/-- The code and message of a public request, or `accepted`: protocols 8 and 9
through `ResourceSource.Wire`, protocol 7 through `Indexed.Wire`. -/
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
`E_PROTOCOL` and a message that contains `text`. -/
private def rejectedBefore9 (j : Json) (text : String) : Bool :=
  [7, 8].all fun version => rejectsWith version [j] "E_PROTOCOL" text

/-- The object `j` with the field `name` added. -/
private def withField (j : Json) (name : String) (value : Json) : Json :=
  Json.mkObj ((j.getObj?.toOption.getD {}).toArray.toList ++ [(name, value)])

/-- The object `j` without the field `name`. -/
private def withoutField (j : Json) (name : String) : Json :=
  Json.mkObj ((j.getObj?.toOption.getD {}).toArray.toList.filter (·.1 != name))

/-! ## The spectral families are data-model rules -/

#eval check "protocol 9 accepts the spectral families"
  ((outcome 9 (smoothBase ++ spectralFamilies)).1 == "accepted")
#eval check "protocols 7 and 8 reject each spectral family representation with E_PROTOCOL"
  (representations.all fun (_, representation) =>
    rejectedBefore9 (family "F" [] [] representation) "spectral declarations require protocol 9")

private def rejectsFamily (families : List Json) (text : String) : Bool :=
  rejectsWith 9 (smoothBase ++ families) "E_TYPE" text

#eval check "a spectral family has one object parameter and the constraint canonical(0)"
  (representations.all fun (name, representation) =>
    rejectsFamily [family name [objectParameter, objectParameter] [canonical 0] representation]
        "exactly one parameter, of the form `object(…)`" &&
      rejectsFamily [family name [objectParameter] [] representation] "exactly the constraint `canonical(0)`")

/-! ## Spectral declarations: protocol 9 only, rejected until implemented -/

/-- Each spectral declaration shape, with what the source checker calls it and
the declarations it names, which follow it in a request. -/
private def declarations : List (String × String × Json × List Json) := [
  ("free module", "V", moduleV, []),
  ("endomorphism", "H", endoH, [moduleV]),
  ("spectrum", "S", spectrumS, [endoH, moduleV]),
  ("branch", "B", branchB, [spectrumS, endoH, moduleV])]

#eval check "protocol 9 decodes each spectral declaration shape"
  (declarations.all fun (_, _, j, _) => decodes j true)
#eval check "protocols 7 and 8 do not decode a spectral declaration"
  (declarations.all fun (_, _, j, _) => !decodes j false)
#eval check "protocols 7 and 8 reject each spectral declaration with E_PROTOCOL"
  (declarations.all fun (_, _, j, _) => rejectedBefore9 j "spectral declarations require protocol 9")
#eval check "the source checker rejects each spectral declaration with E_SPECTRAL until it is implemented"
  (declarations.all fun (kind, name, j, named) =>
    rejectsWith 9 (smoothBase ++ spectralFamilies ++ [j] ++ named) "E_SPECTRAL"
      s!"the {kind} `spectral::{name}` is not implemented yet")
#eval check "an endomorphism without rows, a free module without a basis and a long exponent decode"
  (decodes (endomorphism "H" "V" [] false) true && decodes (freeModule "V" []) true &&
    decodes (branch "B" "S" (natural 1) (natural 1) "123456789") true)
#eval check "the source checker rejects the whole Stage 5 example at its first declaration"
  (rejectsWith 9 (smoothBase ++ spectralFamilies ++ [moduleV, endoH, spectrumS, branchB] ++
      [invariant "tr2" (tracePower "H" "2"), invariant "c0" (charCoefficient "S" "0")] ++
      (observations "S" "B").map (·.2.2))
    "E_SPECTRAL" "the free module `spectral::V` is not implemented yet")

#eval check "a spectral declaration names one object"
  (rejectsWith 9 (smoothBase ++ spectralFamilies ++ [freeModule "V" ["e1"] ["Plane", "Pt"]])
      "E_SPECTRAL" "a free module names one object, as in `FreeModule<X>`, but 2 are given" &&
    rejectsWith 9 (smoothBase ++ spectralFamilies ++ [freeModule "V" ["e1"] []])
      "E_SPECTRAL" "a free module names one object, as in `FreeModule<X>`, but 0 are given")

#eval check "the names of a spectral declaration resolve"
  (rejectsWith 9 (smoothBase ++ spectralFamilies ++ [endoH]) "E_NAME" "undefined name 'V'" &&
    rejectsWith 9 (smoothBase ++ spectralFamilies ++ [spectrumS]) "E_NAME" "undefined name 'H'" &&
    rejectsWith 9 (smoothBase ++ spectralFamilies ++ [branchB]) "E_NAME" "undefined name 'S'")

/- A certificate is never on the wire: the kernel computes it, so a certificate
field is an unknown field. -/
#eval check "a spectral declaration takes exactly its fields, and no certificate"
  (!decodes (withField moduleV "rank" (toJson "2")) true &&
    !decodes (withField endoH "transpose" (toJson ([] : List Json))) true &&
    !decodes (withField spectrumS "characteristic" (toJson ([] : List Json))) true &&
    !decodes (withField spectrumS "adjugate" (toJson ([] : List Json))) true &&
    !decodes (withField spectrumS "certificate" (toJson ([] : List Json))) true &&
    !decodes (withField branchB "quotient" (natural 0)) true &&
    !decodes (withoutField moduleV "basis") true &&
    !decodes (withoutField endoH "symmetric") true &&
    !decodes (withoutField spectrumS "fiber") true &&
    !decodes (withoutField branchB "witness") true &&
    !decodes (withField endoH "symmetric" (toJson "true")) true &&
    !decodes (branch "B" "S" (natural 1) (natural 1) "-1") true &&
    !decodes (branch "B" "S" (natural 1) (natural 1) "") true)
#eval check "the exponent of a branch has a bounded number of digits"
  (!decodes (branch "B" "S" (natural 1) (natural 1) (String.ofList (List.replicate 65 '1'))) true &&
    decodes (branch "B" "S" (natural 1) (natural 1) (String.ofList (List.replicate 64 '1'))) true)

/-! ## Spectral invariants: declared morphisms, rejected until implemented -/

private def invariants : List (String × String × Json) := [
  ("tr2", "trace_power", invariant "tr2" (tracePower "H" "2")),
  ("c0", "char_coefficient", invariant "c0" (charCoefficient "S" "0"))]

#eval check "protocol 9 decodes each spectral invariant"
  (invariants.all fun (_, _, j) => decodes j true)
#eval check "protocols 7 and 8 reject each spectral invariant with E_PROTOCOL"
  (invariants.all fun (_, _, j) => rejectedBefore9 j "require protocol 9")
/- The invariant names a declaration that is not spectral, so that no spectral
declaration is rejected before it. -/
#eval check "the source checker rejects each spectral invariant with E_SPECTRAL until it is implemented"
  (rejectsWith 9 (smoothBase ++ [invariant "tr2" (tracePower "Plane" "2")]) "E_SPECTRAL"
      "the `trace_power` declaration `spectral::tr2` is not implemented yet" &&
    rejectsWith 9 (smoothBase ++ [invariant "c0" (charCoefficient "Plane" "0")]) "E_SPECTRAL"
      "the `char_coefficient` declaration `spectral::c0` is not implemented yet")
#eval check "the endomorphism or spectrum of an invariant resolves"
  (rejectsWith 9 (smoothBase ++ [invariant "tr2" (tracePower "Missing" "2")]) "E_NAME" "undefined name 'Missing'" &&
    rejectsWith 9 (smoothBase ++ [invariant "c0" (charCoefficient "Missing" "0")]) "E_NAME"
      "undefined name 'Missing'")
#eval check "a spectral invariant takes exactly its fields"
  (!decodes (invariant "tr2" (withField (tracePower "H" "2") "map" (toJson ([] : List Json)))) true &&
    !decodes (invariant "tr2" (withoutField (tracePower "H" "2") "power")) true &&
    !decodes (invariant "c0" (withoutField (charCoefficient "S" "0") "index")) true &&
    !decodes (invariant "tr2" (tracePower "H" "-2")) true &&
    !decodes (invariant "c0" (charCoefficient "S" (String.ofList (List.replicate 65 '1')))) true)

/-! ## Spectral observations: protocol 9 only, rejected until implemented -/

#eval check "protocol 9 decodes each spectral observation"
  ((observations "S" "B").all fun (_, _, j) => decodes j true)
#eval check "protocols 7 and 8 reject each spectral observation with E_PROTOCOL"
  ((observations "S" "B").all fun (_, _, j) => rejectedBefore9 j "unknown indexed primitive contract")
/- The observations name a declaration that is not spectral, so that no
spectral declaration is rejected before them. -/
#eval check "the source checker rejects each spectral observation with E_SPECTRAL until it is implemented"
  ((observations "Plane" "Plane").all fun (name, op, j) =>
    rejectsWith 9 (smoothBase ++ [j]) "E_SPECTRAL"
      s!"the `{op}` declaration `spectral::{name}` is not implemented yet")
#eval check "a spectral observation takes exactly its fields"
  ((observations "S" "B").all fun (_, _, j) =>
    let binding := (j.getObjValD "binding")
    !decodes (withField j "binding" (withField binding "certificate" (toJson ([] : List Json)))) true &&
      !decodes (withField j "binding" (withoutField binding "map_family")) true)

/-! ## A spectral entry is invalid in the declaration audit

A checked environment never holds a spectral declaration: `Entry.Valid` calls
the checks of `SpectralDeclarations`, which reject every entry until they are
implemented. -/

private def pkg : Namespace.PackageId := ⟨"/spectral/Vastitas.toml", "spectral", "0.1.0"⟩
private def sid (name : String) : DeclId := ⟨⟨pkg, []⟩, name⟩

private def entries : List Entry := [
  ⟨sid "V", .freeModule (sid "FreeModule") (sid "Plane") ["e1", "e2"]⟩,
  ⟨sid "H", .endomorphism (sid "Endomorphism") (sid "Plane") (sid "V") [] true⟩,
  ⟨sid "S", .spectrum (sid "Spectrum") (sid "Plane") (sid "H") "t" ⟨[], [], []⟩⟩,
  ⟨sid "B", .branch (sid "Branch") (sid "Plane") (sid "S") [] [] 1 []⟩]

#eval check "the declaration audit rejects each spectral entry"
  (entries.all fun entry => !validEntry [] [] entry && !validEnvironment [entry])

end VastitasKernel.Indexed.SpectralDeclarationRegression
