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
checked in full.

Through the source checker, the Stage 5 example is accepted in any order of
its declarations, with the kernel's certificate (`χ = t² − x² − y²`,
`adj = tI + H`, the idempotence quotient `−I`) and the gap quotient `1`; each
rejection of the profile is `E_SPECTRAL` with a message that names the
declaration, or `E_LIMIT` for the rank, power and exponent limits; the
declaration audit rejects every tampered certificate, quotient, localization,
witness, exponent, basis and row. The elaboration turns the invariants into
smooth maps with their exact images and provenance, and fills the
declarations, elements and basis indices of the observations; their registry
entries are the spectral registry's (`SpectralRegression`). -/
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

/-! ## Spectral declarations: protocol 9 only -/

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
/- A declaration comes before the declarations it names, so acceptance does not
depend on the order of the declarations. -/
#eval check "protocol 9 accepts each declaration of the Stage 5 example before the declarations it names"
  (declarations.all fun (_, _, j, named) => (outcome 9 (smoothBase ++ spectralFamilies ++ [j] ++ named)).1 == "accepted")
#eval check "protocol 9 accepts the four declarations of the Stage 5 example"
  ((outcome 9 (smoothBase ++ spectralFamilies ++ [moduleV, endoH, spectrumS, branchB])).1 == "accepted")
#eval check "an endomorphism without rows, a free module without a basis and a long exponent decode"
  (decodes (endomorphism "H" "V" [] false) true && decodes (freeModule "V" []) true &&
    decodes (branch "B" "S" (natural 1) (natural 1) "123456789") true)
#eval check "the source checker names the first spectral declaration that fails"
  (rejectsWith 9 (smoothBase ++ spectralFamilies ++ [freeModule "V" ["e1", "e1"], endoH]) "E_SPECTRAL"
    "the free module `spectral::V` names the basis vector `e1` twice")
#eval check "a long exponent is a limit, before any product"
  (rejectsWith 9 (smoothBase ++ spectralFamilies ++
      [branch "B" "S" (natural 1) (natural 1) "123456789", spectrumS, endoH, moduleV])
    "E_LIMIT" "the branch `spectral::B` has the exponent 123456789, beyond the limit of 8")

#eval check "a spectral declaration names one object"
  (rejectsWith 9 (smoothBase ++ spectralFamilies ++ [freeModule "V" ["e1"] ["Plane", "Pt"]])
      "E_SPECTRAL" "a free module names one object, as in `FreeModule<X>`, but 2 are given" &&
    rejectsWith 9 (smoothBase ++ spectralFamilies ++ [freeModule "V" ["e1"] []])
      "E_SPECTRAL" "a free module names one object, as in `FreeModule<X>`, but 0 are given")

/- The fiber coordinate of a spectrum is a new identifier: the wire carries any
string, and the source checker rejects one that is not an identifier, a
strict keyword among them (#831), or that names a basis vector of the free
module. -/
#eval check "the fiber coordinate of a spectrum is a new identifier"
  ((["", "t t", "0", "1t", "t-1", "λ"].all fun fiber =>
      rejectsWith 9 (smoothBase ++ spectralFamilies ++ [moduleV, endoH, spectrum "S" "H" fiber]) "E_SPECTRAL"
        s!"the fiber coordinate `{fiber}` of the spectrum `spectral::S` is not an identifier") &&
    (strictKeywords.all fun fiber =>
      rejectsWith 9 (smoothBase ++ spectralFamilies ++ [moduleV, endoH, spectrum "S" "H" fiber]) "E_SPECTRAL"
        (s!"the fiber coordinate `{fiber}` of the spectrum `spectral::S` is a strict keyword, not an " ++
          "identifier; `eigen(H, t)` names the fiber coordinate with a new identifier")) &&
    (["e1", "e2"].all fun fiber =>
      rejectsWith 9 (smoothBase ++ spectralFamilies ++ [moduleV, endoH, spectrum "S" "H" fiber]) "E_SPECTRAL"
        (s!"the fiber coordinate `{fiber}` of the spectrum `spectral::S` is a basis vector of the free module " ++
          "`spectral::V`")) &&
    rejectsWith 9 (smoothBase ++ spectralFamilies ++ [moduleV, endoH, spectrum "S" "H" "y"]) "E_SPECTRAL"
      "the fiber coordinate `y` of the spectrum `spectral::S` is a coordinate of `spectral::Plane`" &&
    (["t", "_t", "lambda2", "H", "V", "indexed", "witness", "eigen", "If", "iff", "type_"].all fun fiber =>
      (outcome 9 (smoothBase ++ spectralFamilies ++ [moduleV, endoH, spectrum "S" "H" fiber])).1 == "accepted"))

/- The identifier rule of the fiber audit is the source grammar's: the ASCII
pattern without the strict keywords (#831). -/
#eval check "a strict keyword is no identifier and no fiber coordinate; an ordinary name is"
  (strictKeywords.length == 21 && strictKeywords.all (!SpectralDeclarations.isIdentifier ·) &&
    !SpectralDeclarations.fiberValid ["x"] ["e"] "if" && SpectralDeclarations.fiberValid ["x"] ["e"] "t" &&
    ["t", "_", "x1", "witness", "indexed", "Fn", "If"].all SpectralDeclarations.isIdentifier)

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

/-! ## Spectral invariants on the wire -/

private def invariants : List (String × String × Json) := [
  ("tr2", "trace_power", invariant "tr2" (tracePower "H" "2")),
  ("c0", "char_coefficient", invariant "c0" (charCoefficient "S" "0"))]

#eval check "protocol 9 decodes each spectral invariant"
  (invariants.all fun (_, _, j) => decodes j true)
#eval check "protocols 7 and 8 reject each spectral invariant with E_PROTOCOL"
  (invariants.all fun (_, _, j) => rejectedBefore9 j "require protocol 9")
#eval check "a spectral invariant names an endomorphism or a spectrum"
  (rejectsWith 9 (smoothBase ++ [invariant "tr2" (tracePower "Plane" "2")]) "E_SPECTRAL"
      ("the `trace_power` declaration `spectral::tr2` takes the trace of a power of `spectral::Plane`, which " ++
        "is not an endomorphism declaration") &&
    rejectsWith 9 (smoothBase ++ [invariant "c0" (charCoefficient "Plane" "0")]) "E_SPECTRAL"
      ("the `char_coefficient` declaration `spectral::c0` takes a coefficient of the characteristic " ++
        "polynomial of `spectral::Plane`, which is not a spectrum declaration"))
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

/-! ## Spectral observations on the wire -/

#eval check "protocol 9 decodes each spectral observation"
  ((observations "S" "B").all fun (_, _, j) => decodes j true)
#eval check "protocols 7 and 8 reject each spectral observation with E_PROTOCOL"
  ((observations "S" "B").all fun (_, _, j) => rejectedBefore9 j "unknown indexed primitive contract")
#eval check "a spectral observation names a spectrum or a branch"
  ((observations "Plane" "Plane").all fun (_, op, j) =>
    rejectsWith 9 (smoothBase ++ [j]) "E_SPECTRAL"
      (if op == "annihilates" || op == "action_entry" then
        s!"the spectrum of `{op}` must be a spectrum, but `spectral::Plane` is not a spectrum declaration"
      else s!"the branch of `{op}` must be a branch, but `spectral::Plane` is not a branch declaration"))
#eval check "a spectral observation takes exactly its fields"
  ((observations "S" "B").all fun (_, _, j) =>
    let binding := (j.getObjValD "binding")
    !decodes (withField j "binding" (withField binding "certificate" (toJson ([] : List Json)))) true &&
      !decodes (withField j "binding" (withoutField binding "map_family")) true)

/-! ## Through the source checker

The source programs below declare the Stage 5 example and its variants
directly, without the wire. `Source.checkDeclarations` runs the elaboration
and the whole declaration audit; `Source.lower` runs the elaboration alone,
which shows the elaborated invariants and observations: their registry
entries belong to the spectral registry (`IndexedSpectralRegistry`), which
the audit consults afterwards. -/

private def pkg : Namespace.PackageId := ⟨"/spectral/Vastitas.toml", "spectral", "0.1.0"⟩
private def sid (name : String) : DeclId := ⟨⟨pkg, []⟩, name⟩
private def spath (name : String) : Source.Path := ⟨[name], {}⟩
private def sdecl (name : String) (body : Source.Body) : Source.Declaration := ⟨name, body, true, {}⟩
private def n (value : Nat) : Source.PolyExpr := .natural value
private def c (name : String) : Source.PolyExpr := .coordinate name
private def neg (e : Source.PolyExpr) : Source.PolyExpr := .neg e
private def frac (numerator : Int) (denominator : Nat) : Source.PolyExpr := .fraction numerator denominator
private def sq (e : Source.PolyExpr) : Source.PolyExpr := .pow e 2

private def space (name : String) (coordinates : List String) : Source.Declaration :=
  sdecl name (.smoothAffine (spath "SmoothR") coordinates.length coordinates)
private def objectFamily (name : String) (representation : FamilyRepresentation) : Source.Declaration :=
  sdecl name (.family ⟨[.object (spath "CInfAffine")], [.canonical 0], representation⟩)

/-- Smooth objects of dimension 0, 1 and 2, the smooth, cotangent and spectral
families, and a presented object for contrast. -/
private def sourceBase : List Source.Declaration := [
  sdecl "CInfReal" .marker,
  sdecl "SmoothR" (.implementation (spath "CInfReal") .smoothAffine []),
  sdecl "CInfAffine" (.classification [] [spath "SmoothR"]),
  sdecl "Smooth" (.family ⟨[.object (spath "CInfAffine"), .object (spath "CInfAffine")],
    [.canonical 0, .canonical 1], .smooth⟩),
  objectFamily "Cotangent" (.fiber .cotangent),
  objectFamily "FreeModule" .freeModule,
  objectFamily "Endomorphism" .endomorphism,
  objectFamily "Spectrum" .spectrum,
  objectFamily "Branch" .branch,
  space "Pt" [],
  space "Line" ["s"],
  space "Plane" ["x", "y"],
  sdecl "QQ" .marker,
  sdecl "AffineQQ" (.implementation (spath "QQ") (.presentedAffine .rational) []),
  sdecl "SpecQQ" (.affine (spath "AffineQQ") [] [] none [])]

private def moduleDecl (name : String) (basis : List String) (object := "Plane") (family := "FreeModule") :
    Source.Declaration :=
  sdecl name (.freeModule (spath family) [spath object] basis)
private def endoDecl (name module : String) (rows : List (List Source.PolyExpr)) (symmetric := true)
    (object := "Plane") (family := "Endomorphism") : Source.Declaration :=
  sdecl name (.endomorphism (spath family) [spath object] (spath module) rows symmetric)
private def spectrumDecl (name endomorphism : String) (fiber := "t") (object := "Plane") (family := "Spectrum") :
    Source.Declaration :=
  sdecl name (.spectrum (spath family) [spath object] (spath endomorphism) fiber)
private def branchDecl (name spectrum : String) (localize witness : Source.PolyExpr) (exponent : Nat)
    (object := "Plane") (family := "Branch") : Source.Declaration :=
  sdecl name (.branch (spath family) [spath object] (spath spectrum) localize witness exponent)

private def gapExpr : Source.PolyExpr := .sum [sq (c "x"), sq (c "y")]
private def halfT : Source.PolyExpr := .product [frac 1 2, c "t"]
private def moduleSource : Source.Declaration := moduleDecl "V" ["e1", "e2"]
private def endoSource : Source.Declaration := endoDecl "H" "V" [[c "x", c "y"], [c "y", neg (c "x")]]
private def spectrumSource : Source.Declaration := spectrumDecl "S" "H"
/-- `V`, `H`, `S` and `B` of the Stage 5 example. -/
private def stage5 : List Source.Declaration :=
  [moduleSource, endoSource, spectrumSource, branchDecl "B" "S" gapExpr halfT 1]
/-- `V`, `H` and `S`, and the branch `branch`. -/
private def withBranch (branch : Source.Declaration) : List Source.Declaration :=
  [moduleSource, endoSource, spectrumSource, branch]

private def program (ds : List Source.Declaration) : Source.Program := {
  file := "spectral", root := pkg.source,
  packages := [⟨pkg, [], [{
    module := {path := [], isPublic := true, imports := [], functions := [], generics := [], methods := [], span := {}}
    declarations := sourceBase ++ ds }], none⟩] }

private def code (ds : List Source.Declaration) : String :=
  match Source.checkDeclarations (program ds) with
  | .ok _ => "accepted"
  | .error e => e.code

private def message (ds : List Source.Declaration) : String :=
  match Source.checkDeclarations (program ds) with
  | .ok _ => ""
  | .error e => e.message

/-- `ds` is rejected with `expected` and a message that contains `text`. -/
private def rejects (ds : List Source.Declaration) (expected text : String) : Bool :=
  code ds == expected && mentions (message ds) text

private def checked (ds : List Source.Declaration) : Option Core.Declarations :=
  match Source.checkDeclarations (program ds) with
  | .ok result => some result.resolved.declarations
  | .error _ => none

private def lowered (ds : List Source.Declaration) : Option Core.Declarations :=
  match Source.lower (program ds) with
  | .ok resolved => some resolved.declarations
  | .error _ => none

private def lowerCode (ds : List Source.Declaration) : String :=
  match Source.lower (program ds) with
  | .ok _ => "lowered"
  | .error e => e.code

private def lowerMessage (ds : List Source.Declaration) : String :=
  match Source.lower (program ds) with
  | .ok _ => ""
  | .error e => e.message

private def lowerRejects (ds : List Source.Declaration) (expected text : String) : Bool :=
  lowerCode ds == expected && mentions (lowerMessage ds) text

private def declarationIn (env : Option Core.Declarations) (name : String) : Option Declaration :=
  env.bind fun env => lookup env.indexed (sid name)

private def bindingIn (env : Option Core.Declarations) (name : String) : Option PrimitiveBinding :=
  env.bind fun env => (env.primitives.find? (·.id == sid name)).map (·.binding)

/-! ### The elaborated Stage 5 example -/

open AlgebraRuntime in
private def x : Poly := Poly.var 2 0
open AlgebraRuntime in
private def y : Poly := Poly.var 2 1
open AlgebraRuntime in
private def x3 : Poly := Poly.var 3 0
open AlgebraRuntime in
private def y3 : Poly := Poly.var 3 1
open AlgebraRuntime in
private def t3 : Poly := Poly.var 3 2
private def rowsH : PolyMatrix := [[x, y], [y, AlgebraRuntime.Poly.neg x]]
open AlgebraRuntime in
/-- `χ = t² − x² − y²`. -/
private def chi : Poly := Poly.sub (Poly.mul t3 t3) (Poly.add (Poly.mul x3 x3) (Poly.mul y3 y3))
open AlgebraRuntime in
/-- `adj(tI − H) = tI + H`. -/
private def adjugate : PolyMatrix := [[Poly.add t3 x3, y3], [y3, Poly.sub t3 x3]]
open AlgebraRuntime in
/-- `adj² − χ′·adj = −χ·I`. -/
private def idempotence : PolyMatrix := [[Poly.const 3 (-1), []], [[], Poly.const 3 (-1)]]
open AlgebraRuntime in
private def gap : Poly := Poly.add (Poly.mul x x) (Poly.mul y y)
open AlgebraRuntime in
private def witness : Poly := Poly.scale (1 / 2) t3

private def endoRef : EndoRef := ⟨sid "H", sid "Plane", sid "V", rowsH, true⟩
private def spectrumRef : SpectrumRef := ⟨sid "S", endoRef, chi, adjugate⟩
private def branchRef : BranchRef := ⟨sid "B", spectrumRef, gap, witness, 1⟩

#eval check "the source checker accepts the Stage 5 example in any order"
  (code stage5 == "accepted" && code stage5.reverse == "accepted" &&
    ["V", "H", "S", "B"].all fun name =>
      (declarationIn (checked stage5) name).isSome &&
        declarationIn (checked stage5) name == declarationIn (checked stage5.reverse) name)
#eval check "the endomorphism has its rows, expanded in the coordinates"
  (declarationIn (checked stage5) "H" == some (.endomorphism (sid "Endomorphism") (sid "Plane") (sid "V") rowsH true))
#eval check "the spectrum has the kernel's certificate: χ = t² − x² − y², adj = tI + H, Q = −I"
  (declarationIn (checked stage5) "S" ==
    some (.spectrum (sid "Spectrum") (sid "Plane") (sid "H") "t" ⟨chi, adjugate, idempotence⟩))
#eval check "the branch has its localization in the base and the kernel's quotient 1"
  (declarationIn (checked stage5) "B" ==
    some (.branch (sid "Branch") (sid "Plane") (sid "S") gap witness 1 (AlgebraRuntime.Poly.one 3)))
#eval check "the squared gap (2t·g, 4g²) is a valid chart too"
  (code (withBranch (branchDecl "B" "S" (.product [n 4, sq gapExpr]) (.product [n 2, c "t", gapExpr]) 1)) ==
    "accepted")

/-! ### Rejections

Each variant of the example is rejected at the first declaration that fails,
with `E_SPECTRAL` and a message that names it, or `E_LIMIT` for a limit. -/

private def jordan : List Source.Declaration :=
  [moduleSource, endoDecl "J" "V" [[n 2, n 1], [n 0, n 2]] (symmetric := false), spectrumDecl "SJ" "J"]

/-- `(label, declarations, code, text)`. -/
private def rejections : List (String × List Source.Declaration × String × String) := [
  ("rank 5", [moduleDecl "V" ["a", "b", "c", "d", "e"]], "E_LIMIT",
    "the free module `spectral::V` has rank 5, beyond the limit of 4"),
  ("no basis", [moduleDecl "V" []], "E_SPECTRAL", "the free module `spectral::V` has no basis vector"),
  ("a repeated basis vector", [moduleDecl "V" ["e1", "e2", "e1"]], "E_SPECTRAL",
    "the free module `spectral::V` names the basis vector `e1` twice"),
  ("another family", [moduleDecl "V" ["e1"] (family := "Spectrum")], "E_SPECTRAL",
    "the free module `spectral::V` is declared at `spectral::Spectrum`, which is not a family with the " ++
      "representation `free_module`"),
  ("a presented object", [moduleDecl "V" ["e1"] (object := "SpecQQ")], "E_SPECTRAL",
    "the free module `spectral::V` is on `spectral::SpecQQ`, which is not a smooth object"),
  ("not symmetric", [moduleSource, endoDecl "H" "V" [[c "x", c "y"], [c "x", neg (c "x")]]], "E_SPECTRAL",
    "the endomorphism `spectral::H` is declared `symmetric`, but its entry (e1, e2) differs from its entry (e2, e1)"),
  ("too few rows", [moduleSource, endoDecl "H" "V" [[c "x", c "y"]]], "E_SPECTRAL",
    "needs 2 rows, one for each basis vector, but it has 1"),
  ("a short row", [moduleSource, endoDecl "H" "V" [[c "x"], [c "y", c "x"]]], "E_SPECTRAL",
    "needs 2 entries in each row, but row 1 has 1"),
  ("a module of another object", [moduleDecl "W" ["e1"] (object := "Line"), endoDecl "H" "W" [[c "x"]]],
    "E_SPECTRAL", "an endomorphism and its free module have one object"),
  ("no module", [endoDecl "H" "Plane" [[c "x"]]], "E_SPECTRAL",
    "the endomorphism `spectral::H` acts on `spectral::Plane`, which is not a free module declaration"),
  ("an unknown coordinate", [moduleSource, endoDecl "H" "V" [[c "z", n 0], [n 0, n 0]]], "E_AFFINE_COORDINATE",
    "unknown coordinate z"),
  ("a fiber name that is a coordinate", [moduleSource, endoSource, spectrumDecl "S" "H" (fiber := "x")],
    "E_SPECTRAL", "the fiber coordinate `x` of the spectrum `spectral::S` is a coordinate of `spectral::Plane`"),
  ("a spectrum of a module", [moduleSource, spectrumDecl "S" "V"], "E_SPECTRAL",
    "the spectrum `spectral::S` is the spectrum of `spectral::V`, which is not an endomorphism declaration"),
  ("a spectrum of another object", [moduleSource, endoSource, spectrumDecl "S" "H" (object := "Line")],
    "E_SPECTRAL", "a spectrum and its endomorphism have one object"),
  ("a branch of an endomorphism", [moduleSource, endoSource, branchDecl "B" "H" gapExpr halfT 1], "E_SPECTRAL",
    "the branch `spectral::B` is a branch of `spectral::H`, which is not a spectrum declaration"),
  ("a localization with t", withBranch (branchDecl "B" "S" (.sum [sq (c "x"), sq (c "t")]) halfT 1),
    "E_SPECTRAL", "the localization of the branch `spectral::B` contains the fiber coordinate `t`"),
  ("a zero localization", withBranch (branchDecl "B" "S" (n 0) halfT 1), "E_SPECTRAL",
    "the localization of the branch `spectral::B` is zero"),
  ("an unreduced witness", withBranch (branchDecl "B" "S" gapExpr (.sum [halfT, .pow (c "t") 3]) 1), "E_SPECTRAL",
    "the witness of the branch `spectral::B` has degree 3 in the fiber coordinate `t`"),
  ("a wrong witness", withBranch (branchDecl "B" "S" gapExpr (.product [frac 1 3, c "t"]) 1), "E_SPECTRAL",
    "the witness of the branch `spectral::B` does not certify the gap"),
  ("a witness perturbed by 10⁻²⁰",
    withBranch (branchDecl "B" "S" gapExpr (.product [frac (5 * 10 ^ 19 + 1) (10 ^ 20), c "t"]) 1), "E_SPECTRAL",
    "the witness of the branch `spectral::B` does not certify the gap"),
  ("a wrong exponent", withBranch (branchDecl "B" "S" gapExpr halfT 2), "E_SPECTRAL",
    "the witness of the branch `spectral::B` does not certify the gap"),
  ("the gap at the origin", withBranch (branchDecl "B" "S" (n 1) halfT 0), "E_SPECTRAL",
    "the witness of the branch `spectral::B` does not certify the gap"),
  ("an exponent beyond the limit", withBranch (branchDecl "B" "S" gapExpr halfT 9), "E_LIMIT",
    "the branch `spectral::B` has the exponent 9, beyond the limit of 8"),
  ("the Jordan block", jordan ++ [branchDecl "BJ" "SJ" (n 1) (n 1) 0], "E_SPECTRAL",
    "the witness of the branch `spectral::BJ` does not certify the gap"),
  ("the Jordan block with a shifted witness", jordan ++ [branchDecl "BJ" "SJ" (n 1) (.sum [c "t", neg (n 2)]) 0],
    "E_SPECTRAL", "the witness of the branch `spectral::BJ` does not certify the gap")]

#eval show IO Unit from do
  for (label, ds, expected, text) in rejections do
    check s!"{label}: rejected with {expected} ({code ds}: {message ds})" (rejects ds expected text)

/-! ### Degenerate cases and the rank limit -/

private def basis4 : List String := ["e1", "e2", "e3", "e4"]

#eval check "the zero endomorphism has the spectrum t² and no chart at all"
  (let zero := [moduleSource, endoDecl "Z" "V" [[n 0, n 0], [n 0, n 0]], spectrumDecl "SZ" "Z"];
    code zero == "accepted" &&
      declarationIn (checked zero) "SZ" == some (.spectrum (sid "Spectrum") (sid "Plane") (sid "Z") "t"
        ⟨AlgebraRuntime.Poly.mul t3 t3, [[t3, []], [[], t3]], [[AlgebraRuntime.Poly.const 3 (-1), []],
          [[], AlgebraRuntime.Poly.const 3 (-1)]]⟩) &&
      [n 1, n 0, c "t", .product [frac 1 2, c "t"]].all fun w =>
        code (zero ++ [branchDecl "BZ" "SZ" (n 1) w 0]) == "E_SPECTRAL")
#eval check "a rank-1 endomorphism has the chart g = 1, W = 1, e = 0"
  (code [moduleDecl "L" ["e"], endoDecl "K" "L" [[c "x"]], spectrumDecl "SK" "K", branchDecl "BK" "SK" (n 1) (n 1) 0] ==
    "accepted")
#eval check "a 4 × 4 symmetric endomorphism, at the rank limit, has a checked spectrum"
  (code [moduleDecl "V4" basis4,
      endoDecl "H4" "V4" [[c "x", c "y", n 1, n 0], [c "y", n 0, c "x", n 1], [n 1, c "x", neg (c "y"), n 0],
        [n 0, n 1, n 0, c "x"]],
      spectrumDecl "S4" "H4"] == "accepted")
#eval check "a free module of rank 5 is beyond the limit before any endomorphism is read"
  (rejects [moduleDecl "V5" (basis4 ++ ["e5"]), endoDecl "H5" "V5" []] "E_LIMIT" "has rank 5")

/-! ### The declaration audit

The audit checks every stored declaration again: a tampered certificate,
quotient, localization, witness or row fails it. -/

private def tamper (env : Environment) (name : String) (change : Declaration → Declaration) : Environment :=
  env.map fun entry => if entry.id == sid name then ⟨entry.id, change entry.declaration⟩ else entry

open AlgebraRuntime in
private def tampered : List (String × String × (Declaration → Declaration)) := [
  ("χ", "S", fun
    | .spectrum f o e fiber cert => .spectrum f o e fiber {cert with characteristic := Poly.add cert.characteristic (Poly.one 3)}
    | d => d),
  ("adj", "S", fun
    | .spectrum f o e fiber cert => .spectrum f o e fiber {cert with adjugate := cert.adjugate.reverse}
    | d => d),
  ("the idempotence quotient", "S", fun
    | .spectrum f o e fiber cert => .spectrum f o e fiber {cert with idempotence := scalarZero}
    | d => d),
  ("the fiber name", "S", fun
    | .spectrum f o e _ cert => .spectrum f o e "x" cert
    | d => d),
  ("an empty fiber name", "S", fun
    | .spectrum f o e _ cert => .spectrum f o e "" cert
    | d => d),
  ("a fiber name with a space", "S", fun
    | .spectrum f o e _ cert => .spectrum f o e "t t" cert
    | d => d),
  ("a numeral as the fiber name", "S", fun
    | .spectrum f o e _ cert => .spectrum f o e "0" cert
    | d => d),
  ("a basis vector as the fiber name", "S", fun
    | .spectrum f o e _ cert => .spectrum f o e "e1" cert
    | d => d),
  ("a strict keyword as the fiber name", "S", fun
    | .spectrum f o e _ cert => .spectrum f o e "if" cert
    | d => d),
  ("the rows", "H", fun
    | .endomorphism f o m rows s => .endomorphism f o m rows.reverse s
    | d => d),
  ("the branch quotient", "B", fun
    | .branch f o s g w e _ => .branch f o s g w e []
    | d => d),
  ("the localization", "B", fun
    | .branch f o s g w e q => .branch f o s (Poly.scale 2 g) w e q
    | d => d),
  ("the witness", "B", fun
    | .branch f o s g w e q => .branch f o s g (Poly.scale 2 w) e q
    | d => d),
  ("the exponent", "B", fun
    | .branch f o s g w _ q => .branch f o s g w 2 q
    | d => d),
  ("the basis", "V", fun
    | .freeModule f o _ => .freeModule f o ["e1"]
    | d => d)]
where
  scalarZero : PolyMatrix := [[[], []], [[], []]]

#eval check "the audit accepts the elaborated example and rejects each tampered declaration"
  (match checked stage5 with
    | some env => validEnvironment env.indexed &&
      tampered.all fun (_, name, change) => !validEnvironment (tamper env.indexed name change)
    | none => false)
/- The branch stores polynomials, not the fiber name, so another ordinary name
of the fiber coordinate passes the audit, and a strict keyword does not (#831). -/
#eval check "the audit accepts an ordinary fiber name and rejects a strict keyword"
  (match checked stage5 with
    | some env =>
      let renamed (fiber : String) := tamper env.indexed "S" fun
        | .spectrum f o e _ cert => .spectrum f o e fiber cert
        | d => d
      (["lam", "witness", "If"].all fun fiber => validEnvironment (renamed fiber)) &&
        strictKeywords.all fun fiber => !validEnvironment (renamed fiber)
    | none => false)
#eval check "the declaration audit rejects a spectral entry outside its environment"
  (match checked stage5 with
    | some env => env.indexed.all fun entry =>
      match entry.declaration with
      | .freeModule .. | .endomorphism .. | .spectrum .. | .branch .. => !validEntry [] [] entry
      | _ => true
    | none => false)

/-! ### Invariants -/

private def invariantDecl (name : String) (definition : Source.MorphismDefinition) (source := "Plane")
    (target := "Line") : Source.Declaration :=
  sdecl name (.morphism (spath "Smooth") [spath source, spath target] definition)

private def lineMap : Application := ⟨sid "Smooth", [.object (.global (sid "Plane")), .object (.global (sid "Line"))]⟩

private def withInvariants : List Source.Declaration := stage5 ++ [
  invariantDecl "tr1" (.tracePower (spath "H") 1),
  invariantDecl "tr2" (.tracePower (spath "H") 2),
  invariantDecl "c0" (.charCoefficient (spath "S") 0),
  invariantDecl "c1" (.charCoefficient (spath "S") 1),
  invariantDecl "c2" (.charCoefficient (spath "S") 2)]

open AlgebraRuntime in
#eval check "an invariant is a smooth map with its exact image and its provenance"
  (let env := lowered withInvariants;
    bindingIn env "tr2" == some (.spectralInvariant lineMap ⟨2, [], [Poly.scale 2 gap]⟩ (.tracePower endoRef 2)) &&
      bindingIn env "tr1" == some (.spectralInvariant lineMap ⟨2, [], [[]]⟩ (.tracePower endoRef 1)) &&
      bindingIn env "c0" ==
        some (.spectralInvariant lineMap ⟨2, [], [Poly.neg gap]⟩ (.charCoefficient spectrumRef 0)) &&
      bindingIn env "c1" == some (.spectralInvariant lineMap ⟨2, [], [[]]⟩ (.charCoefficient spectrumRef 1)) &&
      bindingIn env "c2" ==
        some (.spectralInvariant lineMap ⟨2, [], [Poly.one 2]⟩ (.charCoefficient spectrumRef 2)))
#eval check "Newton's identity: c0 = −½ tr2 for the trace-free H"
  (match bindingIn (lowered withInvariants) "c0", bindingIn (lowered withInvariants) "tr2" with
    | some (.spectralInvariant _ c0 _), some (.spectralInvariant _ tr2 _) =>
      c0.images == tr2.images.map (AlgebraRuntime.Poly.scale (-1 / 2))
    | _, _ => false)

private def invariantRejections : List (String × Source.Declaration × String × String) := [
  ("the power 0", invariantDecl "bad" (.tracePower (spath "H") 0), "E_SPECTRAL",
    "the `trace_power` declaration `spectral::bad` takes the power 0"),
  ("the power 9", invariantDecl "bad" (.tracePower (spath "H") 9), "E_LIMIT",
    "the `trace_power` declaration `spectral::bad` takes the power 9, beyond the limit of 8"),
  ("the coefficient of t³", invariantDecl "bad" (.charCoefficient (spath "S") 3), "E_SPECTRAL",
    "takes the coefficient of t^3, but the characteristic polynomial has degree 2"),
  ("a trace power of a spectrum", invariantDecl "bad" (.tracePower (spath "S") 2), "E_SPECTRAL",
    "takes the trace of a power of `spectral::S`, which is not an endomorphism declaration"),
  ("a coefficient of an endomorphism", invariantDecl "bad" (.charCoefficient (spath "H") 0), "E_SPECTRAL",
    "the characteristic polynomial of `spectral::H`, which is not a spectrum declaration"),
  ("a target of dimension 2", invariantDecl "bad" (.tracePower (spath "H") 2) (target := "Plane"), "E_SPECTRAL",
    "the target `spectral::Plane` of the `trace_power` declaration `spectral::bad` must be 1-dimensional"),
  ("another source", invariantDecl "bad" (.charCoefficient (spath "S") 0) (source := "Line"), "E_SPECTRAL",
    "is a smooth map on `spectral::Line`, but its spectrum `spectral::S` is on `spectral::Plane`")]

#eval show IO Unit from do
  for (label, d, expected, text) in invariantRejections do
    check s!"{label}: rejected with {expected} ({lowerCode (stage5 ++ [d])}: {lowerMessage (stage5 ++ [d])})"
      (lowerRejects (stage5 ++ [d]) expected text)

/-! ### Observations -/

private def observe (name op : String) (arguments : List (String × Source.WireArgument)) : Source.Declaration :=
  sdecl name (.primitive ⟨op, arguments⟩)
private def ref (name : String) : Source.WireArgument := .path (spath name)
private def tMinus2 : Source.PolyExpr := .sum [c "t", neg (n 2)]

private def sourceObservations : List Source.Declaration := [
  observe "ann" "annihilates" [("map_family", ref "Smooth"), ("spectrum", ref "S"), ("element", .polynomial tMinus2)],
  observe "entry" "action_entry" [("map_family", ref "Smooth"), ("spectrum", ref "S"),
    ("element", .polynomial (c "t")), ("row", .coordinate "e1"), ("column", .coordinate "e2")],
  observe "on" "on_branch" [("map_family", ref "Smooth"), ("line", ref "Line"), ("branch", ref "B")],
  observe "dlam" "branch_differential" [("map_family", ref "Smooth"), ("cotangent", ref "Cotangent"),
    ("line", ref "Line"), ("branch", ref "B")],
  observe "proj" "branch_projector" [("map_family", ref "Smooth"), ("line", ref "Line"), ("branch", ref "B"),
    ("row", .coordinate "e2"), ("column", .coordinate "e1")]]

open AlgebraRuntime in
#eval check "each observation embeds the declarations it names, its element and its basis indices"
  (let env := lowered (stage5 ++ sourceObservations);
    bindingIn env "ann" == some (.annihilates (sid "Smooth") spectrumRef (Poly.sub t3 (Poly.const 3 2))) &&
      bindingIn env "entry" == some (.actionEntry (sid "Smooth") spectrumRef t3 0 1) &&
      bindingIn env "on" == some (.onBranch (sid "Smooth") (sid "Line") branchRef) &&
      bindingIn env "dlam" == some (.branchDifferential (sid "Smooth") (sid "Cotangent") (sid "Line") branchRef) &&
      bindingIn env "proj" == some (.branchProjector (sid "Smooth") (sid "Line") branchRef 1 0))

private def observationRejections : List (String × Source.Declaration × String × String) := [
  ("an unknown row", observe "bad" "action_entry" [("map_family", ref "Smooth"), ("spectrum", ref "S"),
      ("element", .polynomial (c "t")), ("row", .coordinate "e3"), ("column", .coordinate "e2")], "E_SPECTRAL",
    "`e3` is not a basis vector of the free module `spectral::V` of `action_entry`, whose basis is e1, e2"),
  ("an unknown column", observe "bad" "branch_projector" [("map_family", ref "Smooth"), ("line", ref "Line"),
      ("branch", ref "B"), ("row", .coordinate "e1"), ("column", .coordinate "x")], "E_SPECTRAL",
    "`x` is not a basis vector of the free module `spectral::V` of `branch_projector`"),
  ("an unknown coordinate", observe "bad" "annihilates" [("map_family", ref "Smooth"), ("spectrum", ref "S"),
      ("element", .polynomial (c "z"))], "E_AFFINE_COORDINATE", "unknown coordinate z"),
  ("a branch for a spectrum", observe "bad" "annihilates" [("map_family", ref "Smooth"), ("spectrum", ref "B"),
      ("element", .polynomial (c "t"))], "E_SPECTRAL",
    "the spectrum of `annihilates` must be a spectrum, but `spectral::B` is not a spectrum declaration"),
  ("a spectrum for a branch", observe "bad" "on_branch" [("map_family", ref "Smooth"), ("line", ref "Line"),
      ("branch", ref "S")], "E_SPECTRAL",
    "the branch of `on_branch` must be a branch, but `spectral::S` is not a branch declaration")]

#eval show IO Unit from do
  for (label, d, expected, text) in observationRejections do
    check s!"{label}: rejected with {expected} ({lowerCode (stage5 ++ [d])}: {lowerMessage (stage5 ++ [d])})"
      (lowerRejects (stage5 ++ [d]) expected text)

end VastitasKernel.Indexed.SpectralDeclarationRegression
