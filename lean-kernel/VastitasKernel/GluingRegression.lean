import VastitasKernel.IndexedSourceChecker
import VastitasKernel.RegressionSupport

/-! Gluing two charts in the Zariski and the smooth site (Stage 7, #878),
through the actual common source checker: glued objects, covers, separation,
manifold and projective claims, and the rejection of every forged or
mismatched part. These are executable regressions, not proofs. -/
namespace VastitasKernel.Indexed.GluingRegression

open AlgebraRuntime

private def pkg : Namespace.PackageId := ⟨"/gluing/Vastitas.toml", "gluing", "0.1.0"⟩
private def id (name : String) : DeclId := ⟨⟨pkg, []⟩, name⟩
private def path (name : String) : Source.Path := ⟨[name], {}⟩
private def decl (name : String) (body : Source.Body) : Source.Declaration := ⟨name, body, true, {}⟩
private def c (name : String) : Source.PolyExpr := .coordinate name
private def n (value : Nat) : Source.PolyExpr := .natural value
private def affine (name : String) (generators : List String) (base : Option String := none) :
    Source.Declaration :=
  decl name (.affine (path "AffineQQ") generators [] (base.map path) [])
private def localize (name object : String) (element : Source.PolyExpr) (inverse : String)
    (implementation := "AffineQQ") : Source.Declaration :=
  decl name (.affineLocalization (path implementation) (path object) element inverse)
private def space (name : String) (coordinates : List String) : Source.Declaration :=
  decl name (.smoothAffine (path "SmoothR") coordinates.length coordinates)
private def glued (name implementation : String) (opens : List String)
    (forward backward : List (String × Source.PolyExpr)) : Source.Declaration :=
  decl name (.glued (path implementation) (opens.map path) forward backward)
private def cover (name object : String) (opens : List String) (coefficients : List Source.PolyExpr) :
    Source.Declaration :=
  decl name (.cover (path object) (opens.map path) coefficients)
private def chart (name dehomogenized : String) (image : Source.PolyExpr)
    (inverse : List (String × Source.PolyExpr)) : Source.SourceChart :=
  ⟨path name, dehomogenized, image, inverse⟩
private def projective (name glued : String) (charts : List Source.SourceChart)
    (homogeneous : List String := ["s", "t"]) : Source.Declaration :=
  decl name (.projective (path glued) homogeneous charts)

/-- The two charts of ℙ¹ and of ℝP¹ (`y = 1/x`), their doubled-origin
counterparts (`y = x`), and a cover of the line. -/
private def declarations : List Source.Declaration := [
  decl "QQ" .marker,
  decl "AffineQQ" (.implementation (path "QQ") (.presentedAffine .rational) []),
  affine "SpecQQ" [],
  affine "L1" ["x"] "SpecQQ",
  affine "L2" ["y"] "SpecQQ",
  localize "U1" "L1" (c "x") "xi",
  localize "U2" "L2" (c "y") "yi",
  glued "P" "AffineQQ" ["U1", "U2"] [("y", c "xi"), ("yi", c "x")] [("x", c "yi"), ("xi", c "y")],
  localize "V1" "L1" (c "x") "a",
  localize "V2" "L2" (c "y") "b",
  glued "Doubled" "AffineQQ" ["V1", "V2"] [("y", c "x"), ("b", c "a")] [("x", c "y"), ("a", c "b")],
  affine "Line" ["t"] "SpecQQ",
  localize "Dt" "Line" (c "t") "u",
  localize "Dmt" "Line" (.sum [n 1, .neg (c "t")]) "w",
  decl "CInfReal" .marker,
  decl "SmoothR" (.implementation (path "CInfReal") .smoothAffine []),
  space "M1" ["x"],
  space "M2" ["y"],
  localize "W1" "M1" (c "x") "u" "SmoothR",
  localize "W2" "M2" (c "y") "v" "SmoothR",
  glued "RP1" "SmoothR" ["W1", "W2"] [("y", c "u"), ("v", c "x")] [("x", c "v"), ("u", c "y")],
  localize "Z1" "M1" (c "x") "p" "SmoothR",
  localize "Z2" "M2" (c "y") "q" "SmoothR",
  glued "SmoothDoubled" "SmoothR" ["Z1", "Z2"] [("y", c "x"), ("q", c "p")] [("x", c "y"), ("p", c "q")] ]

private def program (ds := declarations) : Source.Program := {
  file := "gluing", root := pkg.source,
  packages := [⟨pkg, [], [{
    module := {path := [], isPublic := true, imports := [], functions := [], generics := [], methods := [], span := {}}
    declarations := ds }], none⟩] }

private def check := RegressionSupport.check "gluing regression failed"

private def with' (extra : List Source.Declaration) : Source.Program := program (declarations ++ extra)

private def code (p : Source.Program) : String :=
  match Source.checkDeclarations p with
  | .ok _ => "accepted"
  | .error e => e.code

private def message (p : Source.Program) : String :=
  match Source.checkDeclarations p with
  | .ok _ => ""
  | .error e => e.message

private def mentions (p : Source.Program) (text : String) : Bool := ((message p).splitOn text).length > 1

private def resolved (p : Source.Program := program) : Option Core.Declarations :=
  match Source.checkDeclarations p with
  | .ok checked => some checked.resolved.declarations
  | .error _ => none

private def separated (name glued inverse : String) (witness : Source.PolyExpr) : Source.Declaration :=
  decl name (.separated (path glued) inverse witness)
private def manifold (name glued : String) (dimension : Nat) (inverse : String) (witness : Source.PolyExpr) :
    Source.Declaration :=
  decl name (.manifold (path glued) dimension inverse witness)

private def standard : List Source.SourceChart :=
  [chart "L1" "s" (c "x") [("x", c "t")], chart "L2" "t" (c "y") [("y", c "s")]]

-- Glued objects in both sites.
#eval check "ℙ¹, the doubled origin, ℝP¹ and the smooth doubled origin are glued objects"
  (code program == "accepted")
#eval check "the stored transition of ℙ¹ gives y and its inverse in the ring of U1"
  ((resolved.bind fun env => lookup env.indexed (id "P")) matches
    some (.glued _ _ _ [[⟨[0, 1], 1⟩], [⟨[1, 0], 1⟩]] _))
#eval check "a smooth open is stored with its derived presentation"
  ((resolved.bind fun env => smoothOpenData? env.indexed (id "W1")).map (·.generators) == some ["x", "u"])
#eval check "a third open is rejected"
  (code (with' [glued "Three" "AffineQQ" ["U1", "U2", "V1"] [] []]) == "E_GLUE")
#eval check "a single open is rejected"
  (code (with' [glued "One" "AffineQQ" ["U1"] [] []]) == "E_GLUE")
#eval check "two opens of one chart are rejected"
  (code (with' [glued "Same" "AffineQQ" ["U1", "V1"] [("x", c "xi"), ("a", c "x")] [("x", c "a"), ("xi", c "x")]])
    == "E_GLUE")
#eval check "a transition that is not invertible is rejected"
  (code (with' [glued "Bad" "AffineQQ" ["U1", "U2"] [("y", .product [n 2, c "xi"]), ("yi", c "x")]
    [("x", c "yi"), ("xi", c "y")]]) == "E_GLUE")
#eval check "a transition that breaks the relations is rejected"
  (code (with' [glued "Bad" "AffineQQ" ["U1", "U2"] [("y", c "x"), ("yi", c "x")]
    [("x", c "yi"), ("xi", c "y")]]) == "E_GLUE")
#eval check "a missing image is a coordinate error"
  (code (with' [glued "Bad" "AffineQQ" ["U1", "U2"] [("y", c "xi")] [("x", c "yi"), ("xi", c "y")]])
    == "E_AFFINE_COORDINATE")
#eval check "a chart is not an open"
  (code (with' [glued "Bad" "AffineQQ" ["L1", "U2"] [("y", c "x"), ("yi", c "x")] [("x", c "y")]]) == "E_GLUE")

-- The sites are never mixed.
#eval check "a Zariski gluing of smooth opens is rejected"
  (code (with' [glued "Mixed" "AffineQQ" ["W1", "W2"] [("y", c "u"), ("v", c "x")] [("x", c "v"), ("u", c "y")]])
    == "E_GLUE")
#eval check "a smooth gluing of principal opens is rejected"
  (code (with' [glued "Mixed" "SmoothR" ["U1", "U2"] [("y", c "xi"), ("yi", c "x")] [("x", c "yi"), ("xi", c "y")]])
    == "E_GLUE")
#eval check "the site message names the smooth site"
  (mentions (with' [glued "Mixed" "SmoothR" ["U1", "U2"] [("y", c "xi"), ("yi", c "x")]
    [("x", c "yi"), ("xi", c "y")]]) "smooth site")
#eval check "a principal open under a smooth implementation of a presented object stays E_SMOOTH"
  (code (with' [localize "Bad" "L1" (c "x") "k" "SmoothR"]) == "E_SMOOTH")

-- Separation.
#eval check "ℙ¹ is separated with the witness y"
  (code (with' [separated "sep" "P" "xi" (c "L2::y")]) == "accepted")
#eval check "the doubled origin is not separated"
  (code (with' [separated "sep" "Doubled" "a" (c "L2::y")]) == "E_GLUE")
#eval check "the doubled origin is not separated with x either"
  (code (with' [separated "sep" "Doubled" "a" (c "L1::x")]) == "E_GLUE")
#eval check "a witness of another coordinate is rejected"
  (code (with' [separated "sep" "P" "yi" (c "L2::y")]) == "E_GLUE")
#eval check "a smooth gluing has no separation claim"
  (code (with' [separated "sep" "RP1" "u" (c "M2::y")]) == "E_GLUE")
#eval check "the identity gluing along D(x² + 1) is not separated"
  (code (with' [localize "E1" "L1" (.sum [.pow (c "x") 2, n 1]) "e",
    localize "E2" "L2" (.sum [.pow (c "y") 2, n 1]) "f",
    glued "Twice" "AffineQQ" ["E1", "E2"] [("y", c "x"), ("f", c "e")] [("x", c "y"), ("e", c "f")],
    separated "sep" "Twice" "e" (c "L2::y")]) == "E_GLUE")

-- Manifold evidence.
#eval check "ℝP¹ is a manifold of dimension 1"
  (code (with' [manifold "m" "RP1" 1 "u" (c "M2::y")]) == "accepted")
#eval check "a wrong dimension is rejected"
  (code (with' [manifold "m" "RP1" 2 "u" (c "M2::y")]) == "E_GLUE")
#eval check "the smooth doubled origin is not a manifold"
  (code (with' [manifold "m" "SmoothDoubled" 1 "p" (c "M2::y")]) == "E_GLUE")
#eval check "a Zariski gluing has no manifold claim"
  (code (with' [manifold "m" "P" 1 "xi" (c "L2::y")]) == "E_GLUE")

-- The projective line.
#eval check "ℙ¹ is the projective line"
  (code (with' [projective "h" "P" standard]) == "accepted")
#eval check "chart entries in either order are accepted and stored in the order of the opens"
  ((resolved (with' [projective "h" "P" standard.reverse])).bind (fun env => lookup env.indexed (id "h"))
    matches some (.projective _ _ [⟨_, 0, _, _⟩, ⟨_, 1, _, _⟩]))
#eval check "two charts on one standard chart are rejected"
  (code (with' [projective "h" "P" [chart "L1" "s" (c "x") [("x", c "t")], chart "L2" "s" (c "y") [("y", c "t")]]])
    == "E_GLUE")
#eval check "a chart map without an inverse is rejected"
  (code (with' [projective "h" "P" [chart "L1" "s" (.pow (c "x") 2) [("x", c "t")],
    chart "L2" "t" (c "y") [("y", c "s")]]]) == "E_GLUE")
#eval check "an open that is not the preimage of the other standard chart is rejected"
  (code (with' [projective "h" "P" [chart "L1" "s" (.sum [c "x", n 1]) [("x", .sum [c "t", .neg (n 1)])],
    chart "L2" "t" (c "y") [("y", c "s")]]]) == "E_GLUE")
#eval check "the doubled origin is not the projective line"
  (code (with' [projective "h" "Doubled" standard]) == "E_GLUE")
#eval check "a missing chart entry is rejected"
  (code (with' [projective "h" "P" [chart "L1" "s" (c "x") [("x", c "t")]]]) == "E_GLUE")
#eval check "equal homogeneous coordinates are rejected"
  (code (with' [projective "h" "P" standard ["s", "s"]]) == "E_GLUE")
#eval check "the smooth gluing has no projective claim"
  (code (with' [projective "h" "RP1" [chart "M1" "s" (c "x") [("x", c "t")], chart "M2" "t" (c "y") [("y", c "s")]]])
    == "E_GLUE")

-- Covers.
#eval check "D(t) and D(1 − t) cover the line"
  (code (with' [cover "c" "Line" ["Dt", "Dmt"] [n 1, n 1]]) == "accepted")
#eval check "a wrong coefficient is rejected"
  (code (with' [cover "c" "Line" ["Dt", "Dmt"] [n 1, n 2]]) == "E_GLUE")
#eval check "D(t² + 1) is no Zariski cover of the line"
  (code (with' [localize "Dsq" "Line" (.sum [.pow (c "t") 2, n 1]) "k", cover "c" "Line" ["Dsq"] [n 1]])
    == "E_GLUE")
#eval check "an open of another object is rejected"
  (code (with' [cover "c" "Line" ["Dt", "U1"] [n 1, n 1]]) == "E_GLUE")
#eval check "an open listed twice is rejected"
  (code (with' [cover "c" "Line" ["Dt", "Dt"] [n 1, n 1]]) == "E_GLUE")
#eval check "a smooth cover with a unit-ideal witness is accepted"
  (code (with' [localize "Wm" "M1" (.sum [n 1, .neg (c "x")]) "r" "SmoothR",
    cover "c" "M1" ["W1", "Wm"] [n 1, n 1]]) == "accepted")
#eval check "a Zariski open in a smooth cover is rejected"
  (code (with' [cover "c" "M1" ["W1", "U1"] [n 1, n 1]]) == "E_GLUE")

end VastitasKernel.Indexed.GluingRegression
