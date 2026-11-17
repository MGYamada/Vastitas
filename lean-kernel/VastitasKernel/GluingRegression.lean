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
#eval check "doubling the transition breaks the relation of the other open"
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

-- The rules that the acceptance package does not reach.
#eval check "a transition that respects the relations but is not inverse to its inverse is rejected"
  (code (with' [glued "Bad" "AffineQQ" ["U1", "U2"] [("y", c "xi"), ("yi", c "x")]
    [("x", .neg (c "yi")), ("xi", .neg (c "y"))]]) == "E_GLUE")
#eval check "the not-inverse message says so"
  (mentions (with' [glued "Bad" "AffineQQ" ["U1", "U2"] [("y", c "xi"), ("yi", c "x")]
    [("x", .neg (c "yi")), ("xi", .neg (c "y"))]]) "not mutually inverse")
#eval check "charts over different bases are rejected"
  (code (with' [affine "Other" [], affine "L3" ["z"] "Other", localize "U3" "L3" (c "z") "zi",
    glued "Bad" "AffineQQ" ["U1", "U3"] [("z", c "xi"), ("zi", c "x")] [("x", c "zi"), ("xi", c "z")]])
    == "E_GLUE")
-- Over a base with a coordinate, the transition must commute with the structure maps.
private def overBase : List Source.Declaration := [
  decl "S" (.affine (path "AffineQQ") ["t"] [] none []),
  decl "A1" (.affine (path "AffineQQ") ["t", "x"] [] (some (path "S")) [("t", c "t")]),
  decl "A2" (.affine (path "AffineQQ") ["t", "y"] [] (some (path "S")) [("t", c "t")]),
  localize "O1" "A1" (c "x") "xi",
  localize "O2" "A2" (c "y") "yi" ]
#eval check "a family of lines over a base glues fibrewise"
  (code (with' (overBase ++ [glued "Family" "AffineQQ" ["O1", "O2"]
    [("t", c "t"), ("y", c "xi"), ("yi", c "x")] [("t", c "t"), ("x", c "yi"), ("xi", c "y")]])) == "accepted")
#eval check "a transition that moves the base is rejected"
  (code (with' (overBase ++ [glued "Shifted" "AffineQQ" ["O1", "O2"]
    [("t", .sum [c "t", n 1]), ("y", c "xi"), ("yi", c "x")]
    [("t", .sum [c "t", .neg (n 1)]), ("x", c "yi"), ("xi", c "y")]])) == "E_GLUE")
#eval check "a cover with more opens than the limit is E_LIMIT"
  (code (with' ((List.range 33).map (fun k => localize s!"C{k}" "Line" (.sum [c "t", n (k + 1)]) "r") ++
    [cover "big" "Line" ((List.range 33).map (s!"C{·}")) ((List.range 33).map fun _ => n 1)])) == "E_LIMIT")
#eval check "the message of a single open is singular"
  (mentions (with' [glued "One" "AffineQQ" ["U1"] [] []]) "1 open is given")

#eval check "a cover counts its coefficients before it evaluates them"
  (code (with' [cover "c" "Line" ["Dt", "Dmt"] ((List.range 33).map fun _ => n 1)]) == "E_AFFINE_COORDINATE")
#eval check "a gluing of one open names no cocycle"
  (!mentions (with' [glued "One" "AffineQQ" ["U1"] [] []]) "cocycle")
#eval check "a gluing of three opens names the cocycle checks"
  (mentions (with' [glued "Three" "AffineQQ" ["U1", "U2", "V1"] [] []]) "cocycle")

/-! ### The audit on stored data

Elaboration runs the actions of the audit before the audit does, so the
source cases above cannot show that the audit itself rejects. These cases
take the elaborated environment of the program with every kind of Stage 7
declaration, change one stored declaration, and run `validEnvironment`. -/

private def full : Source.Program := with' [
  separated "sep" "P" "xi" (c "L2::y"),
  projective "line" "P" standard,
  cover "halves" "Line" ["Dt", "Dmt"] [n 1, n 1],
  manifold "circle" "RP1" 1 "u" (c "M2::y")]

private def stored : Environment := ((resolved full).map (·.indexed)).getD []

private def stored? (name : String) : Option Declaration := (stored.find? (·.id.name == name)).map (·.declaration)

private def tamper (name : String) (change : Declaration → Declaration) : Environment :=
  stored.map fun entry => if entry.id.name == name then ⟨entry.id, change entry.declaration⟩ else entry

private def rejects (label : String) (env : Environment) : IO Unit :=
  check s!"the audit rejects {label}" (!validEnvironment env)

#eval check "the audit accepts the elaborated program" ((resolved full).isSome && validEnvironment stored)

-- Glued objects.
#eval rejects "a transition that breaks the relations"
  (tamper "P" fun | .glued i a b _ backward => .glued i a b [Poly.var 2 0, Poly.var 2 0] backward | d => d)
private def negated : Declaration → Declaration
  | .glued i a b _ backward => .glued i a b [Poly.neg (Poly.var 2 1), Poly.neg (Poly.var 2 0)] backward
  | d => d
#eval rejects "a transition that is not inverse to its inverse" (tamper "P" negated)
#eval rejects "a second open of the same chart"
  (tamper "P" fun | .glued i a _ forward backward => .glued i a (id "V1") forward backward | d => d)
#eval rejects "a Zariski gluing under a smooth implementation"
  (tamper "P" fun | .glued _ a b forward backward => .glued (id "SmoothR") a b forward backward | d => d)
#eval rejects "a smooth gluing under a presented implementation"
  (tamper "RP1" fun | .glued _ a b forward backward => .glued (id "AffineQQ") a b forward backward | d => d)
#eval rejects "smooth opens in a Zariski gluing"
  (tamper "P" fun
    | .glued i _ _ _ _ => match stored? "RP1" with
      | some (.glued _ a b forward backward) => .glued i a b forward backward
      | _ => .marker
    | d => d)
private def unreduced : Declaration → Declaration
  | .glued i a b forward backward =>
    .glued i a b (Poly.add (Poly.var 2 1) (Poly.sub (Poly.mul (Poly.var 2 0) (Poly.var 2 1)) (Poly.one 2)) ::
      forward.drop 1) backward
  | d => d
#eval rejects "an image that is not a normal form" (tamper "P" unreduced)
#eval rejects "an extra image"
  (tamper "P" fun | .glued i a b forward backward => .glued i a b (forward ++ [Poly.var 2 0]) backward | d => d)
-- Separation and manifold claims.
#eval rejects "a separation witness of the first chart's coordinate"
  (tamper "sep" fun | .separated glued _ => .separated glued (Poly.var 2 0) | d => d)
#eval rejects "a separation claim on the doubled origin"
  (tamper "sep" fun | .separated _ witness => .separated (id "Doubled") witness | d => d)
#eval rejects "a separation claim on a smooth gluing"
  (tamper "sep" fun | .separated _ witness => .separated (id "RP1") witness | d => d)
#eval rejects "a separation witness in too many coordinates"
  (tamper "sep" fun | .separated glued _ => .separated glued (Poly.var 3 2) | d => d)
#eval rejects "a manifold claim of the wrong dimension"
  (tamper "circle" fun | .manifold glued _ witness => .manifold glued 2 witness | d => d)
#eval rejects "a manifold claim on a Zariski gluing"
  (tamper "circle" fun | .manifold _ dimension witness => .manifold (id "P") dimension witness | d => d)
#eval rejects "a manifold claim on the smooth doubled origin"
  (tamper "circle" fun | .manifold _ dimension witness => .manifold (id "SmoothDoubled") dimension witness | d => d)
-- Projective claims.
#eval rejects "chart entries out of the order of the opens"
  (tamper "line" fun | .projective g h [a, b] => .projective g h [b, a] | d => d)
#eval rejects "two entries on one standard chart"
  (tamper "line" fun | .projective g h [a, b] => .projective g h [a, { b with dehomogenized := 0 }] | d => d)
#eval rejects "a homogeneous coordinate index out of range"
  (tamper "line" fun | .projective g h [a, b] => .projective g h [a, { b with dehomogenized := 2 }] | d => d)
#eval rejects "a chart image whose inverse no longer matches"
  (tamper "line" fun | .projective g h [a, b] => .projective g h [{ a with image := Poly.scale 2 (Poly.var 1 0) }, b] | d => d)
#eval rejects "a projective claim on the doubled origin"
  (tamper "line" fun | .projective _ h charts => .projective (id "Doubled") h charts | d => d)
#eval rejects "one homogeneous coordinate"
  (tamper "line" fun | .projective g _ charts => .projective g ["s"] charts | d => d)
#eval rejects "three chart entries"
  (tamper "line" fun | .projective g h charts => .projective g h (charts ++ charts.take 1) | d => d)
-- Covers.
#eval rejects "cover coefficients that do not combine to 1"
  (tamper "halves" fun | .cover o opens _ => .cover o opens [Poly.scale 2 (Poly.one 1), Poly.one 1] | d => d)
#eval rejects "a cover that misses part of the line"
  (tamper "halves" fun | .cover o _ _ => .cover o [id "Dt"] [Poly.one 1] | d => d)
#eval rejects "an open listed twice"
  (tamper "halves" fun | .cover o _ _ => .cover o [id "Dt", id "Dt"] [Poly.one 1, Poly.one 1] | d => d)
#eval rejects "a cover of another object"
  (tamper "halves" fun | .cover _ opens coefficients => .cover (id "M1") opens coefficients | d => d)
#eval rejects "coefficients in too many coordinates"
  (tamper "halves" fun | .cover o opens _ => .cover o opens [Poly.one 2, Poly.one 2] | d => d)
-- Smooth opens.
#eval rejects "a smooth open whose element differs from its relation"
  (tamper "W1" fun | .smoothOpen i data => .smoothOpen i { data with construction := match data.construction with
      | .localization o _ u r => .localization o (Poly.one 1) u r | k => k } | d => d)
#eval rejects "a smooth open under a presented implementation"
  (tamper "W1" fun | .smoothOpen _ data => .smoothOpen (id "AffineQQ") data | d => d)
#eval rejects "a smooth open stored as a presented object"
  (tamper "W1" fun | .smoothOpen i data => .affine i data | d => d)
#eval rejects "a principal open stored as a smooth open"
  (tamper "U1" fun | .affine i data => .smoothOpen i data | d => d)

end VastitasKernel.Indexed.GluingRegression
