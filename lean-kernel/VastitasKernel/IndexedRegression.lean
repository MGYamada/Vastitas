import VastitasKernel.FiniteHom
import VastitasKernel.IndexedTypeAudit
import VastitasKernel.IndexedAudit
import VastitasKernel.RegressionSupport

namespace VastitasKernel.Indexed.Regression
private def id (name : String) : DeclId :=
  ⟨⟨⟨"/indexed/Vastitas.toml", "indexed", "0.1.0"⟩, []⟩, name⟩
private def entry (name : String) (declaration : Declaration) : Entry := ⟨id name, declaration⟩
private def env : Environment := [
  entry "Coefficient" .marker, entry "OtherCoefficient" .marker,
  entry "Grid" (.implementation (id "Coefficient") .affineDescriptor [.origin, .dimension]),
  entry "SparseGrid" (.implementation (id "Coefficient") .affineDescriptor []),
  entry "OtherGrid" (.implementation (id "OtherCoefficient") .affineDescriptor [.dimension]),
  entry "Container" (.classification [] [id "Grid", id "SparseGrid", id "OtherGrid"]),
  entry "DenseContainer" (.classification [id "Container"] [id "Grid"]),
  entry "Canonical" (.global (id "Grid")),
  entry "Position" (.family ⟨[.object (id "Container"), .object (id "Container")],
    [.sameBase 0 1], .point⟩),
  entry "Self" (.family ⟨[.object (id "Container"), .object (id "Container")],
    [.sameObject 0 1], .token⟩),
  entry "VectorShape" (.family ⟨[.object (id "Container"), .marker, .natural], [.over 0 1], .token⟩),
  entry "DenseOnly" (.family ⟨[.object (id "DenseContainer")], [], .token⟩) ]
private def x : ObjectRef := .local ⟨id "Container", id "Coefficient"⟩ 0
private def y : ObjectRef := .local ⟨id "Container", id "Coefficient"⟩ 1
private def z : ObjectRef := .local ⟨id "Container", id "OtherCoefficient"⟩ 2
private def app (family : String) (indices : List Index) : Application := ⟨id family, indices⟩
private def replace (name : String) (declaration : Declaration) : Environment :=
  env.map fun e => if e.id == id name then { e with declaration } else e
private def check := RegressionSupport.check "indexed regression failed"

#eval check "declarations and non-geometric families" (validEnvironment env)
#eval check "order independence" (validEnvironment env.reverse)
#eval check "duplicate identity" (!validEnvironment (env ++ [entry "Container" .marker]))
#eval check "same spelling in a different module stays distinct" (
  let foreignId := { id "Coefficient" with scope := { (id "Coefficient").scope with path := ["other"] } }
  validEnvironment (env ++ [⟨foreignId, .marker⟩]) &&
    !validEnvironment (replace "Grid" (.implementation foreignId .affineDescriptor [])))
#eval check "unknown marker" (!validEnvironment (replace "Grid"
  (.implementation (id "missing") .affineDescriptor [])))
#eval check "wrong marker kind" (!validEnvironment (replace "Grid"
  (.implementation (id "Container") .affineDescriptor [])))
#eval check "unknown class member" (!validEnvironment (replace "Container" (.classification [] [id "absent"])))
#eval check "empty class" (!validEnvironment (replace "Container" (.classification [] [])))
#eval check "invalid parent kind" (!validEnvironment (replace "DenseContainer"
  (.classification [id "Grid"] [id "Grid"])))
#eval check "self cycle" (!validEnvironment (replace "Container"
  (.classification [id "Container"] [id "Grid", id "SparseGrid", id "OtherGrid"])))
#eval check "cycle" (!validEnvironment (replace "Container" (.classification [id "DenseContainer"] [id "Grid"])))
#eval check "subclass domain cannot expand parent" (!validEnvironment
  (env.map fun e => if e.id == id "Container" then
    { e with declaration := .classification [] [id "SparseGrid"] } else e))
#eval check "global must bind an implementation" (!validEnvironment (replace "Canonical" (.global (id "Container"))))
#eval check "sealed point representation requires base constraint" (!validEnvironment
  (replace "Position" (.family ⟨[.object (id "Container"), .object (id "Container")], [], .point⟩)))
#eval check "constraint positions are kind checked" (!validEnvironment
  (replace "Self" (.family ⟨[.marker], [.sameObject 0 0], .token⟩)))
#eval check "constraint positions are bounded" (!validEnvironment
  (replace "Self" (.family ⟨[.object (id "Container")], [.sameObject 0 1], .token⟩)))
#eval check "capabilities cannot be duplicated" (!validEnvironment
  (replace "Grid" (.implementation (id "Coefficient") .affineDescriptor [.origin, .origin])))

#eval check "general test object" (validApplication env (app "Position" [.object x, .object y]))
#eval check "canonical object" (validApplication env (app "Position" [.object x, .object (.global (id "Canonical"))]))
#eval check "a marker is not an object" (!validApplication env (app "Position" [.object x, .marker (id "Coefficient")]))
#eval check "base mismatch" (!validApplication env (app "Position" [.object x, .object z]))
#eval check "exact object equality" (validApplication env (app "Self" [.object x, .object x]) &&
  !validApplication env (app "Self" [.object x, .object y]))
#eval check "non-geometric natural index" (validApplication env (app "VectorShape"
  [.object x, .marker (id "Coefficient"), .natural 12]))
#eval check "forged base metadata" (!validApplication env (app "VectorShape"
  [.object x, .marker (id "OtherCoefficient"), .natural 12]))
#eval check "wrong index arity" (!validApplication env (app "Position" [.object x]) &&
  !validApplication env (app "Position" [.object x, .object y, .object x]))
#eval check "unknown family" (!validApplication env (app "Scheme" []))
#eval check "empty object implementation set" (!validApplication env (app "Self"
  [.object (.local ⟨id "Grid", id "OtherCoefficient"⟩ 0), .object x]))
#eval check "entire finite domain required" (!validApplication env (app "DenseOnly" [.object x]) &&
  validApplication env (app "DenseOnly" [.object (.local ⟨id "Grid", id "Coefficient"⟩ 0)]))
#eval check "token indices cannot hide an escape" (
  let shaped := app "VectorShape" [.object x, .marker (id "Coefficient"), .natural 12]
  decide (shaped.Scoped [x]) && !decide (shaped.Scoped [y]))
#eval check "canonical references cannot be substituted" (
  renameRef [(.global (id "Canonical"), x)] (.global (id "Canonical")) == .global (id "Canonical"))
#eval check "substitution preserves the marker and domain" (
  decide (SubstitutionValid env [(x, y)]) && !decide (SubstitutionValid env [(x, z)]))
#eval check "substitution cannot rewrite a global" (!decide
  (SubstitutionValid env [(.global (id "Canonical"), x)]))
#eval check "substitution cannot duplicate a source" (!decide
  (SubstitutionValid env [(x, y), (x, x)]))
#eval check "actual checked API keeps exact environment" (match checkEnvironment env with
  | .error _ => false
  | .ok checked => (checkApplication checked (app "Self" [.object x, .object x])).isOk &&
    !(checkApplication checked (app "Self" [.object x, .object y])).isOk)
private def renameId (old : DeclId) : DeclId := { old with name := "Renamed_" ++ old.name }
private def renameParameter : Parameter → Parameter
  | .object id => .object (renameId id)
  | .frame family => .frame (renameId family)
  | other => other
private def renameDeclaration : Declaration → Declaration
  | .marker => .marker
  | .finiteCarrier tags => .finiteCarrier tags
  | .finiteTable inputs output rows => .finiteTable (inputs.map renameId) (renameId output) rows
  | .monadSchema => .monadSchema
  | .kleisliSchema kind base => .kleisliSchema kind (renameId base)
  | .finiteKleisli kind schema monad => .finiteKleisli kind (renameId schema) (renameId monad)
  | .finiteMonad schema m => .finiteMonad (renameId schema) (Id.run (m.mapM (pure ∘ renameId)))
  | .isoSchema => .isoSchema
  | .finiteOpposite schema base => .finiteOpposite (renameId schema) (renameId base)
  | .finiteIso schema i => .finiteIso (renameId schema) (Id.run (i.mapM (pure ∘ renameId)))
  | .natTransSchema => .natTransSchema
  | .finiteNatTrans schema n => .finiteNatTrans (renameId schema) (Id.run (n.mapM (pure ∘ renameId)))
  | .functorSchema => .functorSchema
  | .finiteFunctor schema maps => .finiteFunctor (renameId schema) (Id.run (maps.mapM (pure ∘ renameId)))
  | .categorySchema => .categorySchema
  | .composableTable inputs output src dst rows =>
    .composableTable (inputs.map renameId) (renameId output) (renameId src) (renameId dst) rows
  | .finiteCategory schema graph => .finiteCategory (renameId schema) (Id.run (graph.mapM (pure ∘ renameId)))
  | .implementation marker repr capabilities => .implementation (renameId marker) repr capabilities
  | .classification parents domain => .classification (parents.map renameId) (domain.map renameId)
  | .global implementation => .global (renameId implementation)
  | .family family => .family { family with parameters := family.parameters.map renameParameter }
  | .affine implementation data => .affine (renameId implementation) { data with base := data.base.map renameId }
  | .smoothAffine implementation coordinates => .smoothAffine (renameId implementation) coordinates
  | .metric family object gram => .metric (renameId family) (renameId object) gram
  | .metricEvidence metric evidence => .metricEvidence (renameId metric) evidence
  | .frame family object matrix inverse => .frame (renameId family) (renameId object) matrix inverse
  | .baseDimension => .baseDimension
  | .quantity dimension => .quantity (dimension.map fun (base, exponent) => (renameId base, exponent))
  | .reading family object quantities => .reading (renameId family) (renameId object) (quantities.map renameId)
  | .scale quantity magnitude => .scale (renameId quantity) magnitude
  | .physicalMetric family object metric reading value entries =>
    .physicalMetric (renameId family) (renameId object) (renameId metric) (renameId reading)
      (value.map (·.map fun (base, exponent) => (renameId base, exponent))) (match entries with
        | .euclidean => .euclidean
        | .gram rows => .gram (rows.map (·.map fun monomial =>
            { monomial with factors := monomial.factors.map fun (scale, exponent) => (renameId scale, exponent) }))
        | .normalized scales => .normalized (scales.map renameId))
  | .freeModule family object basis => .freeModule (renameId family) (renameId object) basis
  | .endomorphism family object module rows symmetric =>
    .endomorphism (renameId family) (renameId object) (renameId module) rows symmetric
  | .spectrum family object endomorphism fiber certificate =>
    .spectrum (renameId family) (renameId object) (renameId endomorphism) fiber certificate
  | .branch family object spectrum localize witness exponent quotient =>
    .branch (renameId family) (renameId object) (renameId spectrum) localize witness exponent quotient
  | .transitionAverage family object branch source target numerator denominator certificate =>
    .transitionAverage (renameId family) (renameId object) (renameId branch) source target numerator denominator
      certificate
  | .convention value => .convention value
  | .model family object hamiltonian reading convention prepare observe predicts regime =>
    .model (renameId family) (renameId object) (renameId hamiltonian) (renameId reading) (renameId convention)
      prepare observe (renameId predicts) regime
  | .calibration family object parameters method reference revision =>
    .calibration (renameId family) (renameId object) parameters method reference revision
  | .dataset family object model calibration coverage points =>
    .dataset (renameId family) (renameId object) (renameId model) (renameId calibration) coverage points
  | .comparison family object dataset calibration fingerprint verdict =>
    .comparison (renameId family) (renameId object) (renameId dataset) (renameId calibration) fingerprint verdict
  | .smoothOpen implementation data => .smoothOpen (renameId implementation) { data with base := data.base.map renameId }
  | .glued implementation first second forward backward =>
    .glued (renameId implementation) (renameId first) (renameId second) forward backward
  | .cover object opens coefficients => .cover (renameId object) (opens.map renameId) coefficients
  | .separated glued witness => .separated (renameId glued) witness
  | .manifold glued dimension witness => .manifold (renameId glued) dimension witness
  | .projective glued homogeneous charts =>
    .projective (renameId glued) homogeneous (charts.map fun chart => { chart with chart := renameId chart.chart })
private def renamed : Environment := env.map fun e => ⟨renameId e.id, renameDeclaration e.declaration⟩

private def finiteEnv : Environment := [
  entry "flip" (.finiteTable [id "Bit"] (id "Mirror") [(["one"], "zero"), (["zero"], "one")]),
  entry "Bit" (.finiteCarrier ["zero", "one"]), entry "Mirror" (.finiteCarrier ["zero", "one"]),
  entry "Void" (.finiteCarrier []), entry "constant" (.finiteTable [] (id "Bit") [([], "zero")]),
  entry "never" (.finiteTable [id "Bit", id "Void"] (id "Void") [])]
#eval check "table forward references; constant and empty products" (validEnvironment finiteEnv &&
  FiniteTables.lookupTag finiteEnv (id "constant") [] == some (id "Bit", "zero"))
#eval check "nominal lookup does not exchange equal carriers" (
  FiniteTables.lookupTag finiteEnv (id "flip") [(id "Bit", "one")] == some (id "Mirror", "zero") &&
  (FiniteTables.lookupTag finiteEnv (id "flip") [(id "Mirror", "one")]).isNone)
#eval check "table coverage is exact, not just a matching row count" (
  !FiniteTables.validTable finiteEnv [id "Bit"] (id "Bit") [(["one"], "zero"), (["one"], "one")] &&
  !FiniteTables.validTable finiteEnv [id "Bit"] (id "Bit") [(["one"], "zero"), (["miss"], "one")] &&
  !FiniteTables.validTable finiteEnv [id "Bit"] (id "Bit") [(["one"], "zero"), (["zero"], "miss")] &&
  !FiniteTables.validTable finiteEnv [] (id "Bit") [] &&
  !FiniteTables.validTable finiteEnv [id "Void"] (id "Void") [([], "bad")])
#eval check "preflight does not enumerate a rejected or empty product" (
  let wide := List.replicate 4096 "x"
  (FiniteTables.keys [wide, wide, wide]).isNone &&
    FiniteTables.keys [[], wide, wide, wide, wide, wide] == some [])

private def permutations : List (String × List Nat) :=
  [("p012", [0,1,2]), ("p021", [0,2,1]), ("p102", [1,0,2]), ("p120", [1,2,0]),
   ("p201", [2,0,1]), ("p210", [2,1,0])]
private def s3Rows : List (List String × String) :=
  permutations.flatMap fun (g, gv) => permutations.map fun (f, fv) =>
    let composition := fv.map fun i => gv[i]!
    ([g, f], (permutations.find? (·.2 == composition)).get!.1)
private def s3Fields : GraphFields DeclId := ⟨id "Obj", id "Arr", id "s", id "t", id "ids", id "mul"⟩
private def s3 : Environment := [
  entry "Instance" (.finiteCategory (id "Schema") s3Fields), entry "Schema" .categorySchema,
  entry "Obj" (.finiteCarrier ["o"]), entry "Arr" (.finiteCarrier (permutations.map Prod.fst)),
  entry "s" (.finiteTable [id "Arr"] (id "Obj") (permutations.map fun p => ([p.1], "o"))),
  entry "t" (.finiteTable [id "Arr"] (id "Obj") (permutations.map fun p => ([p.1], "o"))),
  entry "ids" (.finiteTable [id "Obj"] (id "Arr") [(["o"], "p012")]),
  entry "mul" (.composableTable [id "Arr", id "Arr"] (id "Arr") (id "s") (id "t") s3Rows)]
#eval check "the declared order of composition in the accepted noncommutative S3 graph" (
  validEnvironment s3 &&
  match FiniteCategories.graph (FiniteCategories.view s3) (id "Schema") s3Fields with
  | none => false
  | some g => g.composition[["p102", "p021"]]? == some "p120" &&
    g.composition[["p021", "p102"]]? == some "p201")
/-- Inversion fixes the identity and all endpoints but reverses the order of
composition in S3. This distinguishes the functor test from either a bare
graph map or a test of products in only one commutative example. -/
private def s3Functor (arrows : List (List String × String)) : Environment :=
  [entry "F" (.finiteFunctor (id "Functor") ⟨id "Instance", id "Instance", id "onObj", id "onArr"⟩),
   entry "Functor" .functorSchema,
   entry "onObj" (.finiteTable [id "Obj"] (id "Obj") [(["o"],"o")]),
   entry "onArr" (.finiteTable [id "Arr"] (id "Arr") arrows)] ++ s3

#eval check "covariant identity and contravariant inversion on S3" (
  let identity := permutations.map fun (f, _) => ([f], f)
  let inverse := permutations.map fun (f, p) =>
    let back := [0,1,2].map fun i => p.idxOf i
    ([f], (permutations.find? (·.2 == back)).get!.1)
  validEnvironment (s3Functor identity) && !validEnvironment (s3Functor inverse))

/-- Conjugation by a three-cycle has a noncentral natural transformation
from the identity functor. Its inverse satisfies the opposite orientation
instead, with both component endpoints still correct. -/
private def s3Transformation (component : String) : Environment :=
  let rows := Std.HashMap.ofList s3Rows
  let product (a b : String) := rows[[a, b]]!
  let conjugation := permutations.map fun (a, _) => ([a], product (product "p120" a) "p201")
  [entry "Trans" .natTransSchema,
   entry "E" (.finiteNatTrans (id "Trans") ⟨id "F", id "G", id "eta"⟩),
   entry "G" (.finiteFunctor (id "Functor") ⟨id "Instance", id "Instance", id "onObj", id "conj"⟩),
   entry "conj" (.finiteTable [id "Arr"] (id "Arr") conjugation),
   entry "eta" (.finiteTable [id "Obj"] (id "Arr") [(["o"],component)])] ++
    s3Functor (permutations.map fun (a, _) => ([a], a))

#eval check "naturality follows the directed square for S3 conjugation" (
  validEnvironment (s3Transformation "p120") && !validEnvironment (s3Transformation "p201"))

/-- Exercise the dependent operation, not an untyped read of the table.
Both directions use exactly the selected model. -/
private def checkedS3 : Bool := Id.run do
  if valid : validEnvironment s3 = true then
    let some m := FiniteHom.select s3 ((Audit.validEnvironment_iff _).mp valid) (id "Instance") | return false
    let some f := FiniteHom.fromTag? m "o" "o" "p102" | return false
    let some g := FiniteHom.fromTag? m "o" "o" "p021" | return false
    let some i := FiniteHom.identity? m "o" | return false
    return ((FiniteHom.compose? f g).map (·.tag) == some "p120") &&
      ((FiniteHom.compose? g f).map (·.tag) == some "p201") &&
      ((FiniteHom.compose? f i).map (·.tag) == some "p102") &&
      (FiniteHom.fromTag? m "x" "o" "p102").isNone && (FiniteHom.fromTag? m "o" "o" "fake").isNone
  else return false

#eval check "typed S3 composition, units, endpoints and unrecognized raw tags" checkedS3

private def chain : Environment := [
  entry "Instance" (.finiteCategory (id "Schema") s3Fields), entry "Schema" .categorySchema,
  entry "Obj" (.finiteCarrier ["lo","hi"]), entry "Arr" (.finiteCarrier ["l","up","r"]),
  entry "s" (.finiteTable [id "Arr"] (id "Obj") [(["l"],"lo"),(["up"],"lo"),(["r"],"hi")]),
  entry "t" (.finiteTable [id "Arr"] (id "Obj") [(["l"],"lo"),(["up"],"hi"),(["r"],"hi")]),
  entry "ids" (.finiteTable [id "Obj"] (id "Arr") [(["lo"],"l"),(["hi"],"r")]),
  entry "mul" (.composableTable [id "Arr", id "Arr"] (id "Arr") (id "s") (id "t")
    [(["l","l"],"l"),(["r","r"],"r"),(["r","up"],"up"),(["up","l"],"up")])]

#eval check "the two-object graph keeps both Hom endpoints on execution" (Id.run do
  if h : validEnvironment chain = true then
    let some m := FiniteHom.select chain ((Audit.validEnvironment_iff _).mp h) (id "Instance") | return false
    let some up := FiniteHom.fromTag? m "lo" "hi" "up" | return false
    let some lo := FiniteHom.identity? m "lo" | return false
    let some hi := FiniteHom.identity? m "hi" | return false
    return ((FiniteHom.compose? up lo).map (·.tag) == some "up") &&
      ((FiniteHom.compose? hi up).map (·.tag) == some "up") &&
      (FiniteHom.fromTag? m "hi" "lo" "up").isNone && (FiniteHom.identity? m "missing").isNone
  else return false)
#eval check "Core independently checks finite Hom literals, sorts and empty fibers" (
  let env : Core.Declarations := ⟨chain, [], []⟩
  let hom := FiniteSort.hom (id "Instance")
  let up := Core.Term.finiteTag (hom "lo" "hi") "up"
  let typed (term : Core.Term) := decide (Core.Typing.HasType env {} [] term)
  typed up && !typed (.finiteTag (hom "hi" "lo") "up") &&
    !typed (.finiteTag (hom "lo" "hi") "l") &&
    !typed (.ascribe (.finite (hom "lo" "hi")) (.finiteTag (id "Arr") "up")) &&
    !typed (.ascribe (.finite (hom "lo" "hi")) (.natural 0)) &&
    decide ((Core.DataType.finite (hom "hi" "lo")).Valid env) &&
    !decide ((Core.DataType.finite (hom "bad" "lo")).Valid env))

/-- Closure on lo < hi maps the nonidentity Hom(lo,hi) to Hom(hi,hi).
The second category has literally the same graph, but a different owner. -/
private def closureMonad : Environment :=
  [entry "Copy" (.finiteCategory (id "Schema") s3Fields),
   entry "Functor" .functorSchema, entry "NatTrans" .natTransSchema, entry "Monad" .monadSchema,
   entry "I" (.finiteFunctor (id "Functor") ⟨id "Instance",id "Instance",id "iObj",id "iArr"⟩),
   entry "T" (.finiteFunctor (id "Functor") ⟨id "Instance",id "Instance",id "tObj",id "tArr"⟩),
   entry "E" (.finiteNatTrans (id "NatTrans") ⟨id "I",id "T",id "eta"⟩),
   entry "U" (.finiteNatTrans (id "NatTrans") ⟨id "T",id "T",id "mu"⟩),
   entry "M" (.finiteMonad (id "Monad") ⟨id "Instance",id "T",id "E",id "U"⟩),
   entry "iObj" (.finiteTable [id "Obj"] (id "Obj") [(["lo"],"lo"),(["hi"],"hi")]),
   entry "iArr" (.finiteTable [id "Arr"] (id "Arr") [(["l"],"l"),(["up"],"up"),(["r"],"r")]),
   entry "tObj" (.finiteTable [id "Obj"] (id "Obj") [(["lo"],"hi"),(["hi"],"hi")]),
   entry "tArr" (.finiteTable [id "Arr"] (id "Arr") [(["l"],"r"),(["up"],"r"),(["r"],"r")]),
   entry "eta" (.finiteTable [id "Obj"] (id "Arr") [(["lo"],"up"),(["hi"],"r")]),
   entry "mu" (.finiteTable [id "Obj"] (id "Arr") [(["lo"],"r"),(["hi"],"r")])] ++ chain

#eval check "Kleisli views derive from the exact Monad schema and preserve their kind" (Id.run do
  let schemas := [entry "K" (.kleisliSchema .category (id "Monad")),
    entry "Triple" (.kleisliSchema .triple (id "Monad")), entry "OtherMonad" .monadSchema,
    entry "OtherK" (.kleisliSchema .category (id "OtherMonad"))] ++ closureMonad
  let category := entry "First" (.finiteKleisli .category (id "K") (id "M"))
  let triple := entry "Second" (.finiteKleisli .triple (id "Triple") (id "M"))
  let read := FiniteCategories.view (triple :: category :: schemas)
  return validEnvironment (triple :: category :: schemas) &&
    KleisliViews.selected read .category category.id == some (id "M") &&
    KleisliViews.selected read .triple triple.id == some (id "M") &&
    (KleisliViews.selected read .triple category.id).isNone &&
    (KleisliViews.selected read .category (id "M")).isNone &&
    !validEnvironment (entry "Bad" (.finiteKleisli .triple (id "K") (id "M")) :: schemas) &&
    !validEnvironment (entry "Bad" (.finiteKleisli .category (id "OtherK") (id "M")) :: schemas) &&
    !validEnvironment (entry "Bad" (.finiteKleisli .category (id "K") (id "T")) :: schemas) &&
    !validEnvironment (entry "Bad" (.kleisliSchema .category (id "M")) :: schemas) &&
    !validEnvironment (entry "Bad" (.finiteKleisli .category (id "K") triple.id) :: triple :: schemas))

#eval check "typed Monad arrow lookup verifies its table, nominal category and both images" (Id.run do
  let hom := FiniteSort.hom (id "Instance")
  let start := hom "lo" "hi"
  let to := hom "hi" "hi"
  let site : FiniteLookup := ⟨id "tArr",some (id "M"),[start],to⟩
  let typed (input : FiniteSort) (s : FiniteLookup) := decide <|
    Core.Typing.HasType ⟨closureMonad,[],[]⟩ {} [⟨0,⟨.finite input,none⟩⟩] (.finiteLookup s [0])
  let some plan := site.plan? closureMonad | return false
  let other := FiniteSort.hom (id "Copy") "lo" "hi"
  let empty := hom "hi" "lo"
  let emptySite := {site with inputs := [empty]}
  return validEnvironment closureMonad && typed start site && plan.atKey ["up"] == some "r" &&
    typed empty emptySite && (emptySite.plan? closureMonad).any (·.rows.isEmpty) &&
    !typed start {site with table := id "iArr"} && !typed start {site with category := some (id "T")} &&
    !typed other {site with inputs := [other]} && !typed start {site with output := hom "lo" "hi"} &&
    !typed (.carrier (id "Arr")) {site with inputs := [.carrier (id "Arr")]})

#eval check "coherent library renaming preserves acceptance" (validEnvironment renamed &&
  validApplication renamed ⟨renameId (id "Position"), [
    .object (.local ⟨renameId (id "Container"), renameId (id "Coefficient")⟩ 0),
    .object (.global (renameId (id "Canonical"))) ]⟩)
#eval check "no acceptance from the old spelling after renaming" (
  !validApplication renamed (app "Position" [.object x, .object y]))
#eval check "equal global descriptors do not identify declarations" (
  let extended := env ++ [entry "SecondCanonical" (.global (id "Grid"))]
  validEnvironment extended && !validApplication extended (app "Self" [
    .object (.global (id "Canonical")), .object (.global (id "SecondCanonical"))]))
end VastitasKernel.Indexed.Regression
