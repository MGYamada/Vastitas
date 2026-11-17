import VastitasKernel.IndexedSmoothSource
import VastitasKernel.GluingValidity

set_option autoImplicit false

/-! Source elaboration of the Stage 7 declarations (#878).

`localize(X, f) inverse u` under a `smooth_affine` implementation declares a
smooth open of the smooth object `X`. `elaborateSmoothOpens` derives its
presentation from the free presentation of `X` before any presented object
is elaborated, so the presented elaboration never sees it.

`elaborateGluing` then elaborates, in this order, glued objects and covers,
and the separation, manifold and projective claims that read a glued
object's transition. Polynomial syntax has the bounds of Stage 2. Each
declaration runs the exact action of its audit in `GluingValidity`, so an
elaborated declaration passes its audit. A budget failure is `E_LIMIT`, an
unknown or missing coordinate `E_AFFINE_COORDINATE`, and every other failure
`E_GLUE`, with a message that names the declarations involved. -/
namespace VastitasKernel.Indexed.Source

open AlgebraRuntime AlgebraBasis AlgebraDeclarations GluingDeclarations Indexed.Gluing

private def spanOf (sources : List (DeclId × Span × Body)) (id : DeclId) : Span :=
  ((sources.find? (·.1 == id)).map (·.2.1)).getD {}

private def bodyOf (sources : List (DeclId × Span × Body)) (id : DeclId) : Option Body :=
  (sources.find? (·.1 == id)).map (·.2.2)

def glueProblem {α : Type} (span : Span) (message : String) : Namespace.Result α :=
  Namespace.problem span "E_GLUE" message

/-- A failed gluing action: a budget failure stays `E_LIMIT` and a coordinate
failure `E_AFFINE_COORDINATE`; every other failure is `E_GLUE`. -/
def glueFailure {α : Type} (span : Span) (context : String) (error : AlgebraBasis.Error) :
    Namespace.Result α :=
  match error with
  | .limit _ | .coordinate _ => algebraProblem span error
  | _ => glueProblem span s!"{context}: {error.message}"

/-- Run a gluing action; `context` names the declaration that a failure is about. -/
def runGlue {α : Type} (span : Span) (context : String) (action : Work α) : Namespace.Result α :=
  match run action with
  | .ok value => pure value
  | .error error => glueFailure span context error

/-- Derive the presentation of every smooth open from its smooth object. -/
def elaborateSmoothOpens (sources : List (DeclId × Span × Body)) (env : Core.Declarations) :
    Namespace.Result Core.Declarations := do
  let mut indexed := []
  for entry in env.indexed do
    match entry.declaration with
    | .affine implementation data =>
      match data.construction, smoothImplementation env.indexed implementation with
      | .localization object _ inverse _, true =>
        let span := spanOf sources entry.id
        let some (.smoothAffine objectImplementation coordinates) := lookup env.indexed object
          | smoothProblem span (.smooth <| s!"`localize(…)` under the smooth implementation " ++
              s!"`{Namespace.Owner.qualified implementation}` declares a smooth open of a smooth object, but `{Namespace.Owner.qualified object}` " ++
              "is not a smooth object")
        unless objectImplementation == implementation do
          smoothProblem span (.smooth <| s!"the smooth open has the implementation `{Namespace.Owner.qualified implementation}`, " ++
            s!"but its object `{Namespace.Owner.qualified object}` has the implementation `{Namespace.Owner.qualified objectImplementation}`")
        let some (.affineLocalization _ _ element _) := bodyOf sources entry.id
          | smoothProblem span (.smooth "missing smooth open source")
        let x := freeData coordinates
        let element ← match run (element.evaluate coordinates) with
          | .ok element => pure element
          | .error error => algebraProblem span error
        let presentation := localizationPresentation object x element inverse
        match AlgebraDeclarations.elaborate presentation.generators presentation.relations presentation.base
            presentation.bindings (some x) (.localization object element inverse presentation.relations) with
        | .ok data => indexed := indexed ++ [⟨entry.id, .smoothOpen implementation data⟩]
        | .error error => algebraProblem span error
      | _, _ => indexed := indexed ++ [entry]
    | _ => indexed := indexed ++ [entry]
  pure { env with indexed }

/-- How a message names the kind of a declaration that is not an open. -/
private def openKind (env : Environment) (id : DeclId) : String :=
  match lookup env id with
  | some (.affine _ data) =>
    match data.construction with
    | .localization .. => "a Zariski principal open"
    | _ => "a presented object, not a principal open"
  | some (.smoothOpen ..) => "a smooth open"
  | some (.smoothAffine ..) => "a smooth object, not a smooth open"
  | some (.glued ..) => "a glued object"
  | _ => "not an open of a chart"

private def siteName : Site → String
  | .zariski => "the Zariski site"
  | .smooth => "the smooth site"

/-- The open `id` in `site`, or the diagnostic that says why it is not one. -/
def requireOpen (env : Environment) (span : Span) (site : Site) (implementation id : DeclId) :
    Namespace.Result Open :=
  match open? env site implementation id with
  | some found => pure found
  | none =>
    let wanted := match site with
      | .zariski => "a principal open `localize(X, f)` of a presented object"
      | .smooth => "a smooth open `localize(X, f)` of a smooth object"
    glueProblem span <| s!"`{Namespace.Owner.qualified id}` is {openKind env id}, but {siteName site} of the implementation " ++
      s!"`{Namespace.Owner.qualified implementation}` needs {wanted} of that implementation"

/-- The images of the coordinates `target`, given by name, in the coordinates
`source`, normalized in the ring of `source`. -/
def transitionImages (span : Span) (target source : AffineData) (bindings : List (String × PolyExpr)) :
    Namespace.Result (List Poly) := do
  let names := bindings.map (·.1)
  unless names.length == target.generators.length && names.Nodup && names.all (target.generators.contains ·) do
    algebraProblem span (.coordinate "a transition gives each coordinate of the other open exactly one image")
  target.generators.mapM fun name => do
    let some e := (bindings.find? (·.1 == name)).map (·.2)
      | algebraProblem span (.coordinate s!"no image for coordinate {name}")
    match run (do reduce source.basis (← e.evaluate source.generators)) with
    | .ok p => pure p
    | .error error => algebraProblem span error

/-- The qualified coordinates of the two charts of a gluing: `X₁::c` and then
`X₂::c`, as for a fiber product. -/
def chartCoordinates (a b : Open) : List String :=
  let (q₁, q₂) := fiberQualifiers a.chart b.chart
  qualify q₁ a.chartData.generators ++ qualify q₂ b.chartData.generators

/-- The witness of a separation or manifold claim: it names the inverse
coordinate of the first open and is a polynomial in the qualified
coordinates of the two charts. -/
def witnessOf (span : Span) (a b : Open) (inverse : String) (witness : PolyExpr) : Namespace.Result Poly := do
  let expected := a.data.generators.getLastD ""
  unless inverse == expected do
    glueProblem span <| s!"the witness must give the inverse coordinate `{expected}` of the first open, " ++
      s!"but it gives `{inverse}`"
  match run (witness.evaluate (chartCoordinates a b)) with
  | .ok p => pure p
  | .error error => algebraProblem span error

/-- The glued object `id` in `site`, with its opens and transition. -/
def requireGlued (env : Environment) (span : Span) (claim : String) (site : Site) (id : DeclId) :
    Namespace.Result (Open × Open × List Poly) :=
  match lookup env id with
  | some (.glued implementation first second forward _) =>
    match gluingOpens? env implementation first second with
    | some (actual, a, b) =>
      if actual == site then pure (a, b, forward)
      else glueProblem span <| s!"`{claim}` is a claim about {siteName site}, but `{Namespace.Owner.qualified id}` is glued in " ++
        siteName actual ++ (match site with
          | .zariski => "; state its smooth evidence with `manifold(…)`"
          | .smooth => "; state its separation with `separated(…)`")
    | none => glueProblem span s!"`{Namespace.Owner.qualified id}` is not an accepted glued object"
  | _ => glueProblem span s!"`{Namespace.Owner.qualified id}` is not a glued object"

/-- Elaborate one glued object. -/
def elaborateGlued (env : Environment) (span : Span) (implementation first second : DeclId)
    (body : Option Body) : Namespace.Result Indexed.Declaration := do
  let some site := site? env implementation
    | glueProblem span <| s!"a gluing needs a presented or a smooth implementation, but " ++
        s!"`{Namespace.Owner.qualified implementation}` is neither"
  let a ← requireOpen env span site implementation first
  let b ← requireOpen env span site implementation second
  if a.chart == b.chart then
    glueProblem span <| s!"`{Namespace.Owner.qualified first}` and `{Namespace.Owner.qualified second}` are opens of one chart `{Namespace.Owner.qualified a.chart}`; " ++
      "a gluing needs two charts"
  let some (.glued _ _ forward backward) := body | glueProblem span "missing gluing source"
  let forward ← transitionImages span b.data a.data forward
  let backward ← transitionImages span a.data b.data backward
  let some bases := baseImages? env site first second a b
    | glueProblem span <| s!"the charts `{Namespace.Owner.qualified a.chart}` and `{Namespace.Owner.qualified b.chart}` of a gluing must have " ++
        "one base"
  runGlue span s!"the transition from `{Namespace.Owner.qualified first}` to `{Namespace.Owner.qualified second}`"
    (checkGluing a b bases forward backward)
  pure (.glued implementation first second forward backward)

/-- Elaborate one cover. -/
def elaborateCover (env : Environment) (span : Span) (object : DeclId) (opens : List DeclId)
    (body : Option Body) : Namespace.Result Indexed.Declaration := do
  let some (site, implementation, x) := coverObject? env object
    | glueProblem span s!"the object `{Namespace.Owner.qualified object}` of a cover is not a presented or a smooth object"
  if opens.length > Limits.algebraRelations then
    algebraProblem span (.limit "cover")
  unless opens.Nodup do glueProblem span "a cover lists an open twice"
  let found ← opens.mapM (requireOpen env span site implementation)
  for (id, o) in opens.zip found do
    unless o.chart == object do
      glueProblem span s!"`{Namespace.Owner.qualified id}` is an open of `{Namespace.Owner.qualified o.chart}`, not of `{Namespace.Owner.qualified object}`"
  let some (.cover _ _ coefficients) := body | glueProblem span "missing cover source"
  -- Counted before any coefficient is evaluated, as every other list of the profile.
  unless coefficients.length == opens.length do
    algebraProblem span (.coordinate "a cover gives one coefficient for each open")
  let coefficients ← coefficients.mapM fun e => do
    match run (e.evaluate x.generators) with
    | .ok p => pure p
    | .error error => algebraProblem span error
  runGlue span s!"the cover of `{Namespace.Owner.qualified object}`"
    (GluingDeclarations.checkCover x (found.map (·.element)) coefficients)
  pure (.cover object opens coefficients)

/-- Elaborate one projective chart entry against the open `o` of the gluing. -/
def elaborateProjectiveChart (span : Span) (homogeneous : List String) (o : Open) (chart : SourceChart) :
    Namespace.Result ProjectiveChart := do
  let some index := homogeneous.idxOf? chart.dehomogenized
    | glueProblem span <| s!"`{chart.dehomogenized}` is not a homogeneous coordinate of the projective line"
  let other := homogeneous.getD (1 - index) ""
  let image ← match run (chart.image.evaluate o.chartData.generators) with
    | .ok p => pure p
    | .error error => algebraProblem span error
  let names := chart.inverse.map (·.1)
  unless names.length == o.chartData.generators.length && names.Nodup &&
      names.all (o.chartData.generators.contains ·) do
    algebraProblem span (.coordinate s!"the inverse of the chart `{Namespace.Owner.qualified o.chart}` gives each of its coordinates exactly one image")
  let inverse ← o.chartData.generators.mapM fun name => do
    let some e := (chart.inverse.find? (·.1 == name)).map (·.2)
      | algebraProblem span (.coordinate s!"no image for coordinate {name}")
    match run (e.evaluate [other]) with
    | .ok p => pure p
    | .error error => algebraProblem span error
  pure { chart := o.chart, dehomogenized := index, image, inverse }

/-- Elaborate every glued object and cover, and then every claim. -/
def elaborateGluing (sources : List (DeclId × Span × Body)) (env : Core.Declarations) :
    Namespace.Result Core.Declarations := do
  let mut indexed := env.indexed
  -- Glued objects and covers read opens and charts only.
  let mut first := []
  for entry in indexed do
    let span := spanOf sources entry.id
    let body := bodyOf sources entry.id
    match entry.declaration with
    | .glued implementation a b _ _ =>
      first := first ++ [⟨entry.id, ← elaborateGlued indexed span implementation a b body⟩]
    | .cover object opens _ =>
      first := first ++ [⟨entry.id, ← elaborateCover indexed span object opens body⟩]
    | _ => first := first ++ [entry]
  indexed := first
  -- Claims read the transition of their glued object.
  let mut second := []
  for entry in indexed do
    let span := spanOf sources entry.id
    let body := bodyOf sources entry.id
    match entry.declaration, body with
    | .separated glued _, some (.separated _ inverse witness) =>
      let (a, b, forward) ← requireGlued indexed span "separated(…)" .zariski glued
      let witness ← witnessOf span a b inverse witness
      runGlue span s!"the witness for `{Namespace.Owner.qualified glued}`"
        (checkSeparation a.data a.chartData.arity b.chartData.arity forward witness)
      second := second ++ [⟨entry.id, .separated glued witness⟩]
    | .manifold glued dimension _, some (.manifold _ _ inverse witness) =>
      let (a, b, forward) ← requireGlued indexed span "manifold(…)" .smooth glued
      unless a.chartData.arity == dimension && b.chartData.arity == dimension do
        glueProblem span <| s!"`manifold({Namespace.Owner.qualified glued}, {dimension})` needs charts of dimension {dimension}, " ++
          s!"but `{Namespace.Owner.qualified a.chart}` has dimension {a.chartData.arity} and `{Namespace.Owner.qualified b.chart}` has dimension " ++
          s!"{b.chartData.arity}"
      let witness ← witnessOf span a b inverse witness
      runGlue span s!"the witness for `{Namespace.Owner.qualified glued}`"
        (checkSeparation a.data a.chartData.arity b.chartData.arity forward witness)
      second := second ++ [⟨entry.id, .manifold glued dimension witness⟩]
    | .projective glued homogeneous charts, some (.projective _ _ sourceCharts) =>
      let (a, b, forward) ← requireGlued indexed span "proj(…)" .zariski glued
      unless homogeneous.length == 2 && homogeneous.Nodup do
        glueProblem span "the projective line has two distinct homogeneous coordinates, as in `proj(P)[s, t]`"
      unless baseFree indexed a.chartData && baseFree indexed b.chartData do
        glueProblem span "the projective line of this profile is over a base without coordinates or relations"
      let pairs := charts.zip sourceCharts
      unless pairs.length == 2 do
        glueProblem span s!"a projective claim gives one chart entry for each of the two charts of `{Namespace.Owner.qualified glued}`"
      let some (_, s₁) := pairs.find? (·.1.chart == a.chart)
        | glueProblem span s!"the projective claim gives no entry for the chart `{Namespace.Owner.qualified a.chart}` of `{Namespace.Owner.qualified glued}`"
      let some (_, s₂) := pairs.find? (·.1.chart == b.chart)
        | glueProblem span s!"the projective claim gives no entry for the chart `{Namespace.Owner.qualified b.chart}` of `{Namespace.Owner.qualified glued}`"
      let c₁ ← elaborateProjectiveChart span homogeneous a s₁
      let c₂ ← elaborateProjectiveChart span homogeneous b s₂
      runGlue span s!"the projective claim for `{Namespace.Owner.qualified glued}`"
        (checkProjectiveCharts a b forward c₁ c₂)
      second := second ++ [⟨entry.id, .projective glued homogeneous [c₁, c₂]⟩]
    | _, _ => second := second ++ [entry]
  pure { env with indexed := second }

end VastitasKernel.Indexed.Source
