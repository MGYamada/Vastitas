import VastitasKernel.Indexed
import VastitasKernel.Limits

set_option autoImplicit false

/-! The validity of the Stage 7 declarations (#878): smooth opens, glued
objects, covers, and separation, manifold and projective claims.

Each check reads the stored data of the declarations that it names through
the views of `Indexed` and runs the exact actions of `GluingDeclarations` in
one work budget. Elaboration runs the same actions, so an elaborated
declaration passes its audit. A site is never converted: a Zariski check
reads only presented objects and their principal opens, a smooth check only
smooth objects and their smooth opens, and the implementation of a gluing
chooses its site. -/
namespace VastitasKernel.Indexed.Gluing

open AlgebraRuntime AlgebraBasis AlgebraDeclarations GluingDeclarations

/-- The site of a gluing, chosen by its implementation. -/
inductive Site where
  | zariski
  | smooth
  deriving Repr, Inhabited, DecidableEq, BEq

/-- The site of an implementation: presented implementations give the
Zariski site, `smooth_affine` implementations the smooth site. -/
def site? (env : Environment) (implementation : DeclId) : Option Site :=
  if presentedImplementation env implementation then some .zariski
  else if smoothImplementation env implementation then some .smooth
  else none

/-- A chart and its presentation: a presented object of the implementation,
or a smooth object of it with its free presentation. -/
def chartData? (env : Environment) (site : Site) (implementation chart : DeclId) : Option AffineData :=
  match site, lookup env chart with
  | .zariski, some (.affine chartImplementation data) =>
    if chartImplementation == implementation then some data else none
  | .smooth, some (.smoothAffine chartImplementation coordinates) =>
    if chartImplementation == implementation then some (freeData coordinates) else none
  | _, _ => none

/-- An open of a chart in one site: its chart, its element, its presentation
and the presentation of its chart. -/
structure Open where
  chart : DeclId
  element : Poly
  data : AffineData
  chartData : AffineData
  deriving Repr, Inhabited

/-- The open `id` of the site of `implementation`: a principal open
`localize(X, f)` of a presented object in the Zariski site, a smooth open in
the smooth site, each of the same implementation as its chart. -/
def open? (env : Environment) (site : Site) (implementation id : DeclId) : Option Open :=
  let found : Option AffineData := match site, lookup env id with
    | .zariski, some (.affine openImplementation data) =>
      if openImplementation == implementation then some data else none
    | .smooth, some (.smoothOpen openImplementation data) =>
      if openImplementation == implementation then some data else none
    | _, _ => none
  match found with
  | none => none
  | some data =>
    match localization? data with
    | none => none
    | some (chart, element) =>
      match chartData? env site implementation chart with
      | some chartData => some ⟨chart, element, data, chartData⟩
      | none => none

/-- A smooth open: its implementation is a smooth representation, its object
a smooth object of the same implementation, and its stored presentation is
the principal open derived from the free presentation of that object. -/
def checkSmoothOpen (env : Environment) (implementation : DeclId) (data : AffineData) : Bool :=
  smoothImplementation env implementation &&
  match data.construction with
  | .localization object _ _ _ =>
    match lookup env object with
    | some (.smoothAffine objectImplementation coordinates) =>
      objectImplementation == implementation &&
      validAffineData data (some (freeData coordinates)) &&
      validConstruction data (fun id => if id == object then some (freeData coordinates) else none)
    | _ => false
  | _ => false

/-- The structure images of both opens to the common base of their charts,
for a Zariski gluing with a base; `none` without a base or in the smooth site. -/
def baseImages? (env : Environment) (site : Site) (first second : DeclId) (a b : Open) :
    Option (Option (List Poly × List Poly)) :=
  match site with
  | .smooth => some none
  | .zariski =>
    if a.chartData.base != b.chartData.base then none else
    match a.chartData.base with
    | none => some none
    | some base =>
      match structureImages? env first base, structureImages? env second base with
      | some sx, some sy => some (some (sx, sy))
      | _, _ => none

/-- Every check of a gluing, in one budget: the transition, and over a base
the commuting triangle. -/
def checkGluing (a b : Open) (bases : Option (List Poly × List Poly)) (forward backward : List Poly) :
    Work Unit := do
  checkTransition a.data b.data forward backward
  if let some (sx, sy) := bases then checkOverBase a.data sx sy forward

/-- The two opens of a gluing in the site of its implementation. -/
def gluingOpens? (env : Environment) (implementation first second : DeclId) : Option (Site × Open × Open) := do
  let site ← site? env implementation
  let a ← open? env site implementation first
  let b ← open? env site implementation second
  pure (site, a, b)

/-- A glued object: two opens of distinct charts in the site of its
implementation, a transition between them that is an isomorphism, and over a
common base a map over that base. -/
def checkGlued (env : Environment) (implementation first second : DeclId) (forward backward : List Poly) :
    Bool :=
  match gluingOpens? env implementation first second with
  | some (site, a, b) =>
    a.chart != b.chart &&
    match baseImages? env site first second a b with
    | some bases => (run (checkGluing a b bases forward backward)).isOk
    | none => false
  | none => false

/-- The site, implementation and presentation of the object of a cover. -/
def coverObject? (env : Environment) (object : DeclId) : Option (Site × DeclId × AffineData) :=
  match lookup env object with
  | some (.affine implementation data) =>
    if presentedImplementation env implementation then some (.zariski, implementation, data) else none
  | some (.smoothAffine implementation coordinates) =>
    if smoothImplementation env implementation then some (.smooth, implementation, freeData coordinates) else none
  | _ => none

/-- A cover of `object` by distinct opens of `object` in its site, with the
coefficients of the unit-ideal identity. -/
def checkCover (env : Environment) (object : DeclId) (opens : List DeclId) (coefficients : List Poly) : Bool :=
  decide (opens.length ≤ Limits.algebraRelations) && decide opens.Nodup &&
  match coverObject? env object with
  | some (site, implementation, x) =>
    match opens.mapM (open? env site implementation) with
    | some found =>
      found.all (·.chart == object) &&
      (run (GluingDeclarations.checkCover x (found.map (·.element)) coefficients)).isOk
    | none => false
  | none => false

/-- The stored data of a glued object, with its site and opens. -/
def glued? (env : Environment) (glued : DeclId) : Option (Site × Open × Open × List Poly) :=
  match lookup env glued with
  | some (.glued implementation first second forward _) =>
    match gluingOpens? env implementation first second with
    | some (site, a, b) => some (site, a, b, forward)
    | none => none
  | _ => none

/-- A separation claim: a Zariski gluing and a witness that gives the inverse
coordinate of its first open. -/
def checkSeparated (env : Environment) (glued : DeclId) (witness : Poly) : Bool :=
  match glued? env glued with
  | some (.zariski, a, b, forward) =>
    (run (checkSeparation a.data a.chartData.arity b.chartData.arity forward witness)).isOk
  | _ => false

/-- A manifold claim: a smooth gluing of two charts of the stated dimension,
and a witness that closes the graph of its transition. -/
def checkManifold (env : Environment) (glued : DeclId) (dimension : Nat) (witness : Poly) : Bool :=
  match glued? env glued with
  | some (.smooth, a, b, forward) =>
    a.chartData.arity == dimension && b.chartData.arity == dimension &&
    (run (checkSeparation a.data a.chartData.arity b.chartData.arity forward witness)).isOk
  | _ => false

/-- The chart is over no base, or over a presented object with no coordinates
and no relations, as the projective line `Proj B[s, t]` of the profile needs. -/
def baseFree (env : Environment) (chart : AffineData) : Bool :=
  match chart.base with
  | none => true
  | some base =>
    match affineData? env base with
    | some data => data.arity == 0 && data.basis.isEmpty
    | none => false

/-- Every check of a projective claim, in one budget. -/
def checkProjectiveCharts (a b : Open) (forward : List Poly) (first second : ProjectiveChart) : Work Unit := do
  checkProjectiveChart a.chartData a.element first
  checkProjectiveChart b.chartData b.element second
  checkProjectiveOverlap a.data a.chartData.arity b.chartData.arity forward first second

/-- A projective claim: a Zariski gluing over a base without coordinates, two
distinct homogeneous coordinates, and one chart entry for each chart, in the
order of the opens of the gluing. -/
def checkProjective (env : Environment) (glued : DeclId) (homogeneous : List String)
    (charts : List ProjectiveChart) : Bool :=
  homogeneous.length == 2 && decide homogeneous.Nodup &&
  match glued? env glued, charts with
  | some (.zariski, a, b, forward), [first, second] =>
    first.chart == a.chart && second.chart == b.chart &&
    baseFree env a.chartData && baseFree env b.chartData &&
    (run (checkProjectiveCharts a b forward first second)).isOk
  | _, _ => false

end VastitasKernel.Indexed.Gluing
