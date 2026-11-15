import VastitasKernel.IndexedNatureSource
import VastitasKernel.SpectralDeclarations
import VastitasKernel.IndexedSpectralContracts

set_option autoImplicit false

/-! Source elaboration of the spectral declarations, invariants and
observations (Stage 5, #806; `std::linalg::spectral`; ADR 0001 §12).

A free module, an endomorphism, a spectrum and a branch are declared at a
family with the representation `free_module`, `endomorphism`, `spectrum` and
`branch` and one smooth object. `resolveBody` resolves their paths and leaves
their rows, certificates and polynomials empty; a `trace_power(H, k)` or
`char_coefficient(S, i)` morphism stays the placeholder of a declared
morphism, which `elaborateSmooth` passes through, and `lower` resolves the
endomorphism or spectrum it names (`targets`); and the observations
`annihilates`, `action_entry`, `on_branch`, `branch_differential` and
`branch_projector` embed placeholders (`SpectrumRef.placeholder`,
`BranchRef.placeholder`). This pass elaborates all of them, after the nature
declarations and before the relative morphisms, in dependency order, so the
result does not depend on the order of the declarations:

1. every free module: its basis (`SpectralDeclarations.checkModule`);
2. every endomorphism: `n` rows of `n` entries for the rank `n` of its free
   module, each entry expanded in the coordinates of the object with the
   Stage 2 polynomial resolver, all entries of one endomorphism within one
   `algebraWork` budget, then `checkRows` (`symmetric` names the first entry
   that differs from its mirror by the names of the basis);
3. every spectrum: its fiber coordinate a new identifier, no strict keyword,
   no coordinate of the object and no basis vector of the free module
   (`fiberValid`), the
   certificate by Faddeev–LeVerrier and the idempotence quotients
   (`SpectralDeclarations.certify`), then `checkCertificate`;
4. every branch: `g` and `W` expanded in the coordinates and the fiber
   coordinate, `g` without the fiber coordinate and nonzero, `W` of degree
   below `n` in it, the quotient of `W·χ′ − gᵉ` by `χ`
   (`SpectralDeclarations.witnessQuotient`), then `checkWitness`, whose
   failure names a term of the remainder (`residualText`);
5. every spectral invariant becomes `.spectralInvariant` with its exact image,
   `tr(Hᵏ)` or the coefficient of `tⁱ` in `χ` (`tracePowerImage`,
   `charCoefficientImage`), and its provenance, the embedded endomorphism or
   spectrum;
6. every observation gets the declarations it names (`EndoRef`,
   `SpectrumRef`, `BranchRef`), its element expanded in the coordinates and the
   fiber coordinate, and its row and column as indices of the basis.

Each declaration ends with the data check that the declaration audit
repeats (`SpectralDeclarations.checkModule`, `checkRows`, `checkCertificate`,
`checkWitness`, which `checkFreeModule`, `checkEndomorphism`,
`checkSpectrum` and `checkBranch` call), with a fresh budget, after the
family, the object and the declaration it names are checked as the audit
checks them, so a declaration that the pass accepts is accepted by the
audit. The certificates and quotients
are the kernel's: the wire has no field for them. Rejections are
`E_SPECTRAL` at the declaration, naming it and its object; the rank, power
and exponent limits and the algebra budget are `E_LIMIT`, and an unknown
coordinate or a zero denominator is `E_AFFINE_COORDINATE`, as in the entries
of a smooth map. The registry entries of the spectral bindings
(`IndexedSpectralRegistry`) check every embedded copy against its
declaration again. A program without spectral declarations, invariants or
observations is unchanged. -/
namespace VastitasKernel.Indexed.Source

open AlgebraRuntime SpectralDeclarations

def spectralProblem {α : Type} (span : Span) (reason : String) : Namespace.Result α :=
  Namespace.problem span "E_SPECTRAL" reason

private def spectralSpan (sources : List (DeclId × Span × Body)) (id : DeclId) : Span :=
  ((sources.find? (·.1 == id)).map (·.2.1)).getD {}

private def spectralBody (sources : List (DeclId × Span × Body)) (id : DeclId) : Option Body :=
  (sources.find? (·.1 == id)).map (·.2.2)

/-- `count` things: `one` for one, otherwise `many`, after the number. -/
private def countText (count : Nat) (one many : String) : String :=
  s!"{count} {if count == 1 then one else many}"

/-- The longest preview of a polynomial term in a diagnostic, in characters. -/
private def previewLength : Nat := 80

/-- `text`, or its first `previewLength − 1` characters and `…`. -/
private def preview (text : String) : String :=
  if text.length ≤ previewLength then text else (text.take (previewLength - 1)).toString ++ "…"

/-- A rational coefficient as the source writes it: `3`, `-3`, `frac(1, 2)`
or `-frac(1, 2)`. -/
private def rationalText (value : Rat) : String :=
  if value.den == 1 then toString value.num
  else if value.num < 0 then s!"-frac({-value.num}, {value.den})"
  else s!"frac({value.num}, {value.den})"

/-- Presentation only: a term `c·z₁^a₁⋯` with the names `names` of its
variables, as the source writes a product: `-1`, `x^2`, `-t` or
`frac(1, 3) * x * y^2`. A variable beyond `names`, which the elaboration
never produces, is `x` with its position. -/
def termText (names : List String) (term : AlgebraRuntime.Term) : String :=
  let factors := term.monomial.zipIdx.filterMap fun (exponent, i) =>
    let name := names.getD i s!"x{i + 1}"
    if exponent == 0 then none else if exponent == 1 then some name else some s!"{name}^{exponent}"
  match factors with
  | [] => rationalText term.coefficient
  | _ =>
    let product := String.intercalate " * " factors
    if term.coefficient == 1 then product
    else if term.coefficient == -1 then "-" ++ product
    else s!"{rationalText term.coefficient} * {product}"

/-- Presentation only: the residual of a failed gap identity, from its first
term and its number of terms (`Failure.witness`). The elaboration computes
the quotient `Q` by division by `χ`, monic in the fiber coordinate, so the
residual `W·χ′ − gᵉ − Q·χ` is the remainder of `W·χ′ − gᵉ` modulo `χ`. The
term is named with `names`, the coordinates of the object and the fiber
coordinate, and is at most `previewLength` characters long (#833). -/
def residualText (names : List String) (term : AlgebraRuntime.Term) (terms : Nat) : String :=
  let text := preview (termText names term)
  if terms == 1 then s!"its remainder modulo χ is `{text}`"
  else s!"its remainder modulo χ has {terms} terms, among them `{text}`"

/-- What a diagnostic says for a failure of a spectral check about `subject`,
such as "the endomorphism `p::H`". `names` names the variables of a residual:
the coordinates of the object and the fiber coordinate of a branch. -/
private def failureReason (subject : String) (names : List String := []) : Failure → String
  | .rank size => s!"{subject} has rank {size}, beyond the limit of {Limits.spectralRank} (`spectralRank`)"
  | .emptyBasis => s!"{subject} has no basis vector; a free module needs at least one"
  | .duplicateBasis name => s!"{subject} names the basis vector `{name}` twice"
  | .shape => s!"the rows of {subject} are not a square matrix of polynomials in the coordinates of its object"
  | .notSymmetric i j =>
    s!"{subject} is declared `symmetric`, but its entry in row {i + 1}, column {j + 1} differs from " ++
      s!"the entry in row {j + 1}, column {i + 1}"
  | .certificateShape => s!"the computed certificate of {subject} is not well formed"
  | .characteristic => s!"the characteristic polynomial computed for {subject} failed its check: χ ≠ det(tI − H)"
  | .adjugate => s!"the adjugate computed for {subject} failed its check: (tI − H)·adj ≠ χ·I"
  | .adjugateRight => s!"the adjugate computed for {subject} failed its check: adj·(tI − H) ≠ χ·I"
  | .adjugateTrace => s!"the adjugate computed for {subject} failed its check: its trace is not χ′"
  | .cayleyHamilton => s!"the characteristic polynomial computed for {subject} failed its check: χ(H) ≠ 0"
  | .idempotence => s!"the idempotence quotient computed for {subject} failed its check: adj² − χ′·adj ≠ Q·χ"
  | .jacobi i => s!"the spectral pair computed for {subject} failed Jacobi's formula in coordinate {i + 1}"
  | .power k => s!"{subject} takes the power {k}, beyond the limit of {Limits.spectralPower} (`spectralPower`)"
  | .zeroPower => s!"{subject} takes the power 0; `trace_power(H, k)` needs 1 ≤ k ≤ {Limits.spectralPower}"
  | .coefficientIndex i n =>
    s!"{subject} takes the coefficient of t^{i}, but the characteristic polynomial has degree {n}"
  | .exponent e => s!"{subject} has the exponent {e}, beyond the limit of {Limits.spectralPower} (`spectralPower`)"
  | .localizeShape => s!"the localization of {subject} is not a polynomial in the coordinates of its object"
  | .localizeZero => s!"the localization of {subject} is zero; a branch localizes at a nonzero `localize`"
  | .witnessShape => s!"the witness of {subject} is not a polynomial in the coordinates and the fiber coordinate"
  | .unreducedWitness d =>
    s!"the witness of {subject} has degree {d} in the fiber coordinate; a witness is reduced, of degree " ++
      "below the rank"
  | .witness term terms =>
    s!"the witness of {subject} does not certify the gap: W·χ′ − g^e is not a multiple of the " ++
      s!"characteristic polynomial χ; {residualText names term terms}"
  | .work error => s!"{subject}: {error.message}"

private def failureProblem {α : Type} (span : Span) (subject : String) (failure : Failure)
    (names : List String := []) : Namespace.Result α :=
  Namespace.problem span failure.code (failureReason subject names failure)

/-- The coordinates of the smooth object `object` of the spectral declaration
`name` of `kind`, declared at `family`, after its family and its object are
checked. -/
private def spectralObject (span : Span) (env : Environment) (kind representation : String)
    (name family object : DeclId) (isFamily : Bool) : Namespace.Result (List String) := do
  unless isFamily do
    spectralProblem span <| s!"the {kind} `{qualified name}` is declared at `{qualified family}`, which is not " ++
      s!"a family with the representation `{representation}`"
  let some coordinates := smoothCoordinates? env object
    | spectralProblem span <| s!"the {kind} `{qualified name}` is on `{qualified object}`, which is not a smooth " ++
        "object; it needs a smooth object declared with `Affine(n)[…]`"
  unless validApplication env ⟨family, [.object (.global object)]⟩ do
    spectralProblem span <| s!"the {kind} `{qualified name}` is on `{qualified object}`, which its family " ++
      s!"`{qualified family}` does not accept"
  pure coordinates

/-! ## Declarations -/

private def elaborateFreeModule (span : Span) (env : Environment) (name family object : DeclId)
    (basis : List String) : Namespace.Result Unit := do
  let _ ← spectralObject span env "free module" "free_module" name family object (isFreeModuleFamily env family)
  if let .error failure := checkModule basis then
    failureProblem span s!"the free module `{qualified name}`" failure

/-- The rows of the endomorphism `name` of `module`, from its source rows. -/
private def elaborateEndomorphism (span : Span) (env : Environment) (name family object module : DeclId)
    (rows : List (List PolyExpr)) (symmetric : Bool) : Namespace.Result PolyMatrix := do
  let coordinates ← spectralObject span env "endomorphism" "endomorphism" name family object
    (isEndomorphismFamily env family)
  let subject := s!"the endomorphism `{qualified name}`"
  let some (_, moduleObject, basis) := freeModuleData? env module
    | spectralProblem span s!"{subject} acts on `{qualified module}`, which is not a free module declaration"
  unless moduleObject == object do
    spectralProblem span <| s!"{subject} is on `{qualified object}`, but its free module `{qualified module}` " ++
      s!"is on `{qualified moduleObject}`; an endomorphism and its free module have one object"
  let n := basis.length
  if rows.length != n then
    spectralProblem span <| s!"{subject} of the free module `{qualified module}` of rank {n} needs " ++
      s!"{countText n "row" "rows"}, one for each basis vector, but it has {rows.length}"
  if let some (row, i) := rows.zipIdx.find? (·.1.length != n) then
    spectralProblem span <| s!"{subject} of the free module `{qualified module}` of rank {n} needs " ++
      s!"{countText n "entry" "entries"} in each row, but row {i + 1} has {row.length}"
  match AlgebraBasis.run (rows.mapM (·.mapM (·.evaluate coordinates))) with
  | .error error => Namespace.problem span error.code s!"{subject} on `{qualified object}`: {error.message}"
  | .ok matrix =>
    match checkRows coordinates.length n matrix symmetric with
    | .ok () => pure matrix
    | .error (.notSymmetric i j) =>
      let vector (k : Nat) := basis.getD k ""
      spectralProblem span <| s!"{subject} is declared `symmetric`, but its entry ({vector i}, {vector j}) " ++
        s!"differs from its entry ({vector j}, {vector i})"
    | .error failure => failureProblem span subject failure

/-- The certificate of the spectrum `name` of `endomorphism` with the fiber
coordinate `fiber`. -/
private def elaborateSpectrum (span : Span) (env : Environment) (name family object endomorphism : DeclId)
    (fiber : String) : Namespace.Result SpectralCertificate := do
  let coordinates ← spectralObject span env "spectrum" "spectrum" name family object (isSpectrumFamily env family)
  let subject := s!"the spectrum `{qualified name}`"
  let some (_, endomorphismObject, module, rows, _) := endomorphismData? env endomorphism
    | spectralProblem span <| s!"{subject} is the spectrum of `{qualified endomorphism}`, which is not an " ++
        "endomorphism declaration"
  unless endomorphismObject == object do
    spectralProblem span <| s!"{subject} is on `{qualified object}`, but its endomorphism " ++
      s!"`{qualified endomorphism}` is on `{qualified endomorphismObject}`; a spectrum and its endomorphism " ++
      "have one object"
  let some (_, _, basis) := freeModuleData? env module
    | spectralProblem span <| s!"the endomorphism `{qualified endomorphism}` of {subject} acts on " ++
        s!"`{qualified module}`, which is not a free module declaration"
  unless isIdentifier fiber do
    let what := if strictKeywords.contains fiber then "is a strict keyword, not an identifier"
      else "is not an identifier"
    spectralProblem span <| s!"the fiber coordinate `{fiber}` of {subject} {what}; " ++
      "`eigen(H, t)` names the fiber coordinate with a new identifier"
  if coordinates.contains fiber then
    spectralProblem span <| s!"the fiber coordinate `{fiber}` of {subject} is a coordinate of `{qualified object}`; " ++
      "`eigen(H, t)` needs a new name for the fiber coordinate"
  if basis.contains fiber then
    spectralProblem span <| s!"the fiber coordinate `{fiber}` of {subject} is a basis vector of the free module " ++
      s!"`{qualified module}`; `eigen(H, t)` needs a new name for the fiber coordinate"
  if rows.length > Limits.spectralRank then failureProblem span subject (.rank rows.length)
  match AlgebraBasis.run (certify coordinates.length rows) with
  | .error error => Namespace.problem span error.code s!"computing the spectral pair of {subject}: {error.message}"
  | .ok certificate =>
    match checkCertificate coordinates.length rows certificate with
    | .ok () => pure certificate
    | .error failure => failureProblem span subject failure

/-- The localization, the witness and the quotient of the branch `name` of
`spectrum`. -/
private def elaborateBranch (span : Span) (env : Environment) (name family object spectrum : DeclId)
    (localize witness : PolyExpr) (exponent : Nat) : Namespace.Result (Poly × Poly × Poly) := do
  let coordinates ← spectralObject span env "branch" "branch" name family object (isBranchFamily env family)
  let subject := s!"the branch `{qualified name}`"
  let some (_, spectrumObject, endomorphism, fiber, certificate) := spectrumData? env spectrum
    | spectralProblem span <| s!"{subject} is a branch of `{qualified spectrum}`, which is not a spectrum " ++
        "declaration"
  unless spectrumObject == object do
    spectralProblem span <| s!"{subject} is on `{qualified object}`, but its spectrum `{qualified spectrum}` is " ++
      s!"on `{qualified spectrumObject}`; a branch and its spectrum have one object"
  let some (_, _, _, rows, _) := endomorphismData? env endomorphism
    | spectralProblem span <| s!"the spectrum `{qualified spectrum}` of {subject} is not the spectrum of an " ++
        "endomorphism declaration"
  let m := coordinates.length
  let n := rows.length
  if exponent > Limits.spectralPower then failureProblem span subject (.exponent exponent)
  let fibered := coordinates ++ [fiber]
  match AlgebraBasis.run (do pure (← localize.evaluate fibered, ← witness.evaluate fibered)) with
  | .error error => Namespace.problem span error.code s!"{subject} on `{qualified object}`: {error.message}"
  | .ok (g, w) =>
    if SpectralRuntime.degT g > 0 then
      spectralProblem span <| s!"the localization of {subject} contains the fiber coordinate `{fiber}`; it is a " ++
        s!"polynomial in the coordinates of `{qualified object}`"
    let g := SpectralRuntime.tCoefficient g 0
    if g.isEmpty then failureProblem span subject .localizeZero
    if SpectralRuntime.degT w ≥ n then
      spectralProblem span <| s!"the witness of {subject} has degree {SpectralRuntime.degT w} in the fiber " ++
        s!"coordinate `{fiber}`; a witness is reduced, of degree below the rank {n}"
    match AlgebraBasis.run (witnessQuotient m n certificate.characteristic g w exponent) with
    | .error error => Namespace.problem span error.code s!"checking the witness of {subject}: {error.message}"
    | .ok quotient =>
      match checkWitness m n certificate.characteristic g w exponent quotient with
      | .ok () => pure (g, w, quotient)
      | .error failure => failureProblem span subject failure (names := fibered)

/-! ## The declarations that bindings embed -/

/-- The embedded copy of the endomorphism declaration `endomorphism`. -/
def endoRef? (env : Environment) (endomorphism : DeclId) : Option EndoRef := do
  let (_, object, module, rows, symmetric) ← endomorphismData? env endomorphism
  pure ⟨endomorphism, object, module, rows, symmetric⟩

/-- The embedded copy of the spectrum declaration `spectrum`: its
endomorphism, `χ` and `adj(tI − H)` of its certificate. -/
def spectrumRef? (env : Environment) (spectrum : DeclId) : Option SpectrumRef := do
  let (_, _, endomorphism, _, certificate) ← spectrumData? env spectrum
  pure ⟨spectrum, ← endoRef? env endomorphism, certificate.characteristic, certificate.adjugate⟩

/-- The embedded copy of the branch declaration `branch`: its spectrum, its
localization, witness and exponent. -/
def branchRef? (env : Environment) (branch : DeclId) : Option BranchRef := do
  let (_, _, spectrum, localize, witness, exponent, _) ← branchData? env branch
  pure ⟨branch, ← spectrumRef? env spectrum, localize, witness, exponent⟩

/-! ## Invariants -/

/-- The binding of the spectral invariant `name : Smooth<X, Line>` defined by
`definition`, which names `target`. -/
private def elaborateInvariant (span : Span) (env : Environment) (name : DeclId) (application : Application)
    (target : DeclId) (definition : MorphismDefinition) : Namespace.Result PrimitiveBinding := do
  let spelling := match definition with
    | .tracePower .. => "trace_power"
    | _ => "char_coefficient"
  let subject := s!"the `{spelling}` declaration `{qualified name}`"
  unless isSmoothFamily env application.family do
    spectralProblem span <| s!"{subject} defines a smooth map, but `{qualified application.family}` is not a " ++
      "family with the representation `smooth`"
  let [.object (.global source), .object (.global line)] := application.indices
    | spectralProblem span s!"{subject} defines a smooth map `Smooth<X, Line>`, from a source to a target object"
  let some coordinates := smoothCoordinates? env source
    | spectralProblem span s!"the source `{qualified source}` of {subject} is not a smooth object"
  match smoothDimension? env line with
  | some 1 => pure ()
  | some dimension =>
    spectralProblem span <| s!"the target `{qualified line}` of {subject} must be 1-dimensional, but it has " ++
      s!"dimension {dimension}"
  | none => spectralProblem span s!"the target `{qualified line}` of {subject} is not a smooth object"
  let m := coordinates.length
  let mismatch (kind : String) (object : DeclId) : Namespace.Result PrimitiveBinding :=
    spectralProblem span <| s!"{subject} is a smooth map on `{qualified source}`, but its {kind} " ++
      s!"`{qualified target}` is on `{qualified object}`"
  match definition with
  | .tracePower _ power =>
    let some endomorphism := endoRef? env target
      | spectralProblem span <| s!"{subject} takes the trace of a power of `{qualified target}`, which is not an " ++
          "endomorphism declaration"
    unless endomorphism.object == source do return ← mismatch "endomorphism" endomorphism.object
    match tracePowerImage m endomorphism.rows power with
    | .error failure => failureProblem span subject failure
    | .ok image => pure (.spectralInvariant application ⟨m, [], [image]⟩ (.tracePower endomorphism power))
  | .charCoefficient _ index =>
    let some spectrum := spectrumRef? env target
      | spectralProblem span <| s!"{subject} takes a coefficient of the characteristic polynomial of " ++
          s!"`{qualified target}`, which is not a spectrum declaration"
    unless spectrum.endomorphism.object == source do return ← mismatch "spectrum" spectrum.endomorphism.object
    match charCoefficientImage spectrum.endomorphism.rows.length spectrum.characteristic index with
    | .error failure => failureProblem span subject failure
    | .ok image => pure (.spectralInvariant application ⟨m, [], [image]⟩ (.charCoefficient spectrum index))
  | _ => spectralProblem span s!"{subject} is not a spectral invariant"

/-! ## Observations -/

/-- The spectrum that the observation `operation` names. -/
private def bindingSpectrum (span : Span) (env : Environment) (operation : String) (spectrum : DeclId) :
    Namespace.Result SpectrumRef := do
  let some ref := spectrumRef? env spectrum
    | spectralProblem span <| s!"the spectrum of `{operation}` must be a spectrum, but `{qualified spectrum}` is " ++
        "not a spectrum declaration"
  pure ref

/-- The branch that the observation `operation` names. -/
private def bindingBranch (span : Span) (env : Environment) (operation : String) (branch : DeclId) :
    Namespace.Result BranchRef := do
  let some ref := branchRef? env branch
    | spectralProblem span <| s!"the branch of `{operation}` must be a branch, but `{qualified branch}` is not a " ++
        "branch declaration"
  pure ref

/-- The element of an observation of `spectrum`, expanded in the coordinates
of its object and its fiber coordinate, last. -/
private def bindingElement (span : Span) (env : Environment) (operation : String) (spectrum : SpectrumRef)
    (body : Option Body) : Namespace.Result Poly := do
  let some (.primitive primitive) := body
    | spectralProblem span s!"the element of `{operation}` is missing"
  let some element := primitive.spectralElement?
    | spectralProblem span s!"the element of `{operation}` is missing"
  let some (_, _, _, fiber, _) := spectrumData? env spectrum.spectrum
    | spectralProblem span s!"`{qualified spectrum.spectrum}` is not a spectrum declaration"
  let some coordinates := smoothCoordinates? env spectrum.endomorphism.object
    | spectralProblem span s!"`{qualified spectrum.endomorphism.object}` is not a smooth object"
  match AlgebraBasis.run (element.evaluate (coordinates ++ [fiber])) with
  | .error error =>
    Namespace.problem span error.code s!"the element of `{operation}` of `{qualified spectrum.spectrum}`: {error.message}"
  | .ok element => pure element

/-- The row and the column of an observation of an endomorphism of `module`,
as indices of the basis of the module. -/
private def bindingEntry (span : Span) (env : Environment) (operation : String) (module : DeclId)
    (body : Option Body) : Namespace.Result (Nat × Nat) := do
  let some (.primitive primitive) := body
    | spectralProblem span s!"the row and the column of `{operation}` are missing"
  let some (row, column) := primitive.spectralEntry?
    | spectralProblem span s!"the row and the column of `{operation}` are missing"
  let some (_, _, basis) := freeModuleData? env module
    | spectralProblem span s!"`{qualified module}` is not a free module declaration"
  let index (name : String) : Namespace.Result Nat :=
    match basis.idxOf? name with
    | some i => pure i
    | none =>
      spectralProblem span <| s!"`{name}` is not a basis vector of the free module `{qualified module}` of " ++
        s!"`{operation}`, whose basis is {", ".intercalate basis}"
  pure (← index row, ← index column)

/-- Give a spectral binding the declarations it names, and elaborate its
element and its row and column. Every other binding is unchanged. -/
private def elaborateObservation (span : Span) (env : Environment) (body : Option Body)
    (entry : Core.NamedPrimitive) : Namespace.Result Core.NamedPrimitive := do
  match entry.binding with
  | .annihilates smooth spectrum _ =>
    let spectrum ← bindingSpectrum span env "annihilates" spectrum.spectrum
    let element ← bindingElement span env "annihilates" spectrum body
    pure ⟨entry.id, .annihilates smooth spectrum element⟩
  | .actionEntry smooth spectrum _ _ _ =>
    let spectrum ← bindingSpectrum span env "action_entry" spectrum.spectrum
    let element ← bindingElement span env "action_entry" spectrum body
    let (row, column) ← bindingEntry span env "action_entry" spectrum.endomorphism.module body
    pure ⟨entry.id, .actionEntry smooth spectrum element row column⟩
  | .onBranch smooth line branch =>
    pure ⟨entry.id, .onBranch smooth line (← bindingBranch span env "on_branch" branch.branch)⟩
  | .branchDifferential smooth cotangent line branch =>
    pure ⟨entry.id, .branchDifferential smooth cotangent line
      (← bindingBranch span env "branch_differential" branch.branch)⟩
  | .branchProjector smooth line branch _ _ =>
    let branch ← bindingBranch span env "branch_projector" branch.branch
    let (row, column) ← bindingEntry span env "branch_projector" branch.spectrum.endomorphism.module body
    pure ⟨entry.id, .branchProjector smooth line branch row column⟩
  | _ => pure entry

/-! ## The pass -/

/-- Elaborate every spectral declaration, invariant and observation.
`targets` maps each `trace_power` or `char_coefficient` declaration to the
declaration it names. -/
def elaborateSpectral (sources : List (DeclId × Span × Body)) (targets : List (DeclId × DeclId))
    (env : Core.Declarations) : Namespace.Result Core.Declarations := do
  for entry in env.indexed do
    if let .freeModule family object basis := entry.declaration then
      elaborateFreeModule (spectralSpan sources entry.id) env.indexed entry.id family object basis
  let modules := env.indexed
  let endomorphisms ← modules.mapM fun entry => do
    match entry.declaration, spectralBody sources entry.id with
    | .endomorphism family object module _ symmetric, some (.endomorphism _ _ _ rows _) =>
      let rows ← elaborateEndomorphism (spectralSpan sources entry.id) modules entry.id family object module rows
        symmetric
      pure ⟨entry.id, .endomorphism family object module rows symmetric⟩
    | _, _ => pure entry
  let spectra ← endomorphisms.mapM fun entry => do
    match entry.declaration with
    | .spectrum family object endomorphism fiber _ =>
      let certificate ← elaborateSpectrum (spectralSpan sources entry.id) endomorphisms entry.id family object
        endomorphism fiber
      pure ⟨entry.id, .spectrum family object endomorphism fiber certificate⟩
    | _ => pure entry
  let indexed ← spectra.mapM fun entry => do
    match entry.declaration, spectralBody sources entry.id with
    | .branch family object spectrum _ _ exponent _, some (.branch _ _ _ localize witness _) =>
      let (g, w, quotient) ← elaborateBranch (spectralSpan sources entry.id) spectra entry.id family object
        spectrum localize witness exponent
      pure ⟨entry.id, .branch family object spectrum g w exponent quotient⟩
    | _, _ => pure entry
  let primitives ← env.primitives.mapM fun entry => do
    let span := spectralSpan sources entry.id
    let body := spectralBody sources entry.id
    match entry.binding, body with
    | .relativeConstant application _, some (.morphism _ _ definition@(.tracePower ..))
    | .relativeConstant application _, some (.morphism _ _ definition@(.charCoefficient ..)) =>
      let some target := targets.lookup entry.id
        | spectralProblem span s!"the declaration `{qualified entry.id}` names no endomorphism or spectrum"
      pure ⟨entry.id, ← elaborateInvariant span indexed entry.id application target definition⟩
    | _, _ => elaborateObservation span indexed body entry
  pure { env with indexed, primitives }

end VastitasKernel.Indexed.Source
