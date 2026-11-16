import VastitasOracle.IndexedPrimitiveSoundness
import VastitasOracle.SmoothFibers
import VastitasKernel.IndexedSpectralRegistry

set_option autoImplicit false

/-! Soundness of the spectral bindings (Stage 5, #806): one `Sound` instance
per spectral binding, which `IndexedSemantics.registry_sound` cites by name.

**Associations and totality.** For each spectral binding, the association of
its shape on its well-shaped operands (`*_association`), the operand list of
any accepted call (`*_shape`), typed totality (`*_total`) and the `Sound`
instance (`*_sound`), with the erasure of the matched operands.

- A spectral invariant is a declared smooth map: with no operands it
  evaluates to its map as one program node, well typed between the
  dimensions of its source and target, since its contract contains that of a
  declared smooth map (`spectralInvariantValid_constant`).
- `annihilates` and `on_branch` return Booleans, and `action_entry` and
  `branch_projector` integer pairs, on a point of the object of their
  spectrum or branch (and a value of the declared line from the same
  0-dimensional object).
- `branch_differential` returns a covector over the branch's object: the
  failure value, or the point's coordinates with one component per
  coordinate (`branchDifferential_typed`).

These are the local obligations of the registry entries only. What the
observations mean (the spectral identities, the eigenprojector, the
implicit-function form of the branch differential) is stated in the other
spectral modules. -/
namespace VastitasOracle.SpectralPrimitives

open VastitasKernel VastitasKernel.Indexed VastitasKernel.Indexed.Core
open VastitasKernel.Indexed.Core.Semantics
open VastitasOracle.IndexedPrimitiveSoundness VastitasOracle.IndexedAssociations
open VastitasOracle.SmoothPrimitives (SmoothOutcome smooth_family smooth_value smooth_typed endpoints_spec
  values_nil values_single values_pair)
open VastitasOracle.SmoothFibers (fiber_family_cotangent fiber_typed point_value coordinates_length)

/-! ## Runtime facts behind the typing -/

/-- The branch differential at a point of `ℝⁿ` is a covector over `ℝⁿ`, or
the failure value. -/
theorem branchDifferential_typed {localize characteristic : AlgebraRuntime.Poly}
    {point value : SmoothRuntime.Program} {n : Nat} (hpoint : point.wellTyped 0 n = true) :
    FiberTyped n (SpectralRuntime.branchDifferential localize characteristic point value) := by
  unfold SpectralRuntime.branchDifferential
  split
  · exact ⟨coordinates_length hpoint, by simp [coordinates_length hpoint]⟩
  · trivial

/-- The contract of a spectral invariant contains that of a declared smooth
map. -/
theorem spectralInvariantValid_constant {env : Indexed.Environment} {application : Application}
    {map : AlgebraRuntime.Map} {invariant : SpectralInvariant}
    (valid : spectralInvariantValid env application map invariant = true) :
    smoothConstantValid env application map = true := by
  unfold spectralInvariantValid at valid
  simp only [Bool.and_eq_true] at valid
  exact valid.1.1.1

/-! ## Associations -/

/-- The simp set of `association_simp`, after exposing a spectral entry. -/
local macro "spectral_association_simp" : tactic =>
  `(tactic| (simp only [PrimitiveAssociation, PrimitiveBinding.contract, SpectralRegistry.spectralInvariant,
      SpectralRegistry.annihilates, SpectralRegistry.actionEntry, SpectralRegistry.onBranch,
      SpectralRegistry.branchDifferential, SpectralRegistry.branchProjector, SpectralRegistry.averageAt];
             association_simp))

theorem spectralInvariant_association {env : Environment} {application : Application} {map : AlgebraRuntime.Map}
    {invariant : SpectralInvariant} {allowed : List Indexed.ObjectRef} {brand : Nat} {result : ValueType} :
    PrimitiveAssociation env (.spectralInvariant application map invariant) allowed brand [] result ↔
      .indexed application = result := by
  spectral_association_simp

theorem annihilates_association {env : Environment} {smooth sf point : DeclId} {spectrum : SpectrumRef}
    {element : AlgebraRuntime.Poly} {x : Indexed.ObjectRef} {allowed : List Indexed.ObjectRef} {brand : Nat}
    {result : ValueType} :
    PrimitiveAssociation env (.annihilates smooth spectrum element) allowed brand
      [.indexed ⟨sf, [.object (.global point), .object x]⟩] result ↔
      sf = smooth ∧ .global spectrum.object = x ∧ smoothDimension? env point = some 0 ∧ .boolean = result := by
  spectral_association_simp

theorem actionEntry_association {env : Environment} {smooth sf point : DeclId} {spectrum : SpectrumRef}
    {element : AlgebraRuntime.Poly} {row column : Nat} {x : Indexed.ObjectRef} {allowed : List Indexed.ObjectRef}
    {brand : Nat} {result : ValueType} :
    PrimitiveAssociation env (.actionEntry smooth spectrum element row column) allowed brand
      [.indexed ⟨sf, [.object (.global point), .object x]⟩] result ↔
      sf = smooth ∧ .global spectrum.object = x ∧ smoothDimension? env point = some 0 ∧ .integerPair = result := by
  spectral_association_simp

theorem onBranch_association {env : Environment} {smooth line sf vf point : DeclId} {branch : BranchRef}
    {x p l : Indexed.ObjectRef} {allowed : List Indexed.ObjectRef} {brand : Nat} {result : ValueType} :
    PrimitiveAssociation env (.onBranch smooth line branch) allowed brand
      [.indexed ⟨sf, [.object (.global point), .object x]⟩, .indexed ⟨vf, [.object p, .object l]⟩] result ↔
      sf = smooth ∧ .global branch.object = x ∧ vf = smooth ∧ .global line = l ∧ .global point = p ∧
        smoothDimension? env point = some 0 ∧ .boolean = result := by
  spectral_association_simp

theorem branchDifferential_association {env : Environment} {smooth cotangent line sf vf point : DeclId}
    {branch : BranchRef} {x p l : Indexed.ObjectRef} {allowed : List Indexed.ObjectRef} {brand : Nat}
    {result : ValueType} :
    PrimitiveAssociation env (.branchDifferential smooth cotangent line branch) allowed brand
      [.indexed ⟨sf, [.object (.global point), .object x]⟩, .indexed ⟨vf, [.object p, .object l]⟩] result ↔
      sf = smooth ∧ .global branch.object = x ∧ vf = smooth ∧ .global line = l ∧ .global point = p ∧
        smoothDimension? env point = some 0 ∧ .indexed ⟨cotangent, [.object (.global branch.object)]⟩ = result := by
  spectral_association_simp

theorem branchProjector_association {env : Environment} {smooth line sf vf point : DeclId} {branch : BranchRef}
    {row column : Nat} {x p l : Indexed.ObjectRef} {allowed : List Indexed.ObjectRef} {brand : Nat}
    {result : ValueType} :
    PrimitiveAssociation env (.branchProjector smooth line branch row column) allowed brand
      [.indexed ⟨sf, [.object (.global point), .object x]⟩, .indexed ⟨vf, [.object p, .object l]⟩] result ↔
      sf = smooth ∧ .global branch.object = x ∧ vf = smooth ∧ .global line = l ∧ .global point = p ∧
        smoothDimension? env point = some 0 ∧ .integerPair = result := by
  spectral_association_simp

/-! ## The operand list of an accepted call -/

theorem spectralInvariant_shape {env : Environment} {application : Application} {map : AlgebraRuntime.Map}
    {invariant : SpectralInvariant} {allowed : List Indexed.ObjectRef} {brand : Nat} {arguments : List ValueType}
    {result : ValueType}
    (association : PrimitiveAssociation env (.spectralInvariant application map invariant) allowed brand arguments
      result) :
    arguments = [] := by
  obtain ⟨h, -, -⟩ := association
  operands_end h
  rfl

/-- The one operand of the module action: a point of the spectrum's object. -/
theorem annihilates_shape {env : Environment} {smooth : DeclId} {spectrum : SpectrumRef}
    {element : AlgebraRuntime.Poly} {allowed : List Indexed.ObjectRef} {brand : Nat} {arguments : List ValueType}
    {result : ValueType}
    (association : PrimitiveAssociation env (.annihilates smooth spectrum element) allowed brand arguments result) :
    ∃ point : DeclId, arguments = [.indexed ⟨smooth, [.object (.global point), .object (.global spectrum.object)]⟩] := by
  obtain ⟨h, relations, -⟩ := association
  have atOrigin := relations (.pointDimension ⟨0, 0⟩ 0)
    (by simp [PrimitiveBinding.contract, SpectralRegistry.annihilates, PrimitiveDescriptor.ofBool])
  operand_cons a ma h
  operands_end h
  indexed_operand ia sa ma
  slot_var ref sa
  slot_fixed sa
  slots_end sa
  obtain ⟨point, rfl⟩ := point_global (by rfl) atOrigin
  exact ⟨point, rfl⟩

theorem actionEntry_shape {env : Environment} {smooth : DeclId} {spectrum : SpectrumRef}
    {element : AlgebraRuntime.Poly} {row column : Nat} {allowed : List Indexed.ObjectRef} {brand : Nat}
    {arguments : List ValueType} {result : ValueType}
    (association : PrimitiveAssociation env (.actionEntry smooth spectrum element row column) allowed brand arguments
      result) :
    ∃ point : DeclId, arguments = [.indexed ⟨smooth, [.object (.global point), .object (.global spectrum.object)]⟩] := by
  obtain ⟨h, relations, -⟩ := association
  have atOrigin := relations (.pointDimension ⟨0, 0⟩ 0)
    (by simp [PrimitiveBinding.contract, SpectralRegistry.actionEntry, PrimitiveDescriptor.ofBool])
  operand_cons a ma h
  operands_end h
  indexed_operand ia sa ma
  slot_var ref sa
  slot_fixed sa
  slots_end sa
  obtain ⟨point, rfl⟩ := point_global (by rfl) atOrigin
  exact ⟨point, rfl⟩

/-- The two operands of a branch observation: a point of the branch's object,
and a value in the declared line. -/
theorem onBranch_shape {env : Environment} {smooth line : DeclId} {branch : BranchRef}
    {allowed : List Indexed.ObjectRef} {brand : Nat} {arguments : List ValueType} {result : ValueType}
    (association : PrimitiveAssociation env (.onBranch smooth line branch) allowed brand arguments result) :
    ∃ (point : DeclId) (p : Indexed.ObjectRef), arguments =
      [.indexed ⟨smooth, [.object (.global point), .object (.global branch.object)]⟩,
        .indexed ⟨smooth, [.object p, .object (.global line)]⟩] := by
  obtain ⟨h, relations, -⟩ := association
  have atOrigin := relations (.pointDimension ⟨0, 0⟩ 0)
    (by simp [PrimitiveBinding.contract, SpectralRegistry.onBranch, PrimitiveDescriptor.ofBool])
  operand_cons a ma h
  operand_cons b mb h
  operands_end h
  indexed_operand ia sa ma
  slot_var ref sa
  slot_fixed sa
  slots_end sa
  indexed_operand ib sb mb
  slot_var p sb
  slot_fixed sb
  slots_end sb
  obtain ⟨point, rfl⟩ := point_global (by rfl) atOrigin
  exact ⟨point, p, rfl⟩

theorem branchDifferential_shape {env : Environment} {smooth cotangent line : DeclId} {branch : BranchRef}
    {allowed : List Indexed.ObjectRef} {brand : Nat} {arguments : List ValueType} {result : ValueType}
    (association : PrimitiveAssociation env (.branchDifferential smooth cotangent line branch) allowed brand arguments
      result) :
    ∃ (point : DeclId) (p : Indexed.ObjectRef), arguments =
      [.indexed ⟨smooth, [.object (.global point), .object (.global branch.object)]⟩,
        .indexed ⟨smooth, [.object p, .object (.global line)]⟩] := by
  obtain ⟨h, relations, -⟩ := association
  have atOrigin := relations (.pointDimension ⟨0, 0⟩ 0)
    (by simp [PrimitiveBinding.contract, SpectralRegistry.branchDifferential, PrimitiveDescriptor.ofBool])
  operand_cons a ma h
  operand_cons b mb h
  operands_end h
  indexed_operand ia sa ma
  slot_var ref sa
  slot_fixed sa
  slots_end sa
  indexed_operand ib sb mb
  slot_var p sb
  slot_fixed sb
  slots_end sb
  obtain ⟨point, rfl⟩ := point_global (by rfl) atOrigin
  exact ⟨point, p, rfl⟩

theorem branchProjector_shape {env : Environment} {smooth line : DeclId} {branch : BranchRef} {row column : Nat}
    {allowed : List Indexed.ObjectRef} {brand : Nat} {arguments : List ValueType} {result : ValueType}
    (association : PrimitiveAssociation env (.branchProjector smooth line branch row column) allowed brand arguments
      result) :
    ∃ (point : DeclId) (p : Indexed.ObjectRef), arguments =
      [.indexed ⟨smooth, [.object (.global point), .object (.global branch.object)]⟩,
        .indexed ⟨smooth, [.object p, .object (.global line)]⟩] := by
  obtain ⟨h, relations, -⟩ := association
  have atOrigin := relations (.pointDimension ⟨0, 0⟩ 0)
    (by simp [PrimitiveBinding.contract, SpectralRegistry.branchProjector, PrimitiveDescriptor.ofBool])
  operand_cons a ma h
  operand_cons b mb h
  operands_end h
  indexed_operand ia sa ma
  slot_var ref sa
  slot_fixed sa
  slots_end sa
  indexed_operand ib sb mb
  slot_var p sb
  slot_fixed sb
  slots_end sb
  obtain ⟨point, rfl⟩ := point_global (by rfl) atOrigin
  exact ⟨point, p, rfl⟩

/-! ## Typed totality -/

theorem spectralInvariant_total {env : Indexed.Environment} {world : World} {application : Application}
    {map : AlgebraRuntime.Map} {invariant : SpectralInvariant} {allowed : List Indexed.ObjectRef} {brand : Nat}
    {output : ValueType} {values : List Value}
    (rule : PrimitiveTyped env (.spectralInvariant application map invariant) allowed brand [] output)
    (typed : PrimitiveValuesHaveTypes env world values []) :
    SmoothOutcome env world (.spectralInvariant application map invariant) values output := by
  have empty := values_nil typed
  subst values
  have association : output = .indexed application := (spectralInvariant_association.mp rule.association).symm
  subst association
  have valid : smoothConstantValid env application map = true :=
    spectralInvariantValid_constant (rule.bindingValid : spectralInvariantValid env application map invariant = true)
  unfold smoothConstantValid at valid
  simp only [Bool.and_eq_true] at valid
  obtain ⟨⟨smooth, _⟩, endpoints⟩ := valid
  cases h : smoothEndpoints? env application with
  | none => simp [h] at endpoints
  | some dimensions =>
    obtain ⟨n, m⟩ := dimensions
    simp only [h] at endpoints
    obtain ⟨x, y, indices, hx, hy⟩ := endpoints_spec h
    exact ⟨_, rfl, smooth_typed (smooth_family smooth) rule.resultValid indices hx hy endpoints⟩

theorem annihilates_total {env : Indexed.Environment} {world : World} {smooth point : DeclId}
    {spectrum : SpectrumRef} {element : AlgebraRuntime.Poly} {allowed : List Indexed.ObjectRef} {brand : Nat}
    {output : ValueType} {values : List Value}
    (rule : PrimitiveTyped env (.annihilates smooth spectrum element) allowed brand
      [.indexed ⟨smooth, [.object (.global point), .object (.global spectrum.object)]⟩] output)
    (typed : PrimitiveValuesHaveTypes env world values
      [.indexed ⟨smooth, [.object (.global point), .object (.global spectrum.object)]⟩]) :
    SmoothOutcome env world (.annihilates smooth spectrum element) values output := by
  have valid : annihilatesValid env smooth spectrum element = true := rule.bindingValid
  obtain ⟨-, -, -, rfl⟩ := annihilates_association.mp rule.association
  unfold annihilatesValid at valid
  simp only [Bool.and_eq_true] at valid
  obtain ⟨value, rfl, valueTyped⟩ := values_single typed
  obtain ⟨program, _, _, _, _, rfl, _⟩ := smooth_value (smooth_family valid.1.1) valueTyped
  exact ⟨.boolean (SpectralRuntime.annihilates spectrum.endomorphism.rows element program), rfl, trivial⟩

theorem actionEntry_total {env : Indexed.Environment} {world : World} {smooth point : DeclId}
    {spectrum : SpectrumRef} {element : AlgebraRuntime.Poly} {row column : Nat} {allowed : List Indexed.ObjectRef}
    {brand : Nat} {output : ValueType} {values : List Value}
    (rule : PrimitiveTyped env (.actionEntry smooth spectrum element row column) allowed brand
      [.indexed ⟨smooth, [.object (.global point), .object (.global spectrum.object)]⟩] output)
    (typed : PrimitiveValuesHaveTypes env world values
      [.indexed ⟨smooth, [.object (.global point), .object (.global spectrum.object)]⟩]) :
    SmoothOutcome env world (.actionEntry smooth spectrum element row column) values output := by
  have valid : actionEntryValid env smooth spectrum element row column = true := rule.bindingValid
  obtain ⟨-, -, -, rfl⟩ := actionEntry_association.mp rule.association
  unfold actionEntryValid annihilatesValid at valid
  simp only [Bool.and_eq_true] at valid
  obtain ⟨value, rfl, valueTyped⟩ := values_single typed
  obtain ⟨program, _, _, _, _, rfl, _⟩ := smooth_value (smooth_family valid.1.1.1.1) valueTyped
  exact ⟨.pairInt (SpectralRuntime.actionEntry spectrum.endomorphism.rows element program row column).1
    (SpectralRuntime.actionEntry spectrum.endomorphism.rows element program row column).2, rfl, trivial⟩

theorem onBranch_total {env : Indexed.Environment} {world : World} {smooth line point : DeclId}
    {branch : BranchRef} {p : Indexed.ObjectRef} {allowed : List Indexed.ObjectRef} {brand : Nat}
    {output : ValueType} {values : List Value}
    (rule : PrimitiveTyped env (.onBranch smooth line branch) allowed brand
      [.indexed ⟨smooth, [.object (.global point), .object (.global branch.object)]⟩,
        .indexed ⟨smooth, [.object p, .object (.global line)]⟩] output)
    (typed : PrimitiveValuesHaveTypes env world values
      [.indexed ⟨smooth, [.object (.global point), .object (.global branch.object)]⟩,
        .indexed ⟨smooth, [.object p, .object (.global line)]⟩]) :
    SmoothOutcome env world (.onBranch smooth line branch) values output := by
  have valid : onBranchValid env smooth line branch = true := rule.bindingValid
  obtain ⟨-, -, -, -, -, -, rfl⟩ := onBranch_association.mp rule.association
  unfold onBranchValid at valid
  simp only [Bool.and_eq_true] at valid
  have representation := smooth_family valid.1.1
  obtain ⟨first, second, rfl, firstTyped, secondTyped⟩ := values_pair typed
  obtain ⟨program, _, _, _, _, rfl, _⟩ := smooth_value representation firstTyped
  obtain ⟨value, _, _, _, _, rfl, _⟩ := smooth_value representation secondTyped
  exact ⟨.boolean (SpectralRuntime.onBranch branch.localize branch.spectrum.characteristic program value), rfl,
    trivial⟩

theorem branchDifferential_total {env : Indexed.Environment} {world : World} {smooth cotangent line point : DeclId}
    {branch : BranchRef} {p : Indexed.ObjectRef} {allowed : List Indexed.ObjectRef} {brand : Nat}
    {output : ValueType} {values : List Value}
    (rule : PrimitiveTyped env (.branchDifferential smooth cotangent line branch) allowed brand
      [.indexed ⟨smooth, [.object (.global point), .object (.global branch.object)]⟩,
        .indexed ⟨smooth, [.object p, .object (.global line)]⟩] output)
    (typed : PrimitiveValuesHaveTypes env world values
      [.indexed ⟨smooth, [.object (.global point), .object (.global branch.object)]⟩,
        .indexed ⟨smooth, [.object p, .object (.global line)]⟩]) :
    SmoothOutcome env world (.branchDifferential smooth cotangent line branch) values output := by
  have valid : branchDifferentialValid env smooth cotangent line branch = true := rule.bindingValid
  obtain ⟨-, -, -, -, -, pointZero, rfl⟩ := branchDifferential_association.mp rule.association
  unfold branchDifferentialValid at valid
  simp only [Bool.and_eq_true] at valid
  have representation := smooth_family valid.1.1.1.1
  have cotangentRepresentation := fiber_family_cotangent valid.1.1.1.2
  obtain ⟨first, second, rfl, firstTyped, secondTyped⟩ := values_pair typed
  obtain ⟨program, n, rfl, hx, welltyped⟩ := point_value representation pointZero firstTyped
  obtain ⟨value, _, _, _, _, rfl, _⟩ := smooth_value representation secondTyped
  exact ⟨_, rfl, fiber_typed cotangentRepresentation rule.resultValid rfl hx (branchDifferential_typed welltyped)⟩

theorem branchProjector_total {env : Indexed.Environment} {world : World} {smooth line point : DeclId}
    {branch : BranchRef} {row column : Nat} {p : Indexed.ObjectRef} {allowed : List Indexed.ObjectRef} {brand : Nat}
    {output : ValueType} {values : List Value}
    (rule : PrimitiveTyped env (.branchProjector smooth line branch row column) allowed brand
      [.indexed ⟨smooth, [.object (.global point), .object (.global branch.object)]⟩,
        .indexed ⟨smooth, [.object p, .object (.global line)]⟩] output)
    (typed : PrimitiveValuesHaveTypes env world values
      [.indexed ⟨smooth, [.object (.global point), .object (.global branch.object)]⟩,
        .indexed ⟨smooth, [.object p, .object (.global line)]⟩]) :
    SmoothOutcome env world (.branchProjector smooth line branch row column) values output := by
  have valid : branchProjectorValid env smooth line branch row column = true := rule.bindingValid
  obtain ⟨-, -, -, -, -, -, rfl⟩ := branchProjector_association.mp rule.association
  unfold branchProjectorValid onBranchValid at valid
  simp only [Bool.and_eq_true] at valid
  have representation := smooth_family valid.1.1.1.1
  obtain ⟨first, second, rfl, firstTyped, secondTyped⟩ := values_pair typed
  obtain ⟨program, _, _, _, _, rfl, _⟩ := smooth_value representation firstTyped
  obtain ⟨value, _, _, _, _, rfl, _⟩ := smooth_value representation secondTyped
  exact ⟨.pairInt
    (SpectralRuntime.projectorEntry branch.localize branch.spectrum.characteristic branch.spectrum.adjugate program
      value row column).1
    (SpectralRuntime.projectorEntry branch.localize branch.spectrum.characteristic branch.spectrum.adjugate program
      value row column).2, rfl, trivial⟩

/-! ## Runtime erasure -/

/-- Erasure of a spectral entry, whose evaluators match one operand pattern:
expose the entry's match, split it, and erase by computation. -/
local macro "erase_spectral" h:ident : tactic =>
  `(tactic| (simp only [evalPrimitive, PrimitiveBinding.contract, SpectralRegistry.spectralInvariant,
      SpectralRegistry.annihilates, SpectralRegistry.actionEntry, SpectralRegistry.onBranch,
      SpectralRegistry.branchDifferential, SpectralRegistry.branchProjector, SpectralRegistry.averageAt,
      PrimitiveDescriptor.ofBool] at $h:ident;
             split at $h:ident <;> first | contradiction | (cases $h:ident; exact ⟨_, _, rfl, rfl, rfl⟩)))

/-! ## Soundness instances -/

theorem spectralInvariant_sound (application : Application) (map : AlgebraRuntime.Map)
    (invariant : SpectralInvariant) :
    Sound (PrimitiveBinding.spectralInvariant application map invariant).contract :=
  .ofPure rfl
    (by
      intro env world allowed brand arguments output values rule typed
      obtain rfl := spectralInvariant_shape rule.association
      exact spectralInvariant_total rule typed)
    (by
      intro env values value evaluated
      erase_spectral evaluated)

theorem annihilates_sound (smooth : DeclId) (spectrum : SpectrumRef) (element : AlgebraRuntime.Poly) :
    Sound (PrimitiveBinding.annihilates smooth spectrum element).contract :=
  .ofPure rfl
    (by
      intro env world allowed brand arguments output values rule typed
      obtain ⟨point, rfl⟩ := annihilates_shape rule.association
      exact annihilates_total rule typed)
    (by
      intro env values value evaluated
      erase_spectral evaluated)

theorem actionEntry_sound (smooth : DeclId) (spectrum : SpectrumRef) (element : AlgebraRuntime.Poly)
    (row column : Nat) : Sound (PrimitiveBinding.actionEntry smooth spectrum element row column).contract :=
  .ofPure rfl
    (by
      intro env world allowed brand arguments output values rule typed
      obtain ⟨point, rfl⟩ := actionEntry_shape rule.association
      exact actionEntry_total rule typed)
    (by
      intro env values value evaluated
      erase_spectral evaluated)

theorem onBranch_sound (smooth line : DeclId) (branch : BranchRef) :
    Sound (PrimitiveBinding.onBranch smooth line branch).contract :=
  .ofPure rfl
    (by
      intro env world allowed brand arguments output values rule typed
      obtain ⟨point, p, rfl⟩ := onBranch_shape rule.association
      exact onBranch_total rule typed)
    (by
      intro env values value evaluated
      erase_spectral evaluated)

theorem branchDifferential_sound (smooth cotangent line : DeclId) (branch : BranchRef) :
    Sound (PrimitiveBinding.branchDifferential smooth cotangent line branch).contract :=
  .ofPure rfl
    (by
      intro env world allowed brand arguments output values rule typed
      obtain ⟨point, p, rfl⟩ := branchDifferential_shape rule.association
      exact branchDifferential_total rule typed)
    (by
      intro env values value evaluated
      erase_spectral evaluated)

theorem branchProjector_sound (smooth line : DeclId) (branch : BranchRef) (row column : Nat) :
    Sound (PrimitiveBinding.branchProjector smooth line branch row column).contract :=
  .ofPure rfl
    (by
      intro env world allowed brand arguments output values rule typed
      obtain ⟨point, p, rfl⟩ := branchProjector_shape rule.association
      exact branchProjector_total rule typed)
    (by
      intro env values value evaluated
      erase_spectral evaluated)

/-- The entry that rejects every binding is sound: its contract never holds and
it evaluates no call. -/
theorem rejected_sound : Sound (PrimitiveDescriptor.evidence fun _ => false) where
  total valid _ _ _ _ _ := absurd valid (by simp [PrimitiveDescriptor.evidence, PrimitiveDescriptor.ofBool])
  erasure evaluated := by simp [PrimitiveDescriptor.evidence, PrimitiveDescriptor.ofBool] at evaluated

/-- The transition average observation of Stage 6 (#841). Not proved yet
beyond vacuity: its entry rejects every binding (`rejected_sound`). The
instance is replaced when the entry is implemented. -/
theorem averageAt_sound (smooth line : DeclId) (average : AverageRef) :
    Sound (PrimitiveBinding.averageAt smooth line average).contract :=
  rejected_sound

end VastitasOracle.SpectralPrimitives
