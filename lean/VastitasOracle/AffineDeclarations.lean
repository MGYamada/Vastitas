import VastitasOracle.AlgebraBasis
import VastitasKernel.IndexedValidity

/-! Structural soundness of presented affine declarations (Stage 2).

An accepted `.affine` entry has a presented implementation, a finite and
duplicate-free declared base chain through presented objects, and stored
data whose certificate and structure map pass the exact checks of
`AlgebraBasis` and `AlgebraDeclarations`. The `structural` constraint holds
only for canonical global objects on such a chain.

Non-regression: presented implementations are never descriptor
implementations. The sealed two-index point and morphism families, whose
validity requires descriptor domains, therefore never range over presented
objects, and their contracts are unchanged.

All statements are about kernel data and `Poly` operations. Their
mathematical meaning (presented algebras, structure morphisms, `Spec`)
is proved in the mathlib bridge. -/
namespace VastitasOracle.AffineDeclarations

open VastitasKernel VastitasKernel.Indexed VastitasKernel.AlgebraRuntime
open VastitasKernel.AlgebraBasis VastitasKernel.AlgebraDeclarations
open VastitasOracle.AlgebraBasis

/-- The exact structure-map facts recorded for an object over `base`. -/
structure StructureValid (data base : AffineData) : Prop where
  names : (data.bindings.map (·.1)).length = base.arity ∧ (data.bindings.map (·.1)).Nodup ∧
    (data.bindings.map (·.1)).all (base.generators.contains ·) = true
  images_length : data.structureImages.length = base.arity
  pullback : ∀ g ∈ base.basis, ∃ quotients,
    combination quotients data.basis = Poly.subst data.arity data.structureImages g

/-- What a successful `checkAffine` establishes. -/
structure AffineValid (data : AffineData) (base : Option AffineData) : Prop where
  arity_bounded : data.arity ≤ Limits.algebraGenerators
  generators_distinct : data.generators.Nodup
  certificate : CertificateValid data.certificate
  unbased : data.base = none → base = none ∧ data.bindings = [] ∧ data.structureImages = []
  based : ∀ b, base = some b → data.base.isSome = true ∧ StructureValid data b

theorem checkMember_ok {basis : List Poly} {image : Poly} {error : Error} {s s' : Nat}
    (h : (checkMember basis image error).run s = .ok ((), s')) :
    ∃ quotients, combination quotients basis = image := by
  unfold checkMember at h
  obtain ⟨division, _, _, h⟩ := bind_ok h
  obtain ⟨identity, _, hidentity, h⟩ := bind_ok h
  have hc := ensure_ok h
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  exact ⟨division.quotients, combine_ok hidentity ▸ hc.2⟩

theorem checkPullback_ok {data : AffineData} {g : Poly} {s s' : Nat}
    (h : (checkPullback data g).run s = .ok ((), s')) :
    ∃ quotients, combination quotients data.basis = Poly.subst data.arity data.structureImages g := by
  unfold checkPullback at h
  obtain ⟨_, _, _, h⟩ := bind_ok h
  obtain ⟨q, _, hq, h⟩ := bind_ok h
  rw [← substitute_ok hq]
  exact checkMember_ok h

theorem checkStructure_sound {data base : AffineData} {s s' : Nat}
    (h : (checkStructure data base).run s = .ok ((), s')) : StructureValid data base := by
  unfold checkStructure at h
  obtain ⟨_, _, hnames, h⟩ := bind_ok h
  obtain ⟨_, _, _, h⟩ := bind_ok h
  obtain ⟨_, _, hlength, h⟩ := bind_ok h
  obtain ⟨_, _, _, hpullback⟩ := bind_ok h
  have hnames := ensure_ok hnames
  have hlength := ensure_ok hlength
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hnames hlength
  exact {
    names := ⟨hnames.1.1, hnames.1.2, hnames.2⟩
    images_length := hlength
    pullback := fun g member => by
      obtain ⟨_, _, hg⟩ := forM_ok hpullback g member
      exact checkPullback_ok hg }

theorem checkAffine_sound {data : AffineData} {base : Option AffineData} {s s' : Nat}
    (h : (checkAffine data base).run s = .ok ((), s')) : AffineValid data base := by
  unfold checkAffine at h
  obtain ⟨_, _, harity, h⟩ := bind_ok h
  obtain ⟨_, _, hdistinct, h⟩ := bind_ok h
  obtain ⟨_, _, hverify, h⟩ := bind_ok h
  have harity := ensure_ok harity
  have hdistinct := ensure_ok hdistinct
  simp only [decide_eq_true_eq] at harity hdistinct
  have certificate := verify_sound hverify
  cases hbase : data.base <;> cases base <;> simp only [hbase] at h
  · have hc := ensure_ok h
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    refine ⟨harity, hdistinct, certificate, fun _ => ⟨rfl, hc.1, hc.2⟩, ?_⟩
    intro _ absurd
    cases absurd
  · simp [StateT.run, throw, throwThe, MonadExceptOf.throw, StateT.lift, bind, Except.bind] at h
  · simp [StateT.run, throw, throwThe, MonadExceptOf.throw, StateT.lift, bind, Except.bind] at h
  · rename_i b
    refine ⟨harity, hdistinct, certificate, (fun absurd => by simp [hbase] at absurd), ?_⟩
    intro b' same
    cases same
    exact ⟨by simp [hbase], checkStructure_sound h⟩

theorem validAffineData_sound {data : AffineData} {base : Option AffineData}
    (h : validAffineData data base = true) : AffineValid data base := by
  unfold validAffineData run at h
  cases result : (checkAffine data base).run 0 with
  | error e => simp [result, Except.map, Except.isOk, Except.toBool] at h
  | ok pair => exact checkAffine_sound (s' := pair.2) (by simpa using result)

/-- A stored structure image is the normal form of its declared binding. -/
theorem checkImage_ok {data : AffineData} {entry : String × Poly} {s s' : Nat}
    (h : (checkImage data entry).run s = .ok ((), s')) :
    ∃ declared, data.binding? entry.1 = some declared ∧ normalForm data.basis declared = entry.2 := by
  unfold checkImage at h
  cases hb : data.binding? entry.1 with
  | none => simp only [hb] at h; exact (throw_not_ok h).elim
  | some declared =>
    simp only [hb] at h
    obtain ⟨division, _, hd, h⟩ := bind_ok h
    have he := ensure_ok h
    simp only [beq_iff_eq] at he
    refine ⟨declared, rfl, ?_⟩
    rw [← he, divide_ok hd]
    rfl

/-- Accepted structure maps store canonical images: each is the normal form of
its binding (which `StructureValid` does not record). -/
theorem checkStructure_images_normal {data base : AffineData} {s s' : Nat}
    (h : (checkStructure data base).run s = .ok ((), s')) :
    ∀ entry ∈ base.generators.zip data.structureImages,
      ∃ declared, data.binding? entry.1 = some declared ∧ normalForm data.basis declared = entry.2 := by
  unfold checkStructure at h
  obtain ⟨_, _, _, h⟩ := bind_ok h
  obtain ⟨_, _, _, h⟩ := bind_ok h
  obtain ⟨_, _, _, h⟩ := bind_ok h
  obtain ⟨_, _, himages, _⟩ := bind_ok h
  intro entry member
  obtain ⟨_, _, he⟩ := forM_ok himages entry member
  exact checkImage_ok he

theorem validAffineData_images_normal {data base : AffineData} (h : validAffineData data (some base) = true) :
    ∀ entry ∈ base.generators.zip data.structureImages,
      ∃ declared, data.binding? entry.1 = some declared ∧ normalForm data.basis declared = entry.2 := by
  unfold validAffineData run at h
  cases result : (checkAffine data (some base)).run 0 with
  | error e => simp [result, Except.map, Except.isOk, Except.toBool] at h
  | ok pair =>
    have hc : (checkAffine data (some base)).run 0 = .ok ((), pair.2) := by simpa using result
    unfold checkAffine at hc
    obtain ⟨_, _, _, hc⟩ := bind_ok hc
    obtain ⟨_, _, _, hc⟩ := bind_ok hc
    obtain ⟨_, _, _, hc⟩ := bind_ok hc
    cases hbase : data.base <;> simp only [hbase] at hc
    · simp [StateT.run, throw, throwThe, MonadExceptOf.throw, StateT.lift, bind, Except.bind] at hc
    · exact checkStructure_images_normal hc

/-- Every accepted declaration over a presented base stores canonical structure images. -/
theorem validAffine_images_normal {env : Environment} {id implementation baseRef : DeclId}
    {data base : AffineData} (h : validAffine env id implementation data = true)
    (hbase : data.base = some baseRef) (hdata : affineData? env baseRef = some base) :
    ∀ entry ∈ base.generators.zip data.structureImages,
      ∃ declared, data.binding? entry.1 = some declared ∧ normalForm data.basis declared = entry.2 := by
  unfold validAffine at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨_, _⟩, _⟩, valid⟩, _⟩ := h
  simp only [hbase, Option.bind, hdata] at valid
  exact validAffineData_images_normal valid

/-- A declared chain starts at the object, is bounded by its fuel, and stays
within presented objects. -/
theorem affineChain_spec {env : Environment} :
    ∀ {fuel : Nat} {id : DeclId} {chain : List DeclId}, affineChain env fuel id = some chain →
      chain.head? = some id ∧ chain.length ≤ fuel ∧ ∀ x ∈ chain, (affineData? env x).isSome = true
  | 0, _, _, h => by simp [affineChain] at h
  | fuel + 1, id, chain, h => by
    unfold affineChain at h
    cases hdata : affineData? env id with
    | none => simp [hdata] at h
    | some data =>
      cases hbase : data.base with
      | none =>
        simp [hdata, hbase] at h
        subst h
        simp [hdata]
      | some base =>
        cases hrest : affineChain env fuel base with
        | none => simp [hdata, hbase, hrest] at h
        | some rest =>
          simp [hdata, hbase, hrest] at h
          subst h
          obtain ⟨_, length, members⟩ := affineChain_spec hrest
          refine ⟨rfl, by simp; omega, ?_⟩
          intro x member
          rcases List.mem_cons.mp member with rfl | member
          · simp [hdata]
          · exact members x member

theorem chainOf_spec {env : Environment} {id : DeclId} {chain : List DeclId}
    (h : chainOf env id = some chain) :
    chain.head? = some id ∧ chain.length ≤ Limits.algebraChain ∧
      ∀ x ∈ chain, (affineData? env x).isSome = true :=
  affineChain_spec h

/-- An accepted presented declaration. -/
theorem validAffine_sound {env : Environment} {id implementation : DeclId} {data : AffineData}
    (h : validAffine env id implementation data = true) :
    presentedImplementation env implementation = true ∧
      (∃ chain, chainOf env id = some chain ∧ chain.Nodup ∧ chain.length ≤ Limits.algebraChain) ∧
      AffineValid data (data.base.bind (affineData? env)) ∧
      validConstruction data (affineData? env) = true := by
  unfold validAffine at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨presented, chain⟩, _⟩, valid⟩, construction⟩ := h
  refine ⟨presented, ?_, validAffineData_sound valid, construction⟩
  cases hchain : chainOf env id with
  | none => simp [hchain] at chain
  | some list =>
    simp only [hchain, decide_eq_true_eq] at chain
    exact ⟨list, rfl, chain, (chainOf_spec hchain).2.1⟩

/-- The structural constraint relates two canonical globals on a declared chain. -/
theorem structural_holds {env : Environment} {indices : List Index} {object base : Nat}
    (h : (Constraint.structural object base).Holds env indices) :
    ∃ x b chain, indices[object]? = some (.object (.global x)) ∧
      indices[base]? = some (.object (.global b)) ∧ chainOf env x = some chain ∧ b ∈ chain := by
  obtain ⟨x, b, hx, hb, on⟩ := h
  unfold onChain at on
  cases hchain : chainOf env x with
  | none => simp [hchain] at on
  | some chain =>
    simp only [hchain, List.contains_iff_mem] at on
    exact ⟨x, b, chain, hx, hb, hchain, on⟩

/-- Presented implementations are never descriptor implementations. -/
theorem presented_not_descriptor {env : Environment} {id : DeclId}
    (h : presentedImplementation env id = true) : affineImplementation env id = false := by
  unfold presentedImplementation at h
  unfold affineImplementation
  split at h <;> simp_all

/-- Non-regression: the sealed two-index point and morphism contracts still
require descriptor domains, so no presented implementation enters them. -/
theorem sealed_families_exclude_presented {env : Environment} {f : Family}
    (valid : f.Valid env) (sealed : f.representation = .point ∨ f.representation = .morphism)
    {domain : DeclId} (parameter : Parameter.object domain ∈ f.parameters) {id : DeclId}
    (member : id ∈ Indexed.domain env domain) : presentedImplementation env id = false := by
  obtain ⟨_, _, _, representation⟩ := valid
  have all : f.parameters.all (fun p => match p with
      | .object id => (Indexed.domain env id).all (affineImplementation env)
      | _ => true) = true := by
    rcases sealed with sealed | sealed <;> simp only [sealed] at representation <;>
      exact representation.2.2.2.2
  have descriptor := List.all_eq_true.mp (List.all_eq_true.mp all _ parameter) id member
  cases presented : presentedImplementation env id
  · rfl
  · rw [presented_not_descriptor presented] at descriptor
    cases descriptor

end VastitasOracle.AffineDeclarations
