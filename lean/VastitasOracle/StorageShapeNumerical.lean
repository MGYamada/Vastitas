import VastitasKernel.StorageShapeNumerical
import VastitasOracle.StorageShapes

/-! Nominal runtime-shape interpretations use the actual numerical checker.
These facts concern exact endpoints, bases and resource layouts. They do not
identify distinct same-dimensional objects or prove native floating-point laws. -/
namespace VastitasOracle.StorageShapeNumerical
open VastitasKernel Storage Shapes.Numerical

deriving instance ReflBEq, LawfulBEq for Shapes.Numerical.Space
deriving instance ReflBEq, LawfulBEq for Shapes.Numerical.Basis
deriving instance ReflBEq, LawfulBEq for Storage.Numerical.SpaceOrigin
deriving instance ReflBEq, LawfulBEq for Storage.Numerical.Space
deriving instance ReflBEq, LawfulBEq for Storage.Numerical.Basis
deriving instance ReflBEq, LawfulBEq for Storage.Layout

@[simp] theorem interpret_lookup (valuation : Shapes.Valuation) (values : Values) (name : Symbol) :
    Storage.Numerical.value? (interpret valuation values) name =
      (value? values name).map (Value.eval valuation) := by
  simp [Storage.Numerical.value?, value?, interpret, List.find?_map, Function.comp_def,
    Option.map_map]

theorem selected_valid {environment : Indexed.Environment} {values : Values}
    (valid : Valid environment values) {name : Symbol} {value : Value}
    (found : value? values name = some value) : value.Valid environment values name := by
  unfold value? at found
  cases selected : values.find? (·.1 == name) with
  | none => simp [selected] at found
  | some pair =>
    have member := List.mem_of_find?_eq_some selected
    have same : pair.1 = name := by simpa using List.find?_some selected
    have valueSame : pair.2 = value := by simpa [selected] using found
    simpa [same, valueSame] using valid.2.2.2 pair member

theorem space_guard {valuation : Shapes.Valuation} {values : Values} {name : Symbol} {space : Space}
    (holds : Shapes.guardsHold valuation (guards values))
    (found : value? values name = some (.space space)) :
    space.dimension.eval valuation ≤ dimensionLimit := by
  unfold value? at found
  cases selected : values.find? (·.1 == name) with
  | none => simp [selected] at found
  | some pair =>
    have member := List.mem_of_find?_eq_some selected
    have same : pair.2 = .space space := by simpa [selected] using found
    have bound := holds (.bound space.dimension dimensionLimit)
      (List.mem_flatMap.mpr ⟨pair, member, by simp [same]⟩)
    simpa [Shapes.Guard.eval] using bound

theorem space_valid {environment : Indexed.Environment} (valuation : Shapes.Valuation) (space : Space)
    (valid : space.Valid environment) (bound : space.dimension.eval valuation ≤ dimensionLimit) :
    (space.eval valuation).Valid environment := by
  refine ⟨valid.1, valid.2.1, valid.2.2, ?_⟩
  change space.dimension.eval valuation * space.scalar.width ≤ byteLimit
  apply Nat.le_trans (Nat.mul_le_mul_right space.scalar.width bound)
  cases coefficient : space.coefficient <;>
    simp [Space.scalar, coefficient, Scalar.width, dimensionLimit, byteLimit]

theorem compatible (valuation : Shapes.Valuation) (view : Map) (valid : view.Compatible) :
    (view.eval valuation).Compatible := by
  simpa [Map.Compatible, Map.eval, Basis.eval, Space.eval,
    Storage.Numerical.MapView.Compatible] using valid

theorem origin_valid {environment : Indexed.Environment} {values : Values}
    (valuation : Shapes.Valuation) (valid : Valid environment values)
    (name : Symbol) (view : Map) (snapshot : view.loan.layout = view.layout)
    (origin : originValid values name view = true) :
    Storage.Numerical.mapOriginValid (interpret valuation values) name (view.eval valuation) = true := by
  cases selected : view.origin with
  | none => simp [Storage.Numerical.mapOriginValid, Map.eval, selected]
  | some parent =>
    cases found : value? values parent with
    | none => simp [originValid, selected, found] at origin
    | some value => cases value with
      | space spc => simp [originValid, selected, found] at origin
      | basis bas => simp [originValid, selected, found] at origin
      | map original =>
        have parentSnapshot := (selected_valid valid found).1
        simp only [originValid, selected, found, Bool.and_eq_true, beq_iff_eq,
          decide_eq_true_eq] at origin
        rcases origin with ⟨order, ⟨⟨⟨⟨source, target⟩, allocation⟩, ancestry⟩, physical⟩⟩
        simp [Storage.Numerical.mapOriginValid, Map.eval, selected, interpret_lookup,
          found, Value.eval, Storage.Numerical.MapView.childOf, Shapes.Loan.eval,
          source, target, allocation, ancestry, snapshot, parentSnapshot, physical, order]

theorem interpreted_value {environment : Indexed.Environment} {values : Values}
    (valuation : Shapes.Valuation) (valid : Valid environment values)
    (holds : Shapes.guardsHold valuation (guards values))
    (entry : Symbol × Value) (member : entry ∈ values) :
    (entry.2.eval valuation).Valid environment (interpret valuation values) entry.1 := by
  have entryValid := valid.2.2.2 entry member
  rcases entry with ⟨name, value⟩
  cases value with
  | space spc =>
    have bounded := holds (.bound spc.dimension dimensionLimit)
      (List.mem_flatMap.mpr ⟨(name, .space spc), member, by simp⟩)
    have bound : spc.dimension.eval valuation ≤ dimensionLimit := by
      simpa [Shapes.Guard.eval] using bounded
    exact ⟨entryValid.1, space_valid valuation spc entryValid.2 bound, rfl⟩
  | basis bas =>
    refine ⟨entryValid.1, ?_, rfl⟩
    simpa [Basis.eval, Space.eval, Value.eval] using
      (show Storage.Numerical.value? (interpret valuation values) bas.space.brand =
        some (.space (bas.space.eval valuation)) by simp [entryValid.2, Value.eval])
  | map view =>
    refine ⟨compatible valuation view entryValid.2.1, ?_, ?_,
      origin_valid valuation valid name view entryValid.1 entryValid.2.2.2.2⟩
    · simpa [Map.eval, Basis.eval] using
        (show Storage.Numerical.value? (interpret valuation values) view.source.brand =
          some (.basis (view.source.eval valuation)) by simp [entryValid.2.2.1, Value.eval])
    · simpa [Map.eval, Basis.eval] using
        (show Storage.Numerical.value? (interpret valuation values) view.target.brand =
          some (.basis (view.target.eval valuation)) by simp [entryValid.2.2.2.1, Value.eval])

/-- All nominal profile/value obligations are those of the actual existing
numerical environment, for every guard-satisfying scalar valuation. -/
theorem values_valid {environment : Indexed.Environment} {values : Values}
    (valuation : Shapes.Valuation) (valid : Valid environment values)
    (holds : Shapes.guardsHold valuation (guards values)) :
    Storage.Numerical.Valid environment (interpret valuation values) := by
  refine ⟨valid.1, ?_, ?_, ?_⟩
  · simpa [interpret] using valid.2.1
  · simpa [interpret, List.map_map, Function.comp_def] using valid.2.2.1
  · intro entry member
    change entry ∈ values.map (fun original => (original.1, original.2.eval valuation)) at member
    obtain ⟨original, originalMember, equal⟩ := List.mem_map.mp member
    subst entry
    exact interpreted_value valuation valid holds original originalMember

theorem map_guards {valuation : Shapes.Valuation} {values : Values} {name : Symbol} {view : Map}
    (holds : Shapes.guardsHold valuation (guards values))
    (found : value? values name = some (.map view)) :
    Shapes.guardsHold valuation view.guards := by
  unfold value? at found
  cases selected : values.find? (·.1 == name) with
  | none => simp [selected] at found
  | some pair =>
    have member := List.mem_of_find?_eq_some selected
    have same : pair.2 = .map view := by simpa [selected] using found
    intro guard present
    exact holds guard (List.mem_flatMap.mpr ⟨pair, member, by simpa [same] using present⟩)

@[simp] theorem logical_rows (valuation : Shapes.Valuation) (layout : Shapes.Layout) :
    (layout.eval valuation).logicalRows = layout.logicalRows.eval valuation := by
  cases transposed : layout.transposed <;>
    simp [Shapes.Layout.eval, Shapes.Layout.logicalRows, Storage.Layout.logicalRows, transposed]

@[simp] theorem logical_columns (valuation : Shapes.Valuation) (layout : Shapes.Layout) :
    (layout.eval valuation).logicalColumns = layout.logicalColumns.eval valuation := by
  cases transposed : layout.transposed <;>
    simp [Shapes.Layout.eval, Shapes.Layout.logicalColumns, Storage.Layout.logicalColumns, transposed]

theorem map_live (valuation : Shapes.Valuation) (frame : Shapes.Frame) (view : Map)
    (live : view.Live frame) (snapshot : view.loan.layout = view.layout)
    (holds : Shapes.guardsHold valuation view.guards) :
    (view.eval valuation).Live (frame.eval valuation) := by
  have rows := holds (.equal view.layout.logicalRows view.target.space.dimension)
    (by simp [Map.guards])
  have columns := holds (.equal view.layout.logicalColumns view.source.space.dimension)
    (by simp [Map.guards])
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [Map.eval, Shapes.Loan.eval, live.1]
  · simpa [Map.eval, Shapes.Loan.eval] using
      (VastitasOracle.StorageShapes.eval_suspended valuation frame view.loan.name).trans live.2.1
  · cases found : frame.allocation? view.loan.allocation with
    | none => simp [Map.Live, found] at live
    | some allocation =>
      have scalar : allocation.scalar = view.source.space.scalar := by
        simpa [found] using live.2.2.1
      simp [Map.eval, Shapes.Loan.eval, Basis.eval, Space.eval, Space.scalar,
        Storage.Numerical.Space.scalar, VastitasOracle.StorageShapes.eval_allocation,
        Shapes.Allocation.eval, found, scalar]
      cases view.source.space.coefficient <;> rfl
  · simpa [Map.eval, Shapes.Loan.eval, Basis.eval, Space.eval, snapshot,
      Shapes.Guard.eval] using rows
  · simpa [Map.eval, Shapes.Loan.eval, Basis.eval, Space.eval, snapshot,
      Shapes.Guard.eval] using columns

def product_eval (valuation : Shapes.Valuation) (product : Product) : Storage.Numerical.Product :=
  ⟨product.left.eval valuation, product.right.eval valuation, product.output.eval valuation,
    product.alpha, product.beta⟩

theorem product_composable (valuation : Shapes.Valuation) (product : Product)
    (valid : product.Composable) : (product_eval valuation product).Composable := by
  exact ⟨congrArg (Basis.eval valuation) valid.1,
    congrArg (Basis.eval valuation) valid.2.1, congrArg (Basis.eval valuation) valid.2.2⟩

/-- The same symbolic numerical product reaches the actual existing numerical
checker, including live nominal views and its real checked GEMM. No sampled
size, independently chosen rectangle, or native floating-point law is used. -/
theorem product_realizes {environment : Indexed.Environment} {frame : Shapes.Frame} {values : Values}
    {left right output : Symbol} {mode : GemmMode} {policy : NumericalPolicy}
    {alpha beta : Option Coefficient}
    (valuation : Shapes.Valuation)
    (checked : CheckedProduct environment frame values left right output mode policy alpha beta)
    (prior : Shapes.guardsHold valuation frame.guards)
    (nominal : Shapes.guardsHold valuation (guards values))
    (emitted : Shapes.guardsHold valuation checked.storage.guards) :
    ∃ actual,
      Storage.Numerical.checkProduct environment (frame.eval valuation) (interpret valuation values)
        left right output mode policy alpha beta = .ok actual ∧
      actual.product = product_eval valuation checked.product := by
  have resourcesValid := VastitasOracle.StorageShapes.frame_audited valuation frame
    checked.storage.beforeValid prior
  have valuesValid := values_valid valuation checked.valuesValid nominal
  have leftFrom : Storage.Numerical.value? (interpret valuation values) left =
      some (.map (checked.product.left.eval valuation)) := by simp [checked.leftFrom, Value.eval]
  have rightFrom : Storage.Numerical.value? (interpret valuation values) right =
      some (.map (checked.product.right.eval valuation)) := by simp [checked.rightFrom, Value.eval]
  have outputFrom : Storage.Numerical.value? (interpret valuation values) output =
      some (.map (checked.product.output.eval valuation)) := by simp [checked.outputFrom, Value.eval]
  have composable := product_composable valuation checked.product checked.composable
  have leftLive := map_live valuation frame checked.product.left checked.leftLive
    (selected_valid checked.valuesValid checked.leftFrom).1 (map_guards nominal checked.leftFrom)
  have rightLive := map_live valuation frame checked.product.right checked.rightLive
    (selected_valid checked.valuesValid checked.rightFrom).1 (map_guards nominal checked.rightFrom)
  have outputLive := map_live valuation frame checked.product.output checked.outputLive
    (selected_valid checked.valuesValid checked.outputFrom).1 (map_guards nominal checked.outputFrom)
  have executed := (VastitasOracle.StorageShapes.gemm_step valuation frame
    (checked.product.request mode policy) checked.storage prior emitted).1
  cases storageAccepted : checkGemm (frame.eval valuation) (checked.product.request mode policy) with
  | error diagnostic => simp [Storage.executeAction, storageAccepted, bind, Except.bind] at executed
  | ok storage =>
    have selected : (⟨checked.product.left.eval valuation, checked.product.right.eval valuation,
        checked.product.output.eval valuation, alpha, beta⟩ : Storage.Numerical.Product) = product_eval valuation checked.product := by
      simp [product_eval, checked.coefficients.1, checked.coefficients.2]
    simp only [Storage.Numerical.checkProduct, resourcesValid, valuesValid, ↓reduceDIte]
    split
    next a b c ha hb hc =>
      have ea : a = checked.product.left.eval valuation := by simpa [leftFrom] using ha.symm
      have eb : b = checked.product.right.eval valuation := by simpa [rightFrom] using hb.symm
      have ec : c = checked.product.output.eval valuation := by simpa [outputFrom] using hc.symm
      subst a b c
      simp only [selected, composable, leftLive, rightLive, outputLive, ↓reduceDIte]
      have direct : (checked.product.output.eval valuation).conjugate = false := rfl
      simp only [direct, ↓reduceDIte]
      have request : (⟨checked.product.left.eval valuation, checked.product.right.eval valuation,
          checked.product.output.eval valuation, alpha, beta⟩ : Storage.Numerical.Product).request mode policy =
          checked.product.request mode policy := by
        simp only [Storage.Numerical.Product.request, Map.eval, Shapes.Loan.eval,
          Product.request, checked.coefficients.1, checked.coefficients.2]
      have succeeds : (checkGemm (frame.eval valuation)
          ((⟨checked.product.left.eval valuation, checked.product.right.eval valuation,
            checked.product.output.eval valuation, alpha, beta⟩ : Storage.Numerical.Product).request mode policy)).isOk = true := by
        have same := congrArg (fun request => (checkGemm (frame.eval valuation) request).toBool) request
        rw [storageAccepted] at same
        exact same
      split
      next diagnostic rejected => simp [rejected, Except.isOk, Except.toBool] at succeeds
      next actualStorage accepted =>
        exact ⟨_, rfl, selected⟩
    next noMaps => exact False.elim (noMaps _ _ _ leftFrom rightFrom outputFrom)

end VastitasOracle.StorageShapeNumerical
