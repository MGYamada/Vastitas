import VastitasKernel.Declaration
import VastitasOracle.ElaborationBase

namespace VastitasOracle.Declaration

open VastitasKernel VastitasKernel.Checker.Internal
open VastitasOracle.Elaboration

theorem parseBase_corresponds (ring : String) (span : Span) :
    Establishes (parseBase ring span) (fun base => VastitasKernel.Declaration.Base ring base) := by
  unfold parseBase
  split
  · exact establishes_pure .qq
  · exact establishes_pure .cinfReal
  · exact establishes_fail _ _ _ _ _

theorem resolveIndex_corresponds (ctx : Context) (raw : RawIndex) (span : Span) :
    Establishes (resolveIndex ctx raw span) (fun ref => VastitasKernel.Declaration.Index ctx raw ref) := by
  cases raw with
  | base ring =>
      unfold resolveIndex
      apply establishes_bind (parseBase_corresponds ring span)
      intro base corresponds
      exact establishes_pure (.base corresponds)
  | name name =>
      unfold resolveIndex
      apply establishes_bind (getBinding_resolves ctx name span)
      intro binding found
      split
      · rename_i ref objectRef
        exact establishes_pure (.name found objectRef)
      · exact establishes_fail _ _ _ _ _

theorem resolveType_corresponds (ctx : Context) (raw : RawType) (span : Span) :
    Establishes (resolveType ctx raw span) (fun ty => VastitasKernel.Declaration.TypeAnnotation ctx raw ty) := by
  have finish (ty : Ty) (corresponds : VastitasKernel.Declaration.TypeAnnotation ctx raw ty) :
      Establishes (do
        unless decide ty.WellFormed do
          fail span "E_BASE" s!"incompatible geometric settings or bases in {← typeLabel ctx ty}"
            (← objectNotes ctx ty.refs)
        pure ty) (fun result => VastitasKernel.Declaration.TypeAnnotation ctx raw result) := by
    split
    · exact establishes_pure corresponds
    · apply establishes_bind_any
      intro _
      apply establishes_bind_any
      intro _
      apply establishes_unreachable
      exact establishes_fail _ _ _ _ _
  cases raw with
  | named name =>
      simp only [resolveType]
      split
      · rename_i equal
        have same := RawType.named.inj equal
        subst name
        exact establishes_pure .nat
      · rename_i equal
        have same := RawType.named.inj equal
        subst name
        exact establishes_pure .int
      · rename_i equal
        have same := RawType.named.inj equal
        subst name
        exact establishes_pure .bool
      · rename_i equal
        have same := RawType.named.inj equal
        subst name
        exact establishes_pure .unit
      · rename_i equal
        have same := RawType.named.inj equal
        subst name
        exact establishes_pure .scheme
      · rename_i equal
        have same := RawType.named.inj equal
        subst name
        exact establishes_pure .cinfScheme
      · apply establishes_unreachable
        exact establishes_fail _ _ _ _ _
      all_goals contradiction
  | pair element =>
      simp only [resolveType]
      split <;> try contradiction
      · rename_i equal
        have same := RawType.pair.inj equal
        subst element
        exact establishes_pure .pairNat
      · rename_i equal
        have same := RawType.pair.inj equal
        subst element
        exact establishes_pure .pairInt
      · apply establishes_unreachable
        exact establishes_fail _ _ _ _ _
      all_goals contradiction
  | point target source =>
      simp only [resolveType]
      apply establishes_bind (resolveIndex_corresponds ctx target span)
      intro targetRef targetCorresponds
      apply establishes_bind (resolveIndex_corresponds ctx source span)
      intro sourceRef sourceCorresponds
      simpa only [pure_bind] using finish _ (.point targetCorresponds sourceCorresponds)
  | morphism source target =>
      simp only [resolveType]
      apply establishes_bind (resolveIndex_corresponds ctx source span)
      intro sourceRef sourceCorresponds
      apply establishes_bind (resolveIndex_corresponds ctx target span)
      intro targetRef targetCorresponds
      simpa only [pure_bind] using finish _ (.morphism sourceCorresponds targetCorresponds)
  | pointed setting ring =>
      simp only [resolveType]
      apply establishes_bind (parseBase_corresponds ring span)
      intro base baseCorresponds
      split
      · rename_i same
        exact establishes_pure (.pointed baseCorresponds (eq_of_beq same))
      · apply establishes_unreachable
        exact establishes_fail _ _ _ _ _

theorem prepareParameters_corresponds (ctx : Context) (raw : List RawParam) :
    Establishes (prepareParameters ctx raw)
      (fun final => VastitasKernel.Declaration.Parameters ctx raw final) := by
  induction raw generalizing ctx with
  | nil => exact establishes_pure (.nil ctx)
  | cons param rest ih =>
      simp only [prepareParameters]
      apply establishes_bind_any
      intro _
      apply establishes_bind (resolveType_corresponds ctx param.ty param.span)
      intro ty corresponds
      apply establishes_bind_any
      intro symbol
      cases ty <;> dsimp only
      all_goals try
        apply establishes_bind_any
        intro _
      all_goals
        apply establishes_mono (ih _)
        intro final restCorresponds
        exact .cons ⟨rfl, corresponds, rfl⟩ restCorresponds

theorem prepareSignature_corresponds (raw : RawFunction) :
    Establishes (prepareSignature raw) (fun signature => VastitasKernel.Declaration.Signature raw signature) := by
  unfold prepareSignature
  apply establishes_bind_any
  intro _
  apply establishes_bind_any
  intro id
  apply establishes_bind (prepareParameters_corresponds [] raw.params)
  intro params paramsCorrespond
  apply establishes_bind (resolveType_corresponds params raw.returnType raw.span)
  intro result resultCorresponds
  split
  · apply establishes_unreachable
    exact establishes_fail _ _ _ _ _
  · exact establishes_pure ⟨rfl, paramsCorrespond, resultCorresponds⟩

end VastitasOracle.Declaration
