import VastitasOracle.ElaborationBase
import VastitasOracle.DeclarationSafety

namespace VastitasOracle.Elaboration

open VastitasKernel VastitasKernel.Checker.Internal VastitasKernel.Elaboration

inductive ResolvedAnnotation (ctx : Context) : Option RawType → Option Ty → Prop
  | none : ResolvedAnnotation ctx none none
  | some {raw ty} : VastitasKernel.Declaration.TypeAnnotation ctx raw ty →
      ResolvedAnnotation ctx (some raw) (some ty)

theorem resolveAnnotation_corresponds (ctx : Context) (raw : Option RawType) (span : Span) :
    Establishes (raw.mapM fun annotation => resolveType ctx annotation span)
      (ResolvedAnnotation ctx raw) := by
  cases raw with
  | none => exact establishes_pure ResolvedAnnotation.none
  | some raw =>
      simp only [Option.mapM, map_eq_pure_bind]
      apply establishes_bind (VastitasOracle.Declaration.resolveType_corresponds ctx raw span)
      intro ty corresponds
      exact establishes_pure (ResolvedAnnotation.some corresponds)

theorem annotation_matches {ctx : Context} {raw : Option RawType} {expected : Option Ty}
    {value : Result} (resolved : ResolvedAnnotation ctx raw expected)
    (matchesType : MatchesExpected expected value) : Annotation ctx raw value.term.ty := by
  cases resolved with
  | none => trivial
  | some corresponds =>
      change VastitasKernel.Declaration.TypeAnnotation _ _ _
      rw [matchesType _ rfl]
      exact corresponds

theorem checkArguments_step (previous : SoundAt fuel) (signatures : Signatures) (ctx : Context)
    (params : List Binding) (raws : List RawExpr) (substitutions : List (ObjectRef × ObjectRef)) (span : Span) :
    Establishes (checkArguments (fuel + 1) signatures ctx params raws substitutions span)
      (fun result => Arguments signatures ctx raws result.1) := by
  cases params with
  | nil =>
      cases raws with
      | nil => exact establishes_pure Arguments.nil
      | cons raw rest => exact establishes_fail _ _ _ _ _
  | cons param params =>
      cases raws with
      | nil => exact establishes_fail _ _ _ _ _
      | cons raw rest =>
          simp only [checkArguments]
          apply establishes_bind (previous.expr signatures ctx raw _)
          intro value corresponds
          split
          · apply establishes_bind_any
            intro target
            simp only [pure_bind]
            apply establishes_bind (previous.arguments signatures ctx params rest _ span)
            intro result tailCorresponds
            exact establishes_pure (Arguments.cons corresponds tailCorresponds)
          · simp only [pure_bind]
            apply establishes_bind (previous.arguments signatures ctx params rest _ span)
            intro result tailCorresponds
            exact establishes_pure (Arguments.cons corresponds tailCorresponds)

theorem checkBlock_step (previous : SoundAt fuel) (signatures : Signatures) (ctx : Context)
    (raw : RawBlock) (expected : Option Ty) :
    Establishes (checkBlock (fuel + 1) signatures ctx raw expected)
      (fun result => Block signatures ctx raw result.term) := by
  cases raw with
  | mk statements result span =>
      simp only [checkBlock]
      apply establishes_bind (previous.statements signatures ctx statements result expected)
      intro checked corresponds
      apply establishes_bind (checkEscape_scoped ctx checked span)
      intro _ inScope
      exact establishes_pure (Block.mk corresponds inScope)

theorem checkStatements_step (previous : SoundAt fuel) (signatures : Signatures) (ctx : Context)
    (statements : List RawStmt) (result : RawExpr) (expected : Option Ty) :
    Establishes (checkStatements (fuel + 1) signatures ctx statements result expected)
      (fun checked => Statements signatures ctx statements result checked.term) := by
  cases statements with
  | nil =>
      exact establishes_mono (previous.expr signatures ctx result expected)
        (fun _ corresponds => Statements.nil corresponds)
  | cons statement rest =>
      cases statement with
      | letE name annotation raw span =>
          simp only [checkStatements]
          apply establishes_bind_any
          intro _
          split
          · apply establishes_unreachable
            exact establishes_fail _ _ _ _ _
          · apply establishes_bind (resolveAnnotation_corresponds ctx annotation span)
            intro checkedAnnotation resolvedAnnotation
            apply establishes_bind (establishes_and
              (previous.expr signatures ctx raw checkedAnnotation)
              (checkExpr_matches fuel signatures ctx raw checkedAnnotation))
            intro value valueFacts
            obtain ⟨valueCorresponds, valueMatches⟩ := valueFacts
            have annotated := annotation_matches resolvedAnnotation valueMatches
            apply establishes_bind_any
            intro symbol
            split
            · apply establishes_bind_any
              intro _
              apply establishes_bind (previous.statements signatures _ rest result expected)
              intro body bodyCorresponds
              exact establishes_pure (Statements.letE annotated valueCorresponds bodyCorresponds)
            · apply establishes_bind (previous.statements signatures _ rest result expected)
              intro body bodyCorresponds
              exact establishes_pure (Statements.letE annotated valueCorresponds bodyCorresponds)
      | unpack raw scheme point span =>
          simp only [checkStatements]
          apply establishes_bind_any
          intro _
          apply establishes_bind_any
          intro _
          split
          · apply establishes_unreachable
            exact establishes_fail _ _ _ _ _
          · split
            · apply establishes_unreachable
              exact establishes_fail _ _ _ _ _
            · apply establishes_bind (previous.expr signatures ctx raw none)
              intro value valueCorresponds
              split
              · rename_i base valueType
                apply establishes_bind_any
                intro objectSymbol
                apply establishes_bind_any
                intro pointSymbol
                apply establishes_bind_any
                intro _
                apply establishes_bind (previous.statements signatures _ rest result expected)
                intro body bodyCorresponds
                exact establishes_pure (Statements.unpack valueCorresponds valueType bodyCorresponds)
              · apply establishes_bind_any
                intro _
                apply establishes_bind_any
                intro _
                exact establishes_fail _ _ _ _ _

end VastitasOracle.Elaboration
