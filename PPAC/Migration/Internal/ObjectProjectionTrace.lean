import PPAC.Migration.Internal.ProjectionRuleConstruction
import PPAC.Migration.Internal.ProjectionTraceUnfold

/-! 原七规则投影闭轨迹、实际赋值界及全根一步展开的原核闭句。 -/
namespace PPAC.Migration.Internal.ObjectProjectionTrace
open Source SourceAlgebra SourceLogic OmegaSyntax

def projectionTraceNaturalSentence {m} (w r : Fin m) : Source.Sentence := ((ProjectionTraceSyntax.condition w r).imp ((Formula.mem r w))).close

theorem source_projectionTraceNatural {m} (w r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (projectionTraceNaturalSentence w r) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (ProjectionTraceSyntax.condition w r) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (ProjectionTraceSyntax.condition w r) := .hyp (Or.inl rfl)
  exact ProjectionTraceSyntax.condition_natural w r h0

theorem projectionTraceNatural_kernel_certificate {m} (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (projectionTraceNaturalSentence w r)) := TheoryTransport.sentence (source_projectionTraceNatural w r)

theorem native_projectionTraceNatural {m} (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (projectionTraceNaturalSentence w r)) := ZFReplay.replay (projectionTraceNatural_kernel_certificate w r)

def projectionTraceOriginalStepSentence {m} (w r : Fin m) : Source.Sentence := ((ProjectionTraceSyntax.condition w r).imp ((HornStepSyntax.step YesMetaZFC.Automation.ObjectProjection.rules w r w))).close

theorem source_projectionTraceOriginalStep {m} (w r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (projectionTraceOriginalStepSentence w r) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (ProjectionTraceSyntax.condition w r) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (ProjectionTraceSyntax.condition w r) := .hyp (Or.inl rfl)
  exact ProjectionTraceSyntax.condition_step w r h0

theorem projectionTraceOriginalStep_kernel_certificate {m} (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (projectionTraceOriginalStepSentence w r)) := TheoryTransport.sentence (source_projectionTraceOriginalStep w r)

theorem native_projectionTraceOriginalStep {m} (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (projectionTraceOriginalStepSentence w r)) := ZFReplay.replay (projectionTraceOriginalStep_kernel_certificate w r)

def projectionTraceSetExistsSentence {m} (w : Fin m) : Source.Sentence := ((ProjectionTraceSetSyntax.existsValue w)).close

theorem source_projectionTraceSetExists {m} (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (projectionTraceSetExistsSentence w) := by
  apply close_derives
  let Δ : Context m := Source.SetLanguage.ZF.at m
  have hZ : ZFContext.Evidence Δ := by
    exact ZFContext.source_ZF m
  exact ProjectionTraceSet.exists_value hZ w

theorem projectionTraceSetExists_kernel_certificate {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (projectionTraceSetExistsSentence w)) := TheoryTransport.sentence (source_projectionTraceSetExists w)

theorem native_projectionTraceSetExists {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (projectionTraceSetExistsSentence w)) := ZFReplay.replay (projectionTraceSetExists_kernel_certificate w)

def projectionTraceAllRootsUnfoldSentence {m} (w : Fin m) : Source.Sentence := ((ProjectionTraceUnfold.existsUnfolded w)).close

theorem source_projectionTraceAllRootsUnfold {m} (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (projectionTraceAllRootsUnfoldSentence w) := by
  apply close_derives
  let Δ : Context m := Source.SetLanguage.ZF.at m
  have hZ : ZFContext.Evidence Δ := by
    exact ZFContext.source_ZF m
  exact ProjectionTraceUnfold.exists_unfolded hZ w

theorem projectionTraceAllRootsUnfold_kernel_certificate {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (projectionTraceAllRootsUnfoldSentence w)) := TheoryTransport.sentence (source_projectionTraceAllRootsUnfold w)

theorem native_projectionTraceAllRootsUnfold {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (projectionTraceAllRootsUnfoldSentence w)) := ZFReplay.replay (projectionTraceAllRootsUnfold_kernel_certificate w)

def projectionTraceAtActualSetIffSentence {m} (w V r : Fin m) : Source.Sentence := ((ProjectionTraceSetSyntax.value w V).imp ((Formula.mem r w).imp (((ProjectionTraceSyntax.condition w r).iff (HornStepSyntax.step YesMetaZFC.Automation.ObjectProjection.rules w r V))))).close

theorem source_projectionTraceAtActualSetIff {m} (w V r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (projectionTraceAtActualSetIffSentence w V r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem r w) (Context.add (ProjectionTraceSetSyntax.value w V) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (ProjectionTraceSetSyntax.value w V) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (Formula.mem r w) := .hyp (Or.inl rfl)
  exact ProjectionTraceUnfold.unfold_iff hZ w V r h0 h1

theorem projectionTraceAtActualSetIff_kernel_certificate {m} (w V r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (projectionTraceAtActualSetIffSentence w V r)) := TheoryTransport.sentence (source_projectionTraceAtActualSetIff w V r)

theorem native_projectionTraceAtActualSetIff {m} (w V r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (projectionTraceAtActualSetIffSentence w V r)) := ZFReplay.replay (projectionTraceAtActualSetIff_kernel_certificate w V r)

def projectionActualHeadBoundSentence {m} (rule : YesMetaZFC.Automation.ObjectHorn.Rule) (env : Fin rule.arity → Fin m) (w r : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat rule.arity w env).imp ((HornExprSyntax.graph rule.head w env r).imp ((HornExprBounds.environmentBound rule.arity r env))))).close

theorem source_projectionActualHeadBound {m} (rule : YesMetaZFC.Automation.ObjectHorn.Rule) (hr : rule ∈ YesMetaZFC.Automation.ObjectProjection.rules) (env : Fin rule.arity → Fin m) (w r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (projectionActualHeadBoundSentence rule env w r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.graph rule.head w env r) (Context.add (HornExprSyntax.environmentNat rule.arity w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat rule.arity w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (HornExprSyntax.graph rule.head w env r) := .hyp (Or.inl rfl)
  exact ProjectionRuleConstruction.head_bound hZ rule hr w r env h0 h1 h2

theorem projectionActualHeadBound_kernel_certificate {m} (rule : YesMetaZFC.Automation.ObjectHorn.Rule) (hr : rule ∈ YesMetaZFC.Automation.ObjectProjection.rules) (env : Fin rule.arity → Fin m) (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (projectionActualHeadBoundSentence rule env w r)) := TheoryTransport.sentence (source_projectionActualHeadBound rule hr env w r)

theorem native_projectionActualHeadBound {m} (rule : YesMetaZFC.Automation.ObjectHorn.Rule) (hr : rule ∈ YesMetaZFC.Automation.ObjectProjection.rules) (env : Fin rule.arity → Fin m) (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (projectionActualHeadBoundSentence rule env w r)) := ZFReplay.replay (projectionActualHeadBound_kernel_certificate rule hr env w r)

def projectionActualRuleApplicationSentence {m} (rule : YesMetaZFC.Automation.ObjectHorn.Rule) (env : Fin rule.arity → Fin m) (w r R : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat rule.arity w env).imp ((HornExprSyntax.graph rule.head w env r).imp ((HornRuleSyntax.premises rule.premises w R env).imp ((HornApplicationSyntax.application rule w r R)))))).close

theorem source_projectionActualRuleApplication {m} (rule : YesMetaZFC.Automation.ObjectHorn.Rule) (hr : rule ∈ YesMetaZFC.Automation.ObjectProjection.rules) (env : Fin rule.arity → Fin m) (w r R : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (projectionActualRuleApplicationSentence rule env w r R) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornRuleSyntax.premises rule.premises w R env) (Context.add (HornExprSyntax.graph rule.head w env r) (Context.add (HornExprSyntax.environmentNat rule.arity w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (HornExprSyntax.environmentNat rule.arity w env) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (HornExprSyntax.graph rule.head w env r) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (HornRuleSyntax.premises rule.premises w R env) := .hyp (Or.inl rfl)
  exact ProjectionRuleConstruction.application hZ rule hr w r R env h0 h1 h2 h3

theorem projectionActualRuleApplication_kernel_certificate {m} (rule : YesMetaZFC.Automation.ObjectHorn.Rule) (hr : rule ∈ YesMetaZFC.Automation.ObjectProjection.rules) (env : Fin rule.arity → Fin m) (w r R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (projectionActualRuleApplicationSentence rule env w r R)) := TheoryTransport.sentence (source_projectionActualRuleApplication rule hr env w r R)

theorem native_projectionActualRuleApplication {m} (rule : YesMetaZFC.Automation.ObjectHorn.Rule) (hr : rule ∈ YesMetaZFC.Automation.ObjectProjection.rules) (env : Fin rule.arity → Fin m) (w r R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (projectionActualRuleApplicationSentence rule env w r R)) := ZFReplay.replay (projectionActualRuleApplication_kernel_certificate rule hr env w r R)

def projectionActualRuleConditionSentence {m} (rule : YesMetaZFC.Automation.ObjectHorn.Rule) (env : Fin rule.arity → Fin m) (w r : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat rule.arity w env).imp ((HornExprSyntax.graph rule.head w env r).imp ((ProjectionExprQuery.premises rule.premises w env).imp ((ProjectionTraceSyntax.condition w r)))))).close

theorem source_projectionActualRuleCondition {m} (rule : YesMetaZFC.Automation.ObjectHorn.Rule) (hr : rule ∈ YesMetaZFC.Automation.ObjectProjection.rules) (env : Fin rule.arity → Fin m) (w r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (projectionActualRuleConditionSentence rule env w r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ProjectionExprQuery.premises rule.premises w env) (Context.add (HornExprSyntax.graph rule.head w env r) (Context.add (HornExprSyntax.environmentNat rule.arity w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (HornExprSyntax.environmentNat rule.arity w env) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (HornExprSyntax.graph rule.head w env r) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (ProjectionExprQuery.premises rule.premises w env) := .hyp (Or.inl rfl)
  exact ProjectionRuleConstruction.condition_from_rule hZ rule hr w r env h0 h1 h2 h3

theorem projectionActualRuleCondition_kernel_certificate {m} (rule : YesMetaZFC.Automation.ObjectHorn.Rule) (hr : rule ∈ YesMetaZFC.Automation.ObjectProjection.rules) (env : Fin rule.arity → Fin m) (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (projectionActualRuleConditionSentence rule env w r)) := TheoryTransport.sentence (source_projectionActualRuleCondition rule hr env w r)

theorem native_projectionActualRuleCondition {m} (rule : YesMetaZFC.Automation.ObjectHorn.Rule) (hr : rule ∈ YesMetaZFC.Automation.ObjectProjection.rules) (env : Fin rule.arity → Fin m) (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (projectionActualRuleConditionSentence rule env w r)) := ZFReplay.replay (projectionActualRuleCondition_kernel_certificate rule hr env w r)

def projectionTagZeroRuleSentence {m} (env : Fin 0 → Fin m) (w : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 0 w env).imp ((ProjectionExprQuery.query YesMetaZFC.Automation.ObjectProjection.tagZero.head w env)))).close

theorem source_projectionTagZeroRule {m} (env : Fin 0 → Fin m) (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (projectionTagZeroRuleSentence env w) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.environmentNat 0 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 0 w env) := .hyp (Or.inl rfl)
  exact ProjectionRuleConstruction.query_from_rule hZ YesMetaZFC.Automation.ObjectProjection.tagZero (by simp [YesMetaZFC.Automation.ObjectProjection.rules]) w env h0 h1 HornRuleSyntax.truth_proved

theorem projectionTagZeroRule_kernel_certificate {m} (env : Fin 0 → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (projectionTagZeroRuleSentence env w)) := TheoryTransport.sentence (source_projectionTagZeroRule env w)

theorem native_projectionTagZeroRule {m} (env : Fin 0 → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (projectionTagZeroRuleSentence env w)) := ZFReplay.replay (projectionTagZeroRule_kernel_certificate env w)

def projectionTagPositiveRuleSentence {m} (env : Fin 2 → Fin m) (w : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 2 w env).imp ((ProjectionExprQuery.query YesMetaZFC.Automation.ObjectProjection.tagPositive.head w env)))).close

theorem source_projectionTagPositiveRule {m} (env : Fin 2 → Fin m) (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (projectionTagPositiveRuleSentence env w) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.environmentNat 2 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 2 w env) := .hyp (Or.inl rfl)
  exact ProjectionRuleConstruction.query_from_rule hZ YesMetaZFC.Automation.ObjectProjection.tagPositive (by simp [YesMetaZFC.Automation.ObjectProjection.rules]) w env h0 h1 HornRuleSyntax.truth_proved

theorem projectionTagPositiveRule_kernel_certificate {m} (env : Fin 2 → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (projectionTagPositiveRuleSentence env w)) := TheoryTransport.sentence (source_projectionTagPositiveRule env w)

theorem native_projectionTagPositiveRule {m} (env : Fin 2 → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (projectionTagPositiveRuleSentence env w)) := ZFReplay.replay (projectionTagPositiveRule_kernel_certificate env w)

def projectionGetZeroRuleSentence {m} (env : Fin 1 → Fin m) (w : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 1 w env).imp ((ProjectionExprQuery.query YesMetaZFC.Automation.ObjectProjection.getZero.head w env)))).close

theorem source_projectionGetZeroRule {m} (env : Fin 1 → Fin m) (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (projectionGetZeroRuleSentence env w) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.environmentNat 1 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 1 w env) := .hyp (Or.inl rfl)
  exact ProjectionRuleConstruction.query_from_rule hZ YesMetaZFC.Automation.ObjectProjection.getZero (by simp [YesMetaZFC.Automation.ObjectProjection.rules]) w env h0 h1 HornRuleSyntax.truth_proved

theorem projectionGetZeroRule_kernel_certificate {m} (env : Fin 1 → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (projectionGetZeroRuleSentence env w)) := TheoryTransport.sentence (source_projectionGetZeroRule env w)

theorem native_projectionGetZeroRule {m} (env : Fin 1 → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (projectionGetZeroRuleSentence env w)) := ZFReplay.replay (projectionGetZeroRule_kernel_certificate env w)

def projectionGetHeadRuleSentence {m} (env : Fin 3 → Fin m) (w : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 3 w env).imp ((ProjectionExprQuery.query YesMetaZFC.Automation.ObjectProjection.getHead.head w env)))).close

theorem source_projectionGetHeadRule {m} (env : Fin 3 → Fin m) (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (projectionGetHeadRuleSentence env w) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.environmentNat 3 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 3 w env) := .hyp (Or.inl rfl)
  exact ProjectionRuleConstruction.query_from_rule hZ YesMetaZFC.Automation.ObjectProjection.getHead (by simp [YesMetaZFC.Automation.ObjectProjection.rules]) w env h0 h1 HornRuleSyntax.truth_proved

theorem projectionGetHeadRule_kernel_certificate {m} (env : Fin 3 → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (projectionGetHeadRuleSentence env w)) := TheoryTransport.sentence (source_projectionGetHeadRule env w)

theorem native_projectionGetHeadRule {m} (env : Fin 3 → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (projectionGetHeadRuleSentence env w)) := ZFReplay.replay (projectionGetHeadRule_kernel_certificate env w)

def projectionGetTailRuleSentence {m} (env : Fin 5 → Fin m) (w : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 5 w env).imp ((ProjectionExprQuery.query (YesMetaZFC.Automation.ObjectProjection.getTail.premises[0]) w env).imp ((ProjectionExprQuery.query YesMetaZFC.Automation.ObjectProjection.getTail.head w env))))).close

theorem source_projectionGetTailRule {m} (env : Fin 5 → Fin m) (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (projectionGetTailRuleSentence env w) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ProjectionExprQuery.query (YesMetaZFC.Automation.ObjectProjection.getTail.premises[0]) w env) (Context.add (HornExprSyntax.environmentNat 5 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 5 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (ProjectionExprQuery.query (YesMetaZFC.Automation.ObjectProjection.getTail.premises[0]) w env) := .hyp (Or.inl rfl)
  exact ProjectionRuleConstruction.query_from_rule hZ YesMetaZFC.Automation.ObjectProjection.getTail (by simp [YesMetaZFC.Automation.ObjectProjection.rules]) w env h0 h1 (Derives.conjI h2 HornRuleSyntax.truth_proved)

theorem projectionGetTailRule_kernel_certificate {m} (env : Fin 5 → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (projectionGetTailRuleSentence env w)) := TheoryTransport.sentence (source_projectionGetTailRule env w)

theorem native_projectionGetTailRule {m} (env : Fin 5 → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (projectionGetTailRuleSentence env w)) := ZFReplay.replay (projectionGetTailRule_kernel_certificate env w)

def projectionFieldZeroRuleSentence {m} (env : Fin 1 → Fin m) (w : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 1 w env).imp ((ProjectionExprQuery.query YesMetaZFC.Automation.ObjectProjection.fieldZero.head w env)))).close

theorem source_projectionFieldZeroRule {m} (env : Fin 1 → Fin m) (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (projectionFieldZeroRuleSentence env w) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.environmentNat 1 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 1 w env) := .hyp (Or.inl rfl)
  exact ProjectionRuleConstruction.query_from_rule hZ YesMetaZFC.Automation.ObjectProjection.fieldZero (by simp [YesMetaZFC.Automation.ObjectProjection.rules]) w env h0 h1 HornRuleSyntax.truth_proved

theorem projectionFieldZeroRule_kernel_certificate {m} (env : Fin 1 → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (projectionFieldZeroRuleSentence env w)) := TheoryTransport.sentence (source_projectionFieldZeroRule env w)

theorem native_projectionFieldZeroRule {m} (env : Fin 1 → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (projectionFieldZeroRuleSentence env w)) := ZFReplay.replay (projectionFieldZeroRule_kernel_certificate env w)

def projectionFieldPositiveRuleSentence {m} (env : Fin 4 → Fin m) (w : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 4 w env).imp ((ProjectionExprQuery.query (YesMetaZFC.Automation.ObjectProjection.fieldPositive.premises[0]) w env).imp ((ProjectionExprQuery.query YesMetaZFC.Automation.ObjectProjection.fieldPositive.head w env))))).close

theorem source_projectionFieldPositiveRule {m} (env : Fin 4 → Fin m) (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (projectionFieldPositiveRuleSentence env w) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ProjectionExprQuery.query (YesMetaZFC.Automation.ObjectProjection.fieldPositive.premises[0]) w env) (Context.add (HornExprSyntax.environmentNat 4 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 4 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (ProjectionExprQuery.query (YesMetaZFC.Automation.ObjectProjection.fieldPositive.premises[0]) w env) := .hyp (Or.inl rfl)
  exact ProjectionRuleConstruction.query_from_rule hZ YesMetaZFC.Automation.ObjectProjection.fieldPositive (by simp [YesMetaZFC.Automation.ObjectProjection.rules]) w env h0 h1 (Derives.conjI h2 HornRuleSyntax.truth_proved)

theorem projectionFieldPositiveRule_kernel_certificate {m} (env : Fin 4 → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (projectionFieldPositiveRuleSentence env w)) := TheoryTransport.sentence (source_projectionFieldPositiveRule env w)

theorem native_projectionFieldPositiveRule {m} (env : Fin 4 → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (projectionFieldPositiveRuleSentence env w)) := ZFReplay.replay (projectionFieldPositiveRule_kernel_certificate env w)

end PPAC.Migration.Internal.ObjectProjectionTrace
