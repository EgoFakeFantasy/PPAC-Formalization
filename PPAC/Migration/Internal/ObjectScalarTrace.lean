import PPAC.Migration.Internal.OriginalScalarPositive
import PPAC.Migration.Internal.HornLookupPowerCondition

/-! 原规则轨迹扩展及模式0/3变量正分支的原核证书；不宣称完整数值接口。 -/
namespace PPAC.Migration.Internal.ObjectScalarTrace
open Source SourceAlgebra SourceLogic OmegaSyntax

def ruleMatrixTraceMonotoneSentence {m} (rule : YesMetaZFC.Automation.ObjectHorn.Rule) (env : Fin rule.arity → Fin m) (w r R S : Fin m) : Source.Sentence := ((RestrictionSyntax.subset R S).imp ((HornRuleSyntax.matrix rule w r R env).imp ((HornRuleSyntax.matrix rule w r S env)))).close

theorem source_ruleMatrixTraceMonotone {m} (rule : YesMetaZFC.Automation.ObjectHorn.Rule) (env : Fin rule.arity → Fin m) (w r R S : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (ruleMatrixTraceMonotoneSentence rule env w r R S) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornRuleSyntax.matrix rule w r R env) (Context.add (RestrictionSyntax.subset R S) (Source.SetLanguage.ZF.at m))
  have h0 : Derives Δ (RestrictionSyntax.subset R S) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (HornRuleSyntax.matrix rule w r R env) := .hyp (Or.inl rfl)
  exact HornTraceMonotone.matrix rule w r R S env h0 h1

theorem ruleMatrixTraceMonotone_kernel_certificate {m} (rule : YesMetaZFC.Automation.ObjectHorn.Rule) (env : Fin rule.arity → Fin m) (w r R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (ruleMatrixTraceMonotoneSentence rule env w r R S)) := TheoryTransport.sentence (source_ruleMatrixTraceMonotone rule env w r R S)

theorem native_ruleMatrixTraceMonotone {m} (rule : YesMetaZFC.Automation.ObjectHorn.Rule) (env : Fin rule.arity → Fin m) (w r R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (ruleMatrixTraceMonotoneSentence rule env w r R S)) := ZFReplay.replay (ruleMatrixTraceMonotone_kernel_certificate rule env w r R S)

def ruleApplicationTraceMonotoneSentence {m} (rule : YesMetaZFC.Automation.ObjectHorn.Rule) (w r R S : Fin m) : Source.Sentence := ((RestrictionSyntax.subset R S).imp ((HornApplicationSyntax.application rule w r R).imp ((HornApplicationSyntax.application rule w r S)))).close

theorem source_ruleApplicationTraceMonotone {m} (rule : YesMetaZFC.Automation.ObjectHorn.Rule) (w r R S : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (ruleApplicationTraceMonotoneSentence rule w r R S) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornApplicationSyntax.application rule w r R) (Context.add (RestrictionSyntax.subset R S) (Source.SetLanguage.ZF.at m))
  have h0 : Derives Δ (RestrictionSyntax.subset R S) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (HornApplicationSyntax.application rule w r R) := .hyp (Or.inl rfl)
  exact HornTraceMonotone.application rule w r R S h0 h1

theorem ruleApplicationTraceMonotone_kernel_certificate {m} (rule : YesMetaZFC.Automation.ObjectHorn.Rule) (w r R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (ruleApplicationTraceMonotoneSentence rule w r R S)) := TheoryTransport.sentence (source_ruleApplicationTraceMonotone rule w r R S)

theorem native_ruleApplicationTraceMonotone {m} (rule : YesMetaZFC.Automation.ObjectHorn.Rule) (w r R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (ruleApplicationTraceMonotoneSentence rule w r R S)) := ZFReplay.replay (ruleApplicationTraceMonotone_kernel_certificate rule w r R S)

def originalWholeTableTraceMonotoneSentence {m} (w r R S : Fin m) : Source.Sentence := ((RestrictionSyntax.subset R S).imp ((HornStepSyntax.originalStep w r R).imp ((HornStepSyntax.originalStep w r S)))).close

theorem source_originalWholeTableTraceMonotone {m} (w r R S : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalWholeTableTraceMonotoneSentence w r R S) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornStepSyntax.originalStep w r R) (Context.add (RestrictionSyntax.subset R S) (Source.SetLanguage.ZF.at m))
  have h0 : Derives Δ (RestrictionSyntax.subset R S) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (HornStepSyntax.originalStep w r R) := .hyp (Or.inl rfl)
  exact HornTraceMonotone.originalStep w r R S h0 h1

theorem originalWholeTableTraceMonotone_kernel_certificate {m} (w r R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalWholeTableTraceMonotoneSentence w r R S)) := TheoryTransport.sentence (source_originalWholeTableTraceMonotone w r R S)

theorem native_originalWholeTableTraceMonotone {m} (w r R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalWholeTableTraceMonotoneSentence w r R S)) := ZFReplay.replay (originalWholeTableTraceMonotone_kernel_certificate w r R S)

def insertedTraceIncludesSentence {m} (R r S : Fin m) : Source.Sentence := ((InsertSyntax.insert S R r).imp ((RestrictionSyntax.subset R S))).close

theorem source_insertedTraceIncludes {m} (R r S : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (insertedTraceIncludesSentence R r S) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (InsertSyntax.insert S R r) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (InsertSyntax.insert S R r) := .hyp (Or.inl rfl)
  exact HornTraceExtension.includes R r S h0

theorem insertedTraceIncludes_kernel_certificate {m} (R r S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (insertedTraceIncludesSentence R r S)) := TheoryTransport.sentence (source_insertedTraceIncludes R r S)

theorem native_insertedTraceIncludes {m} (R r S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (insertedTraceIncludesSentence R r S)) := ZFReplay.replay (insertedTraceIncludes_kernel_certificate R r S)

def insertedTraceSubsetOmegaSentence {m} (w R r S : Fin m) : Source.Sentence := ((RestrictionSyntax.subset R w).imp ((Formula.mem r w).imp ((InsertSyntax.insert S R r).imp ((RestrictionSyntax.subset S w))))).close

theorem source_insertedTraceSubsetOmega {m} (w R r S : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (insertedTraceSubsetOmegaSentence w R r S) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (InsertSyntax.insert S R r) (Context.add (Formula.mem r w) (Context.add (RestrictionSyntax.subset R w) (Source.SetLanguage.ZF.at m)))
  have h0 : Derives Δ (RestrictionSyntax.subset R w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (Formula.mem r w) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (InsertSyntax.insert S R r) := .hyp (Or.inl rfl)
  exact HornTraceExtension.subset w R r S h0 h1 h2

theorem insertedTraceSubsetOmega_kernel_certificate {m} (w R r S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (insertedTraceSubsetOmegaSentence w R r S)) := TheoryTransport.sentence (source_insertedTraceSubsetOmega w R r S)

theorem native_insertedTraceSubsetOmega {m} (w R r S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (insertedTraceSubsetOmegaSentence w R r S)) := ZFReplay.replay (insertedTraceSubsetOmega_kernel_certificate w R r S)

def insertedTraceClosedSentence {m} (w R r S : Fin m) : Source.Sentence := ((HornLookupSoundSyntax.closed w R).imp ((HornStepSyntax.originalStep w r R).imp ((InsertSyntax.insert S R r).imp ((HornLookupSoundSyntax.closed w S))))).close

theorem source_insertedTraceClosed {m} (w R r S : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (insertedTraceClosedSentence w R r S) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (InsertSyntax.insert S R r) (Context.add (HornStepSyntax.originalStep w r R) (Context.add (HornLookupSoundSyntax.closed w R) (Source.SetLanguage.ZF.at m)))
  have h0 : Derives Δ (HornLookupSoundSyntax.closed w R) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornStepSyntax.originalStep w r R) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (InsertSyntax.insert S R r) := .hyp (Or.inl rfl)
  exact HornTraceExtension.closed w R r S h0 h1 h2

theorem insertedTraceClosed_kernel_certificate {m} (w R r S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (insertedTraceClosedSentence w R r S)) := TheoryTransport.sentence (source_insertedTraceClosed w R r S)

theorem native_insertedTraceClosed {m} (w R r S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (insertedTraceClosedSentence w R r S)) := ZFReplay.replay (insertedTraceClosed_kernel_certificate w R r S)

def insertedRootActualTraceSentence {m} (w R r : Fin m) : Source.Sentence := ((RestrictionSyntax.subset R w).imp ((Formula.mem r w).imp ((HornLookupSoundSyntax.closed w R).imp ((HornStepSyntax.originalStep w r R).imp ((HornLookupConditionSyntax.condition w r)))))).close

theorem source_insertedRootActualTrace {m} (w R r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (insertedRootActualTraceSentence w R r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornStepSyntax.originalStep w r R) (Context.add (HornLookupSoundSyntax.closed w R) (Context.add (Formula.mem r w) (Context.add (RestrictionSyntax.subset R w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (RestrictionSyntax.subset R w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (Formula.mem r w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (HornLookupSoundSyntax.closed w R) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (HornStepSyntax.originalStep w r R) := .hyp (Or.inl rfl)
  exact HornTraceExtension.condition hZ w R r h0 h1 h2 h3

theorem insertedRootActualTrace_kernel_certificate {m} (w R r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (insertedRootActualTraceSentence w R r)) := TheoryTransport.sentence (source_insertedRootActualTrace w R r)

theorem native_insertedRootActualTrace {m} (w R r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (insertedRootActualTraceSentence w R r)) := ZFReplay.replay (insertedRootActualTrace_kernel_certificate w R r)

def boundModeZeroTraceSentence {m} (env : Fin 3 → Fin m) (w r : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 3 w env).imp ((HornExprSyntax.graph (YesMetaZFC.Automation.ObjectSyntaxTransform.boundIdentity 0).head w env r).imp ((HornLookupConditionSyntax.condition w r))))).close

theorem source_boundModeZeroTrace {m} (env : Fin 3 → Fin m) (w r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (boundModeZeroTraceSentence env w r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.graph (YesMetaZFC.Automation.ObjectSyntaxTransform.boundIdentity 0).head w env r) (Context.add (HornExprSyntax.environmentNat 3 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 3 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (HornExprSyntax.graph (YesMetaZFC.Automation.ObjectSyntaxTransform.boundIdentity 0).head w env r) := .hyp (Or.inl rfl)
  exact OriginalScalarPositive.bound_zero hZ w r env h0 h1 h2

theorem boundModeZeroTrace_kernel_certificate {m} (env : Fin 3 → Fin m) (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (boundModeZeroTraceSentence env w r)) := TheoryTransport.sentence (source_boundModeZeroTrace env w r)

theorem native_boundModeZeroTrace {m} (env : Fin 3 → Fin m) (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (boundModeZeroTraceSentence env w r)) := ZFReplay.replay (boundModeZeroTrace_kernel_certificate env w r)

def boundModeZeroPowerTraceSentence {m} (env : Fin 3 → Fin m) (w r : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 3 w env).imp ((HornExprSyntax.graph (YesMetaZFC.Automation.ObjectSyntaxTransform.boundIdentity 0).head w env r).imp ((HornLookupPowerCondition.condition w r))))).close

theorem source_boundModeZeroPowerTrace {m} (env : Fin 3 → Fin m) (w r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (boundModeZeroPowerTraceSentence env w r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.graph (YesMetaZFC.Automation.ObjectSyntaxTransform.boundIdentity 0).head w env r) (Context.add (HornExprSyntax.environmentNat 3 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 3 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (HornExprSyntax.graph (YesMetaZFC.Automation.ObjectSyntaxTransform.boundIdentity 0).head w env r) := .hyp (Or.inl rfl)
  exact Derives.impE (.conjR (HornLookupPowerCondition.search_condition_iff hZ w r)) (Derives.impE (.conjL (HornLookupSearchCondition.condition_iff hZ w r h0)) (OriginalScalarPositive.bound_zero hZ w r env h0 h1 h2))

theorem boundModeZeroPowerTrace_kernel_certificate {m} (env : Fin 3 → Fin m) (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (boundModeZeroPowerTraceSentence env w r)) := TheoryTransport.sentence (source_boundModeZeroPowerTrace env w r)

theorem native_boundModeZeroPowerTrace {m} (env : Fin 3 → Fin m) (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (boundModeZeroPowerTraceSentence env w r)) := ZFReplay.replay (boundModeZeroPowerTrace_kernel_certificate env w r)

def boundModeThreeTraceSentence {m} (env : Fin 3 → Fin m) (w r : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 3 w env).imp ((HornExprSyntax.graph (YesMetaZFC.Automation.ObjectSyntaxTransform.boundIdentity 3).head w env r).imp ((HornLookupConditionSyntax.condition w r))))).close

theorem source_boundModeThreeTrace {m} (env : Fin 3 → Fin m) (w r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (boundModeThreeTraceSentence env w r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.graph (YesMetaZFC.Automation.ObjectSyntaxTransform.boundIdentity 3).head w env r) (Context.add (HornExprSyntax.environmentNat 3 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 3 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (HornExprSyntax.graph (YesMetaZFC.Automation.ObjectSyntaxTransform.boundIdentity 3).head w env r) := .hyp (Or.inl rfl)
  exact OriginalScalarPositive.bound_three hZ w r env h0 h1 h2

theorem boundModeThreeTrace_kernel_certificate {m} (env : Fin 3 → Fin m) (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (boundModeThreeTraceSentence env w r)) := TheoryTransport.sentence (source_boundModeThreeTrace env w r)

theorem native_boundModeThreeTrace {m} (env : Fin 3 → Fin m) (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (boundModeThreeTraceSentence env w r)) := ZFReplay.replay (boundModeThreeTrace_kernel_certificate env w r)

def boundModeThreePowerTraceSentence {m} (env : Fin 3 → Fin m) (w r : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 3 w env).imp ((HornExprSyntax.graph (YesMetaZFC.Automation.ObjectSyntaxTransform.boundIdentity 3).head w env r).imp ((HornLookupPowerCondition.condition w r))))).close

theorem source_boundModeThreePowerTrace {m} (env : Fin 3 → Fin m) (w r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (boundModeThreePowerTraceSentence env w r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.graph (YesMetaZFC.Automation.ObjectSyntaxTransform.boundIdentity 3).head w env r) (Context.add (HornExprSyntax.environmentNat 3 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 3 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (HornExprSyntax.graph (YesMetaZFC.Automation.ObjectSyntaxTransform.boundIdentity 3).head w env r) := .hyp (Or.inl rfl)
  exact Derives.impE (.conjR (HornLookupPowerCondition.search_condition_iff hZ w r)) (Derives.impE (.conjL (HornLookupSearchCondition.condition_iff hZ w r h0)) (OriginalScalarPositive.bound_three hZ w r env h0 h1 h2))

theorem boundModeThreePowerTrace_kernel_certificate {m} (env : Fin 3 → Fin m) (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (boundModeThreePowerTraceSentence env w r)) := TheoryTransport.sentence (source_boundModeThreePowerTrace env w r)

theorem native_boundModeThreePowerTrace {m} (env : Fin 3 → Fin m) (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (boundModeThreePowerTraceSentence env w r)) := ZFReplay.replay (boundModeThreePowerTrace_kernel_certificate env w r)

def freeModeZeroTraceSentence {m} (env : Fin 3 → Fin m) (w r : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 3 w env).imp ((HornExprSyntax.graph (YesMetaZFC.Automation.ObjectSyntaxTransform.freeWeaken).head w env r).imp ((HornLookupConditionSyntax.condition w r))))).close

theorem source_freeModeZeroTrace {m} (env : Fin 3 → Fin m) (w r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (freeModeZeroTraceSentence env w r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.graph (YesMetaZFC.Automation.ObjectSyntaxTransform.freeWeaken).head w env r) (Context.add (HornExprSyntax.environmentNat 3 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 3 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (HornExprSyntax.graph (YesMetaZFC.Automation.ObjectSyntaxTransform.freeWeaken).head w env r) := .hyp (Or.inl rfl)
  exact OriginalScalarPositive.free_zero hZ w r env h0 h1 h2

theorem freeModeZeroTrace_kernel_certificate {m} (env : Fin 3 → Fin m) (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (freeModeZeroTraceSentence env w r)) := TheoryTransport.sentence (source_freeModeZeroTrace env w r)

theorem native_freeModeZeroTrace {m} (env : Fin 3 → Fin m) (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (freeModeZeroTraceSentence env w r)) := ZFReplay.replay (freeModeZeroTrace_kernel_certificate env w r)

def freeModeZeroPowerTraceSentence {m} (env : Fin 3 → Fin m) (w r : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 3 w env).imp ((HornExprSyntax.graph (YesMetaZFC.Automation.ObjectSyntaxTransform.freeWeaken).head w env r).imp ((HornLookupPowerCondition.condition w r))))).close

theorem source_freeModeZeroPowerTrace {m} (env : Fin 3 → Fin m) (w r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (freeModeZeroPowerTraceSentence env w r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.graph (YesMetaZFC.Automation.ObjectSyntaxTransform.freeWeaken).head w env r) (Context.add (HornExprSyntax.environmentNat 3 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 3 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (HornExprSyntax.graph (YesMetaZFC.Automation.ObjectSyntaxTransform.freeWeaken).head w env r) := .hyp (Or.inl rfl)
  exact Derives.impE (.conjR (HornLookupPowerCondition.search_condition_iff hZ w r)) (Derives.impE (.conjL (HornLookupSearchCondition.condition_iff hZ w r h0)) (OriginalScalarPositive.free_zero hZ w r env h0 h1 h2))

theorem freeModeZeroPowerTrace_kernel_certificate {m} (env : Fin 3 → Fin m) (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (freeModeZeroPowerTraceSentence env w r)) := TheoryTransport.sentence (source_freeModeZeroPowerTrace env w r)

theorem native_freeModeZeroPowerTrace {m} (env : Fin 3 → Fin m) (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (freeModeZeroPowerTraceSentence env w r)) := ZFReplay.replay (freeModeZeroPowerTrace_kernel_certificate env w r)

def freeModeThreeTraceSentence {m} (env : Fin 4 → Fin m) (w r : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 4 w env).imp ((HornExprSyntax.graph (YesMetaZFC.Automation.ObjectSyntaxTransform.freeReplace).head w env r).imp ((LookupTableExecutionSyntax.executed w (env 1) (env 2) (env 3)).imp ((HornLookupConditionSyntax.condition w r)))))).close

theorem source_freeModeThreeTrace {m} (env : Fin 4 → Fin m) (w r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (freeModeThreeTraceSentence env w r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (LookupTableExecutionSyntax.executed w (env 1) (env 2) (env 3)) (Context.add (HornExprSyntax.graph (YesMetaZFC.Automation.ObjectSyntaxTransform.freeReplace).head w env r) (Context.add (HornExprSyntax.environmentNat 4 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 4 w env) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (HornExprSyntax.graph (YesMetaZFC.Automation.ObjectSyntaxTransform.freeReplace).head w env r) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (LookupTableExecutionSyntax.executed w (env 1) (env 2) (env 3)) := .hyp (Or.inl rfl)
  exact OriginalScalarPositive.free_three hZ w r env h0 h1 h2 h3

theorem freeModeThreeTrace_kernel_certificate {m} (env : Fin 4 → Fin m) (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (freeModeThreeTraceSentence env w r)) := TheoryTransport.sentence (source_freeModeThreeTrace env w r)

theorem native_freeModeThreeTrace {m} (env : Fin 4 → Fin m) (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (freeModeThreeTraceSentence env w r)) := ZFReplay.replay (freeModeThreeTrace_kernel_certificate env w r)

def freeModeThreePowerTraceSentence {m} (env : Fin 4 → Fin m) (w r : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 4 w env).imp ((HornExprSyntax.graph (YesMetaZFC.Automation.ObjectSyntaxTransform.freeReplace).head w env r).imp ((LookupTableExecutionSyntax.executed w (env 1) (env 2) (env 3)).imp ((HornLookupPowerCondition.condition w r)))))).close

theorem source_freeModeThreePowerTrace {m} (env : Fin 4 → Fin m) (w r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (freeModeThreePowerTraceSentence env w r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (LookupTableExecutionSyntax.executed w (env 1) (env 2) (env 3)) (Context.add (HornExprSyntax.graph (YesMetaZFC.Automation.ObjectSyntaxTransform.freeReplace).head w env r) (Context.add (HornExprSyntax.environmentNat 4 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 4 w env) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (HornExprSyntax.graph (YesMetaZFC.Automation.ObjectSyntaxTransform.freeReplace).head w env r) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (LookupTableExecutionSyntax.executed w (env 1) (env 2) (env 3)) := .hyp (Or.inl rfl)
  exact Derives.impE (.conjR (HornLookupPowerCondition.search_condition_iff hZ w r)) (Derives.impE (.conjL (HornLookupSearchCondition.condition_iff hZ w r h0)) (OriginalScalarPositive.free_three hZ w r env h0 h1 h2 h3))

theorem freeModeThreePowerTrace_kernel_certificate {m} (env : Fin 4 → Fin m) (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (freeModeThreePowerTraceSentence env w r)) := TheoryTransport.sentence (source_freeModeThreePowerTrace env w r)

theorem native_freeModeThreePowerTrace {m} (env : Fin 4 → Fin m) (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (freeModeThreePowerTraceSentence env w r)) := ZFReplay.replay (freeModeThreePowerTrace_kernel_certificate env w r)

end PPAC.Migration.Internal.ObjectScalarTrace
