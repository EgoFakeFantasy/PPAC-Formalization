import PPAC.Migration.Internal.FreeReplaceOutcome

/-! 原模式3自由替换的全内部轨迹、实际行码、精确成功域及无输出的原核证书。 -/
namespace PPAC.Migration.Internal.ObjectFreeReplace
open Source SourceAlgebra SourceLogic OmegaSyntax

def originalVariableExprCodeIffSentence {m} {n} (bound : Bool) (e : YesMetaZFC.Automation.ObjectHorn.Expr n) (env : Fin n → Fin m) (w idx y : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat n w env).imp ((HornExprSyntax.graph e w env idx).imp (((HornExprSyntax.graph (HornVariableExpr.expression bound e) w env y).iff (SyntaxVariableSyntax.code bound w idx y)))))).close

theorem source_originalVariableExprCodeIff {m} {n} (bound : Bool) (e : YesMetaZFC.Automation.ObjectHorn.Expr n) (env : Fin n → Fin m) (w idx y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalVariableExprCodeIffSentence bound e env w idx y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.graph e w env idx) (Context.add (HornExprSyntax.environmentNat n w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat n w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (HornExprSyntax.graph e w env idx) := .hyp (Or.inl rfl)
  exact HornVariableValue.graph_iff_code hZ bound e w idx y env h0 h1 h2

theorem originalVariableExprCodeIff_kernel_certificate {m} {n} (bound : Bool) (e : YesMetaZFC.Automation.ObjectHorn.Expr n) (env : Fin n → Fin m) (w idx y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalVariableExprCodeIffSentence bound e env w idx y)) := TheoryTransport.sentence (source_originalVariableExprCodeIff bound e env w idx y)

theorem native_originalVariableExprCodeIff {m} {n} (bound : Bool) (e : YesMetaZFC.Automation.ObjectHorn.Expr n) (env : Fin n → Fin m) (w idx y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalVariableExprCodeIffSentence bound e env w idx y)) := ZFReplay.replay (originalVariableExprCodeIff_kernel_certificate bound e env w idx y)

def originalVariableCodeNaturalSentence {m} (bound : Bool) (w idx y : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxVariableSyntax.code bound w idx y).imp ((Formula.mem y w)))).close

theorem source_originalVariableCodeNatural {m} (bound : Bool) (w idx y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalVariableCodeNaturalSentence bound w idx y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxVariableSyntax.code bound w idx y) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxVariableSyntax.code bound w idx y) := .hyp (Or.inl rfl)
  exact HornVariableValue.code_natural hZ bound w idx y h0 h1

theorem originalVariableCodeNatural_kernel_certificate {m} (bound : Bool) (w idx y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalVariableCodeNaturalSentence bound w idx y)) := TheoryTransport.sentence (source_originalVariableCodeNatural bound w idx y)

theorem native_originalVariableCodeNatural {m} (bound : Bool) (w idx y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalVariableCodeNaturalSentence bound w idx y)) := ZFReplay.replay (originalVariableCodeNatural_kernel_certificate bound w idx y)

def originalFreeReplaceLookupPremiseSoundSentence {m} (env : Fin 4 → Fin m) (w R : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 4 w env).imp ((HornLookupSoundSyntax.closed w R).imp ((HornRuleSyntax.premise OriginalLookupExpr.premiseExpr w R env).imp ((LookupTableExecutionSyntax.executed w (env 1) (env 2) (env 3))))))).close

theorem source_originalFreeReplaceLookupPremiseSound {m} (env : Fin 4 → Fin m) (w R : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalFreeReplaceLookupPremiseSoundSentence env w R) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornRuleSyntax.premise OriginalLookupExpr.premiseExpr w R env) (Context.add (HornLookupSoundSyntax.closed w R) (Context.add (HornExprSyntax.environmentNat 4 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 4 w env) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (HornLookupSoundSyntax.closed w R) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (HornRuleSyntax.premise OriginalLookupExpr.premiseExpr w R env) := .hyp (Or.inl rfl)
  exact OriginalFreeReplaceSound.premise_execution hZ w R env h0 h1 h2 h3

theorem originalFreeReplaceLookupPremiseSound_kernel_certificate {m} (env : Fin 4 → Fin m) (w R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalFreeReplaceLookupPremiseSoundSentence env w R)) := TheoryTransport.sentence (source_originalFreeReplaceLookupPremiseSound env w R)

theorem native_originalFreeReplaceLookupPremiseSound {m} (env : Fin 4 → Fin m) (w R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalFreeReplaceLookupPremiseSoundSentence env w R)) := ZFReplay.replay (originalFreeReplaceLookupPremiseSound_kernel_certificate env w R)

def originalFreeReplaceMatrixSoundSentence {m} (env : Fin 4 → Fin m) (xs : Fin 5 → Fin m) (w r R idx : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 4 w env).imp ((SyntaxNodeSyntax.constructor 5 1 w xs r).imp ((SyntaxVariableSyntax.code false w idx (xs 3)).imp ((HornLookupSoundSyntax.closed w R).imp ((HornRuleSyntax.matrix YesMetaZFC.Automation.ObjectSyntaxTransform.freeReplace w r R env).imp ((LookupTableExecutionSyntax.executed w (xs 2) idx (xs 4))))))))).close

theorem source_originalFreeReplaceMatrixSound {m} (env : Fin 4 → Fin m) (xs : Fin 5 → Fin m) (w r R idx : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalFreeReplaceMatrixSoundSentence env xs w r R idx) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornRuleSyntax.matrix YesMetaZFC.Automation.ObjectSyntaxTransform.freeReplace w r R env) (Context.add (HornLookupSoundSyntax.closed w R) (Context.add (SyntaxVariableSyntax.code false w idx (xs 3)) (Context.add (SyntaxNodeSyntax.constructor 5 1 w xs r) (Context.add (HornExprSyntax.environmentNat 4 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 4 w env) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (SyntaxNodeSyntax.constructor 5 1 w xs r) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (SyntaxVariableSyntax.code false w idx (xs 3)) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (HornLookupSoundSyntax.closed w R) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (HornRuleSyntax.matrix YesMetaZFC.Automation.ObjectSyntaxTransform.freeReplace w r R env) := .hyp (Or.inl rfl)
  exact OriginalFreeReplaceSound.matrix_execution hZ w r R idx env xs h0 h1 h2 h3 h4 h5

theorem originalFreeReplaceMatrixSound_kernel_certificate {m} (env : Fin 4 → Fin m) (xs : Fin 5 → Fin m) (w r R idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalFreeReplaceMatrixSoundSentence env xs w r R idx)) := TheoryTransport.sentence (source_originalFreeReplaceMatrixSound env xs w r R idx)

theorem native_originalFreeReplaceMatrixSound {m} (env : Fin 4 → Fin m) (xs : Fin 5 → Fin m) (w r R idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalFreeReplaceMatrixSoundSentence env xs w r R idx)) := ZFReplay.replay (originalFreeReplaceMatrixSound_kernel_certificate env xs w r R idx)

def originalFreeReplaceApplicationSoundSentence {m} (xs : Fin 5 → Fin m) (w r R idx : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNodeSyntax.constructor 5 1 w xs r).imp ((SyntaxVariableSyntax.code false w idx (xs 3)).imp ((HornLookupSoundSyntax.closed w R).imp ((HornApplicationSyntax.application YesMetaZFC.Automation.ObjectSyntaxTransform.freeReplace w r R).imp ((LookupTableExecutionSyntax.executed w (xs 2) idx (xs 4)))))))).close

theorem source_originalFreeReplaceApplicationSound {m} (xs : Fin 5 → Fin m) (w r R idx : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalFreeReplaceApplicationSoundSentence xs w r R idx) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornApplicationSyntax.application YesMetaZFC.Automation.ObjectSyntaxTransform.freeReplace w r R) (Context.add (HornLookupSoundSyntax.closed w R) (Context.add (SyntaxVariableSyntax.code false w idx (xs 3)) (Context.add (SyntaxNodeSyntax.constructor 5 1 w xs r) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxNodeSyntax.constructor 5 1 w xs r) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (SyntaxVariableSyntax.code false w idx (xs 3)) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (HornLookupSoundSyntax.closed w R) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (HornApplicationSyntax.application YesMetaZFC.Automation.ObjectSyntaxTransform.freeReplace w r R) := .hyp (Or.inl rfl)
  exact OriginalFreeReplaceSound.application_execution hZ w r R idx xs h0 h1 h2 h3 h4

theorem originalFreeReplaceApplicationSound_kernel_certificate {m} (xs : Fin 5 → Fin m) (w r R idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalFreeReplaceApplicationSoundSentence xs w r R idx)) := TheoryTransport.sentence (source_originalFreeReplaceApplicationSound xs w r R idx)

theorem native_originalFreeReplaceApplicationSound {m} (xs : Fin 5 → Fin m) (w r R idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalFreeReplaceApplicationSoundSentence xs w r R idx)) := ZFReplay.replay (originalFreeReplaceApplicationSound_kernel_certificate xs w r R idx)

def originalFreeReplaceTraceExecutionIffSentence {m} (xs : Fin 5 → Fin m) (w r idx : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNodeSyntax.constructor 5 1 w xs r).imp ((SyntaxNumeralSyntax.numeral 3 (xs 0)).imp ((SyntaxVariableSyntax.code false w idx (xs 3)).imp (((HornLookupConditionSyntax.condition w r).iff (LookupTableExecutionSyntax.executed w (xs 2) idx (xs 4)))))))).close

theorem source_originalFreeReplaceTraceExecutionIff {m} (xs : Fin 5 → Fin m) (w r idx : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalFreeReplaceTraceExecutionIffSentence xs w r idx) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxVariableSyntax.code false w idx (xs 3)) (Context.add (SyntaxNumeralSyntax.numeral 3 (xs 0)) (Context.add (SyntaxNodeSyntax.constructor 5 1 w xs r) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNodeSyntax.constructor 5 1 w xs r) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral 3 (xs 0)) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxVariableSyntax.code false w idx (xs 3)) := .hyp (Or.inl rfl)
  exact OriginalFreeReplace.trace_iff_execution hZ w r idx xs h0 h1 h2 h3

theorem originalFreeReplaceTraceExecutionIff_kernel_certificate {m} (xs : Fin 5 → Fin m) (w r idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalFreeReplaceTraceExecutionIffSentence xs w r idx)) := TheoryTransport.sentence (source_originalFreeReplaceTraceExecutionIff xs w r idx)

theorem native_originalFreeReplaceTraceExecutionIff {m} (xs : Fin 5 → Fin m) (w r idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalFreeReplaceTraceExecutionIffSentence xs w r idx)) := ZFReplay.replay (originalFreeReplaceTraceExecutionIff_kernel_certificate xs w r idx)

def originalFreeReplacePowerTraceExecutionIffSentence {m} (xs : Fin 5 → Fin m) (w r idx : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNodeSyntax.constructor 5 1 w xs r).imp ((SyntaxNumeralSyntax.numeral 3 (xs 0)).imp ((SyntaxVariableSyntax.code false w idx (xs 3)).imp (((HornLookupPowerCondition.condition w r).iff (LookupTableExecutionSyntax.executed w (xs 2) idx (xs 4)))))))).close

theorem source_originalFreeReplacePowerTraceExecutionIff {m} (xs : Fin 5 → Fin m) (w r idx : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalFreeReplacePowerTraceExecutionIffSentence xs w r idx) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxVariableSyntax.code false w idx (xs 3)) (Context.add (SyntaxNumeralSyntax.numeral 3 (xs 0)) (Context.add (SyntaxNodeSyntax.constructor 5 1 w xs r) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNodeSyntax.constructor 5 1 w xs r) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral 3 (xs 0)) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxVariableSyntax.code false w idx (xs 3)) := .hyp (Or.inl rfl)
  exact OriginalFreeReplace.power_trace_iff_execution hZ w r idx xs h0 h1 h2 h3

theorem originalFreeReplacePowerTraceExecutionIff_kernel_certificate {m} (xs : Fin 5 → Fin m) (w r idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalFreeReplacePowerTraceExecutionIffSentence xs w r idx)) := TheoryTransport.sentence (source_originalFreeReplacePowerTraceExecutionIff xs w r idx)

theorem native_originalFreeReplacePowerTraceExecutionIff {m} (xs : Fin 5 → Fin m) (w r idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalFreeReplacePowerTraceExecutionIffSentence xs w r idx)) := ZFReplay.replay (originalFreeReplacePowerTraceExecutionIff_kernel_certificate xs w r idx)

def originalFreeReplaceTraceCandidateRejectionIffSentence {m} (xs : Fin 5 → Fin m) (w r idx : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNodeSyntax.constructor 5 1 w xs r).imp ((SyntaxNumeralSyntax.numeral 3 (xs 0)).imp ((SyntaxVariableSyntax.code false w idx (xs 3)).imp (((HornLookupConditionSyntax.condition w r).neg.iff (LookupTableExecutionSyntax.executed w (xs 2) idx (xs 4)).neg)))))).close

theorem source_originalFreeReplaceTraceCandidateRejectionIff {m} (xs : Fin 5 → Fin m) (w r idx : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalFreeReplaceTraceCandidateRejectionIffSentence xs w r idx) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxVariableSyntax.code false w idx (xs 3)) (Context.add (SyntaxNumeralSyntax.numeral 3 (xs 0)) (Context.add (SyntaxNodeSyntax.constructor 5 1 w xs r) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNodeSyntax.constructor 5 1 w xs r) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral 3 (xs 0)) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxVariableSyntax.code false w idx (xs 3)) := .hyp (Or.inl rfl)
  exact OriginalFreeReplace.rejected_iff hZ w r idx xs h0 h1 h2 h3

theorem originalFreeReplaceTraceCandidateRejectionIff_kernel_certificate {m} (xs : Fin 5 → Fin m) (w r idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalFreeReplaceTraceCandidateRejectionIffSentence xs w r idx)) := TheoryTransport.sentence (source_originalFreeReplaceTraceCandidateRejectionIff xs w r idx)

theorem native_originalFreeReplaceTraceCandidateRejectionIff {m} (xs : Fin 5 → Fin m) (w r idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalFreeReplaceTraceCandidateRejectionIffSentence xs w r idx)) := ZFReplay.replay (originalFreeReplaceTraceCandidateRejectionIff_kernel_certificate xs w r idx)

def actualOriginalFreeReplaceRootSentence {m} (w d p x y : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem d w).imp ((Formula.mem p w).imp ((Formula.mem x w).imp ((Formula.mem y w).imp ((FreeReplaceResultSyntax.existsRoot w d p x y))))))).close

theorem source_actualOriginalFreeReplaceRoot {m} (w d p x y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (actualOriginalFreeReplaceRootSentence w d p x y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem y w) (Context.add (Formula.mem x w) (Context.add (Formula.mem p w) (Context.add (Formula.mem d w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (Formula.mem d w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (Formula.mem p w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (Formula.mem x w) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (Formula.mem y w) := .hyp (Or.inl rfl)
  exact FreeReplaceResultRows.exists_root hZ w d p x y h0 h1 h2 h3 h4

theorem actualOriginalFreeReplaceRoot_kernel_certificate {m} (w d p x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (actualOriginalFreeReplaceRootSentence w d p x y)) := TheoryTransport.sentence (source_actualOriginalFreeReplaceRoot w d p x y)

theorem native_actualOriginalFreeReplaceRoot {m} (w d p x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (actualOriginalFreeReplaceRootSentence w d p x y)) := ZFReplay.replay (actualOriginalFreeReplaceRoot_kernel_certificate w d p x y)

def allInternalFreeReplaceReturnedIffSentence {m} (w d p x idx y : Fin m) : Source.Sentence := ((omega w).imp (((FreeReplaceResultSyntax.returned w d p x idx y).iff ((FreeReplaceResultSyntax.guard w d x idx).conj (LookupTableExecutionSyntax.executed w p idx y))))).close

theorem source_allInternalFreeReplaceReturnedIff {m} (w d p x idx y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (allInternalFreeReplaceReturnedIffSentence w d p x idx y) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact FreeReplaceResult.returned_iff hZ w d p x idx y h0

theorem allInternalFreeReplaceReturnedIff_kernel_certificate {m} (w d p x idx y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (allInternalFreeReplaceReturnedIffSentence w d p x idx y)) := TheoryTransport.sentence (source_allInternalFreeReplaceReturnedIff w d p x idx y)

theorem native_allInternalFreeReplaceReturnedIff {m} (w d p x idx y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (allInternalFreeReplaceReturnedIffSentence w d p x idx y)) := ZFReplay.replay (allInternalFreeReplaceReturnedIff_kernel_certificate w d p x idx y)

def allInternalFreeReplaceCheckedIffSentence {m} (w d p x idx y : Fin m) : Source.Sentence := ((omega w).imp (((FreeReplaceResultSyntax.returned w d p x idx y).iff ((FreeReplaceResultSyntax.guard w d x idx).conj (StrictLookupSyntax.checked w p idx y))))).close

theorem source_allInternalFreeReplaceCheckedIff {m} (w d p x idx y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (allInternalFreeReplaceCheckedIffSentence w d p x idx y) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact FreeReplaceResult.checked_iff hZ w d p x idx y h0

theorem allInternalFreeReplaceCheckedIff_kernel_certificate {m} (w d p x idx y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (allInternalFreeReplaceCheckedIffSentence w d p x idx y)) := TheoryTransport.sentence (source_allInternalFreeReplaceCheckedIff w d p x idx y)

theorem native_allInternalFreeReplaceCheckedIff {m} (w d p x idx y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (allInternalFreeReplaceCheckedIffSentence w d p x idx y)) := ZFReplay.replay (allInternalFreeReplaceCheckedIff_kernel_certificate w d p x idx y)

def validFreeReplaceReturnedExecutionIffSentence {m} (w d p x idx y : Fin m) : Source.Sentence := ((omega w).imp ((FreeReplaceResultSyntax.guard w d x idx).imp (((FreeReplaceResultSyntax.returned w d p x idx y).iff (LookupTableExecutionSyntax.executed w p idx y))))).close

theorem source_validFreeReplaceReturnedExecutionIff {m} (w d p x idx y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (validFreeReplaceReturnedExecutionIffSentence w d p x idx y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (FreeReplaceResultSyntax.guard w d x idx) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (FreeReplaceResultSyntax.guard w d x idx) := .hyp (Or.inl rfl)
  exact FreeReplaceResult.under_guard_iff hZ w d p x idx y h0 h1

theorem validFreeReplaceReturnedExecutionIff_kernel_certificate {m} (w d p x idx y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (validFreeReplaceReturnedExecutionIffSentence w d p x idx y)) := TheoryTransport.sentence (source_validFreeReplaceReturnedExecutionIff w d p x idx y)

theorem native_validFreeReplaceReturnedExecutionIff {m} (w d p x idx y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (validFreeReplaceReturnedExecutionIffSentence w d p x idx y)) := ZFReplay.replay (validFreeReplaceReturnedExecutionIff_kernel_certificate w d p x idx y)

def naturalFreeReplaceReturnedStrictIffSentence {m} (w d p x idx y : Fin m) : Source.Sentence := ((omega w).imp ((FreeReplaceResultSyntax.guard w d x idx).imp ((Formula.mem p w).imp (((FreeReplaceResultSyntax.returned w d p x idx y).iff (StrictLookupSyntax.returned w p idx y)))))).close

theorem source_naturalFreeReplaceReturnedStrictIff {m} (w d p x idx y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (naturalFreeReplaceReturnedStrictIffSentence w d p x idx y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem p w) (Context.add (FreeReplaceResultSyntax.guard w d x idx) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (FreeReplaceResultSyntax.guard w d x idx) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (Formula.mem p w) := .hyp (Or.inl rfl)
  exact FreeReplaceResult.strict_iff hZ w d p x idx y h0 h1 h2

theorem naturalFreeReplaceReturnedStrictIff_kernel_certificate {m} (w d p x idx y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (naturalFreeReplaceReturnedStrictIffSentence w d p x idx y)) := TheoryTransport.sentence (source_naturalFreeReplaceReturnedStrictIff w d p x idx y)

theorem native_naturalFreeReplaceReturnedStrictIff {m} (w d p x idx y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (naturalFreeReplaceReturnedStrictIffSentence w d p x idx y)) := ZFReplay.replay (naturalFreeReplaceReturnedStrictIff_kernel_certificate w d p x idx y)

def allInternalFreeReplaceCandidateRejectionIffSentence {m} (w d p x idx y : Fin m) : Source.Sentence := ((omega w).imp (((FreeReplaceResultSyntax.returned w d p x idx y).neg.iff ((FreeReplaceResultSyntax.guard w d x idx).conj (LookupTableExecutionSyntax.executed w p idx y)).neg))).close

theorem source_allInternalFreeReplaceCandidateRejectionIff {m} (w d p x idx y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (allInternalFreeReplaceCandidateRejectionIffSentence w d p x idx y) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact FreeReplaceResult.rejected_iff hZ w d p x idx y h0

theorem allInternalFreeReplaceCandidateRejectionIff_kernel_certificate {m} (w d p x idx y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (allInternalFreeReplaceCandidateRejectionIffSentence w d p x idx y)) := TheoryTransport.sentence (source_allInternalFreeReplaceCandidateRejectionIff w d p x idx y)

theorem native_allInternalFreeReplaceCandidateRejectionIff {m} (w d p x idx y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (allInternalFreeReplaceCandidateRejectionIffSentence w d p x idx y)) := ZFReplay.replay (allInternalFreeReplaceCandidateRejectionIff_kernel_certificate w d p x idx y)

def allInternalFreeReplaceHasOutputGuardedIffSentence {m} (w d p x idx : Fin m) : Source.Sentence := ((omega w).imp (((FreeReplaceResultSyntax.hasOutput w d p x idx).iff ((FreeReplaceResultSyntax.guard w d x idx).conj (LookupTableOutcomeSyntax.hasOutput w p idx))))).close

theorem source_allInternalFreeReplaceHasOutputGuardedIff {m} (w d p x idx : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (allInternalFreeReplaceHasOutputGuardedIffSentence w d p x idx) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact FreeReplaceOutcome.has_output_iff_guarded hZ w d p x idx h0

theorem allInternalFreeReplaceHasOutputGuardedIff_kernel_certificate {m} (w d p x idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (allInternalFreeReplaceHasOutputGuardedIffSentence w d p x idx)) := TheoryTransport.sentence (source_allInternalFreeReplaceHasOutputGuardedIff w d p x idx)

theorem native_allInternalFreeReplaceHasOutputGuardedIff {m} (w d p x idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (allInternalFreeReplaceHasOutputGuardedIffSentence w d p x idx)) := ZFReplay.replay (allInternalFreeReplaceHasOutputGuardedIff_kernel_certificate w d p x idx)

def allInternalFreeReplaceNoOutputGuardedIffSentence {m} (w d p x idx : Fin m) : Source.Sentence := ((omega w).imp (((FreeReplaceResultSyntax.noOutput w d p x idx).iff ((FreeReplaceResultSyntax.guard w d x idx).conj (LookupTableOutcomeSyntax.hasOutput w p idx)).neg))).close

theorem source_allInternalFreeReplaceNoOutputGuardedIff {m} (w d p x idx : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (allInternalFreeReplaceNoOutputGuardedIffSentence w d p x idx) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact FreeReplaceOutcome.no_output_iff_guarded hZ w d p x idx h0

theorem allInternalFreeReplaceNoOutputGuardedIff_kernel_certificate {m} (w d p x idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (allInternalFreeReplaceNoOutputGuardedIffSentence w d p x idx)) := TheoryTransport.sentence (source_allInternalFreeReplaceNoOutputGuardedIff w d p x idx)

theorem native_allInternalFreeReplaceNoOutputGuardedIff {m} (w d p x idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (allInternalFreeReplaceNoOutputGuardedIffSentence w d p x idx)) := ZFReplay.replay (allInternalFreeReplaceNoOutputGuardedIff_kernel_certificate w d p x idx)

def validFreeReplaceHasOutputIffSentence {m} (w d p x idx : Fin m) : Source.Sentence := ((omega w).imp ((FreeReplaceResultSyntax.guard w d x idx).imp (((FreeReplaceResultSyntax.hasOutput w d p x idx).iff (LookupTableOutcomeSyntax.hasOutput w p idx))))).close

theorem source_validFreeReplaceHasOutputIff {m} (w d p x idx : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (validFreeReplaceHasOutputIffSentence w d p x idx) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (FreeReplaceResultSyntax.guard w d x idx) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (FreeReplaceResultSyntax.guard w d x idx) := .hyp (Or.inl rfl)
  exact FreeReplaceOutcome.has_output_iff hZ w d p x idx h0 h1

theorem validFreeReplaceHasOutputIff_kernel_certificate {m} (w d p x idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (validFreeReplaceHasOutputIffSentence w d p x idx)) := TheoryTransport.sentence (source_validFreeReplaceHasOutputIff w d p x idx)

theorem native_validFreeReplaceHasOutputIff {m} (w d p x idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (validFreeReplaceHasOutputIffSentence w d p x idx)) := ZFReplay.replay (validFreeReplaceHasOutputIff_kernel_certificate w d p x idx)

def validFreeReplaceNoOutputIffSentence {m} (w d p x idx : Fin m) : Source.Sentence := ((omega w).imp ((FreeReplaceResultSyntax.guard w d x idx).imp (((FreeReplaceResultSyntax.noOutput w d p x idx).iff (LookupTableOutcomeSyntax.noOutput w p idx))))).close

theorem source_validFreeReplaceNoOutputIff {m} (w d p x idx : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (validFreeReplaceNoOutputIffSentence w d p x idx) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (FreeReplaceResultSyntax.guard w d x idx) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (FreeReplaceResultSyntax.guard w d x idx) := .hyp (Or.inl rfl)
  exact FreeReplaceOutcome.no_output_iff hZ w d p x idx h0 h1

theorem validFreeReplaceNoOutputIff_kernel_certificate {m} (w d p x idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (validFreeReplaceNoOutputIffSentence w d p x idx)) := TheoryTransport.sentence (source_validFreeReplaceNoOutputIff w d p x idx)

theorem native_validFreeReplaceNoOutputIff {m} (w d p x idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (validFreeReplaceNoOutputIffSentence w d p x idx)) := ZFReplay.replay (validFreeReplaceNoOutputIff_kernel_certificate w d p x idx)

def naturalFreeReplaceStrictNoOutputIffSentence {m} (w d p x idx : Fin m) : Source.Sentence := ((omega w).imp ((FreeReplaceResultSyntax.guard w d x idx).imp ((Formula.mem p w).imp (((FreeReplaceResultSyntax.noOutput w d p x idx).iff (StrictLookupSyntax.rejected w p idx)))))).close

theorem source_naturalFreeReplaceStrictNoOutputIff {m} (w d p x idx : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (naturalFreeReplaceStrictNoOutputIffSentence w d p x idx) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem p w) (Context.add (FreeReplaceResultSyntax.guard w d x idx) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (FreeReplaceResultSyntax.guard w d x idx) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (Formula.mem p w) := .hyp (Or.inl rfl)
  exact FreeReplaceOutcome.strict_no_output_iff hZ w d p x idx h0 h1 h2

theorem naturalFreeReplaceStrictNoOutputIff_kernel_certificate {m} (w d p x idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (naturalFreeReplaceStrictNoOutputIffSentence w d p x idx)) := TheoryTransport.sentence (source_naturalFreeReplaceStrictNoOutputIff w d p x idx)

theorem native_naturalFreeReplaceStrictNoOutputIff {m} (w d p x idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (naturalFreeReplaceStrictNoOutputIffSentence w d p x idx)) := ZFReplay.replay (naturalFreeReplaceStrictNoOutputIff_kernel_certificate w d p x idx)

def invalidFreeReplaceGuardNoOutputSentence {m} (w d p x idx : Fin m) : Source.Sentence := ((omega w).imp (((FreeReplaceResultSyntax.guard w d x idx).neg).imp ((FreeReplaceResultSyntax.noOutput w d p x idx)))).close

theorem source_invalidFreeReplaceGuardNoOutput {m} (w d p x idx : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (invalidFreeReplaceGuardNoOutputSentence w d p x idx) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add ((FreeReplaceResultSyntax.guard w d x idx).neg) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ ((FreeReplaceResultSyntax.guard w d x idx).neg) := .hyp (Or.inl rfl)
  exact FreeReplaceOutcome.invalid_guard_no_output hZ w d p x idx h0 h1

theorem invalidFreeReplaceGuardNoOutput_kernel_certificate {m} (w d p x idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (invalidFreeReplaceGuardNoOutputSentence w d p x idx)) := TheoryTransport.sentence (source_invalidFreeReplaceGuardNoOutput w d p x idx)

theorem native_invalidFreeReplaceGuardNoOutput {m} (w d p x idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (invalidFreeReplaceGuardNoOutputSentence w d p x idx)) := ZFReplay.replay (invalidFreeReplaceGuardNoOutput_kernel_certificate w d p x idx)

def nonNaturalFreeReplaceOutputRejectedSentence {m} (w d p x idx y : Fin m) : Source.Sentence := ((omega w).imp (((Formula.mem y w).neg).imp (((FreeReplaceResultSyntax.returned w d p x idx y).neg)))).close

theorem source_nonNaturalFreeReplaceOutputRejected {m} (w d p x idx y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (nonNaturalFreeReplaceOutputRejectedSentence w d p x idx y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add ((Formula.mem y w).neg) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ ((Formula.mem y w).neg) := .hyp (Or.inl rfl)
  exact FreeReplaceOutcome.invalid_output_rejected hZ w d p x idx y h0 h1

theorem nonNaturalFreeReplaceOutputRejected_kernel_certificate {m} (w d p x idx y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (nonNaturalFreeReplaceOutputRejectedSentence w d p x idx y)) := TheoryTransport.sentence (source_nonNaturalFreeReplaceOutputRejected w d p x idx y)

theorem native_nonNaturalFreeReplaceOutputRejected {m} (w d p x idx y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (nonNaturalFreeReplaceOutputRejectedSentence w d p x idx y)) := ZFReplay.replay (nonNaturalFreeReplaceOutputRejected_kernel_certificate w d p x idx y)

def allInternalFreeReplaceOutputUniqueSentence {m} (w d p x idx y z : Fin m) : Source.Sentence := ((omega w).imp ((FreeReplaceResultSyntax.returned w d p x idx y).imp ((FreeReplaceResultSyntax.returned w d p x idx z).imp ((Formula.equal y z))))).close

theorem source_allInternalFreeReplaceOutputUnique {m} (w d p x idx y z : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (allInternalFreeReplaceOutputUniqueSentence w d p x idx y z) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (FreeReplaceResultSyntax.returned w d p x idx z) (Context.add (FreeReplaceResultSyntax.returned w d p x idx y) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (FreeReplaceResultSyntax.returned w d p x idx y) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (FreeReplaceResultSyntax.returned w d p x idx z) := .hyp (Or.inl rfl)
  exact FreeReplaceOutcome.unique hZ w d p x idx y z h0 h1 h2

theorem allInternalFreeReplaceOutputUnique_kernel_certificate {m} (w d p x idx y z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (allInternalFreeReplaceOutputUniqueSentence w d p x idx y z)) := TheoryTransport.sentence (source_allInternalFreeReplaceOutputUnique w d p x idx y z)

theorem native_allInternalFreeReplaceOutputUnique {m} (w d p x idx y z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (allInternalFreeReplaceOutputUniqueSentence w d p x idx y z)) := ZFReplay.replay (allInternalFreeReplaceOutputUnique_kernel_certificate w d p x idx y z)

end PPAC.Migration.Internal.ObjectFreeReplace
