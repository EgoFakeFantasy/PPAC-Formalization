import PPAC.Migration.Internal.PureSyntaxTermCorrectness

/-! 完整纯签名规则表上项查询的实际闭轨迹、全内部双条件及原核证书。 -/
namespace PPAC.Migration.Internal.ObjectPureSyntaxTermChecker
open Source SourceAlgebra SourceLogic OmegaSyntax
open YesMetaZFC.Automation.ObjectHorn (Rule)

def purePremiseFreeTraceExistsSentence {m} (rule : Rule) (_hmem : rule ∈ PureSyntaxRules.rules) (_hn : rule.premises = []) (w r : Fin m) : Source.Sentence := ((Formula.mem r w).imp ((HornApplicationSyntax.application rule w r w).imp ((PureSyntaxTrace.condition w r)))).close

theorem source_purePremiseFreeTraceExists {m} (rule : Rule) (hmem : rule ∈ PureSyntaxRules.rules) (hn : rule.premises = []) (w r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (purePremiseFreeTraceExistsSentence rule hmem hn w r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornApplicationSyntax.application rule w r w) (Context.add (Formula.mem r w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (Formula.mem r w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (HornApplicationSyntax.application rule w r w) := .hyp (Or.inl rfl)
  exact PureSyntaxTraceRules.premise_free_condition hZ rule hmem hn w r h0 h1

theorem purePremiseFreeTraceExists_kernel_certificate {m} (rule : Rule) (hmem : rule ∈ PureSyntaxRules.rules) (hn : rule.premises = []) (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (purePremiseFreeTraceExistsSentence rule hmem hn w r)) := TheoryTransport.sentence (source_purePremiseFreeTraceExists rule hmem hn w r)

theorem native_purePremiseFreeTraceExists {m} (rule : Rule) (hmem : rule ∈ PureSyntaxRules.rules) (hn : rule.premises = []) (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (purePremiseFreeTraceExistsSentence rule hmem hn w r)) := ZFReplay.replay (purePremiseFreeTraceExists_kernel_certificate rule hmem hn w r)

def pureVariableExpressionIffSentence {m} (bound : Bool) (w n e0 e1 e2 : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 3 w (SyntaxAtomSyntax.three e0 e1 e2)).imp (((HornExprSyntax.graph (PureSyntaxVariableExpr.variableExpr bound (2 : Fin 3)) w (SyntaxAtomSyntax.three e0 e1 e2) n).iff (SyntaxVariableSyntax.code bound w e2 n))))).close

theorem source_pureVariableExpressionIff {m} (bound : Bool) (w n e0 e1 e2 : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (pureVariableExpressionIffSentence bound w n e0 e1 e2) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.environmentNat 3 w (SyntaxAtomSyntax.three e0 e1 e2)) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 3 w (SyntaxAtomSyntax.three e0 e1 e2)) := .hyp (Or.inl rfl)
  exact PureSyntaxVariableExpr.variable_iff hZ bound (2 : Fin 3) w n (SyntaxAtomSyntax.three e0 e1 e2) h0 h1

theorem pureVariableExpressionIff_kernel_certificate {m} (bound : Bool) (w n e0 e1 e2 : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (pureVariableExpressionIffSentence bound w n e0 e1 e2)) := TheoryTransport.sentence (source_pureVariableExpressionIff bound w n e0 e1 e2)

theorem native_pureVariableExpressionIff {m} (bound : Bool) (w n e0 e1 e2 : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (pureVariableExpressionIffSentence bound w n e0 e1 e2)) := ZFReplay.replay (pureVariableExpressionIff_kernel_certificate bound w n e0 e1 e2)

def pureVariableApplicationSoundSentence {m} (bound : Bool) (w b f n r R : Fin m) : Source.Sentence := ((omega w).imp ((PureSyntaxTrace.termRow w b f n r).imp ((HornApplicationSyntax.application (YesMetaZFC.Automation.ObjectTermSyntax.variableRule (!bound)) w r R).imp ((SyntaxTermSyntax.term w b f n))))).close

theorem source_pureVariableApplicationSound {m} (bound : Bool) (w b f n r R : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (pureVariableApplicationSoundSentence bound w b f n r R) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornApplicationSyntax.application (YesMetaZFC.Automation.ObjectTermSyntax.variableRule (!bound)) w r R) (Context.add (PureSyntaxTrace.termRow w b f n r) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (PureSyntaxTrace.termRow w b f n r) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (HornApplicationSyntax.application (YesMetaZFC.Automation.ObjectTermSyntax.variableRule (!bound)) w r R) := .hyp (Or.inl rfl)
  exact PureSyntaxTermMatrix.application_sound hZ bound w b f n r R h0 h1 h2

theorem pureVariableApplicationSound_kernel_certificate {m} (bound : Bool) (w b f n r R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (pureVariableApplicationSoundSentence bound w b f n r R)) := TheoryTransport.sentence (source_pureVariableApplicationSound bound w b f n r R)

theorem native_pureVariableApplicationSound {m} (bound : Bool) (w b f n r R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (pureVariableApplicationSoundSentence bound w b f n r R)) := ZFReplay.replay (pureVariableApplicationSound_kernel_certificate bound w b f n r R)

def pureTermClosedTraceSoundSentence {m} (w b f n r : Fin m) : Source.Sentence := ((omega w).imp ((PureSyntaxTrace.termRow w b f n r).imp ((PureSyntaxTrace.condition w r).imp ((SyntaxTermSyntax.term w b f n))))).close

theorem source_pureTermClosedTraceSound {m} (w b f n r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (pureTermClosedTraceSoundSentence w b f n r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PureSyntaxTrace.condition w r) (Context.add (PureSyntaxTrace.termRow w b f n r) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (PureSyntaxTrace.termRow w b f n r) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (PureSyntaxTrace.condition w r) := .hyp (Or.inl rfl)
  exact PureSyntaxTermCorrectness.condition_sound hZ w b f n r h0 h1 h2

theorem pureTermClosedTraceSound_kernel_certificate {m} (w b f n r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (pureTermClosedTraceSoundSentence w b f n r)) := TheoryTransport.sentence (source_pureTermClosedTraceSound w b f n r)

theorem native_pureTermClosedTraceSound {m} (w b f n r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (pureTermClosedTraceSoundSentence w b f n r)) := ZFReplay.replay (pureTermClosedTraceSound_kernel_certificate w b f n r)

def pureTermCheckSoundSentence {m} (w b f n : Fin m) : Source.Sentence := ((omega w).imp ((PureSyntaxTrace.term w b f n).imp ((SyntaxTermSyntax.term w b f n)))).close

theorem source_pureTermCheckSound {m} (w b f n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (pureTermCheckSoundSentence w b f n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PureSyntaxTrace.term w b f n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PureSyntaxTrace.term w b f n) := .hyp (Or.inl rfl)
  exact PureSyntaxTermCorrectness.checked_sound hZ w b f n h0 h1

theorem pureTermCheckSound_kernel_certificate {m} (w b f n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (pureTermCheckSoundSentence w b f n)) := TheoryTransport.sentence (source_pureTermCheckSound w b f n)

theorem native_pureTermCheckSound {m} (w b f n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (pureTermCheckSoundSentence w b f n)) := ZFReplay.replay (pureTermCheckSound_kernel_certificate w b f n)

def pureTermCheckCompleteSentence {m} (w b f n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxTermSyntax.term w b f n).imp ((PureSyntaxTrace.term w b f n)))).close

theorem source_pureTermCheckComplete {m} (w b f n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (pureTermCheckCompleteSentence w b f n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTermSyntax.term w b f n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxTermSyntax.term w b f n) := .hyp (Or.inl rfl)
  exact PureSyntaxTermCorrectness.checked_complete hZ w b f n h0 h1

theorem pureTermCheckComplete_kernel_certificate {m} (w b f n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (pureTermCheckCompleteSentence w b f n)) := TheoryTransport.sentence (source_pureTermCheckComplete w b f n)

theorem native_pureTermCheckComplete {m} (w b f n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (pureTermCheckCompleteSentence w b f n)) := ZFReplay.replay (pureTermCheckComplete_kernel_certificate w b f n)

def pureTermCheckIffSentence {m} (w b f n : Fin m) : Source.Sentence := ((omega w).imp (((PureSyntaxTrace.term w b f n).iff (SyntaxTermSyntax.term w b f n)))).close

theorem source_pureTermCheckIff {m} (w b f n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (pureTermCheckIffSentence w b f n) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact PureSyntaxTermCorrectness.checked_iff hZ w b f n h0

theorem pureTermCheckIff_kernel_certificate {m} (w b f n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (pureTermCheckIffSentence w b f n)) := TheoryTransport.sentence (source_pureTermCheckIff w b f n)

theorem native_pureTermCheckIff {m} (w b f n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (pureTermCheckIffSentence w b f n)) := ZFReplay.replay (pureTermCheckIff_kernel_certificate w b f n)

def pureEmptyBoundTermCheckFreeSentence {m} (w z f n : Fin m) : Source.Sentence := ((omega w).imp ((empty z).imp ((PureSyntaxTrace.term w z f n).imp ((SyntaxTermSyntax.branch false w f n))))).close

theorem source_pureEmptyBoundTermCheckFree {m} (w z f n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (pureEmptyBoundTermCheckFreeSentence w z f n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PureSyntaxTrace.term w z f n) (Context.add (empty z) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (empty z) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (PureSyntaxTrace.term w z f n) := .hyp (Or.inl rfl)
  exact PureSyntaxTermCorrectness.empty_bound_free hZ w z f n h0 h1 h2

theorem pureEmptyBoundTermCheckFree_kernel_certificate {m} (w z f n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (pureEmptyBoundTermCheckFreeSentence w z f n)) := TheoryTransport.sentence (source_pureEmptyBoundTermCheckFree w z f n)

theorem native_pureEmptyBoundTermCheckFree {m} (w z f n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (pureEmptyBoundTermCheckFreeSentence w z f n)) := ZFReplay.replay (pureEmptyBoundTermCheckFree_kernel_certificate w z f n)

end PPAC.Migration.Internal.ObjectPureSyntaxTermChecker
