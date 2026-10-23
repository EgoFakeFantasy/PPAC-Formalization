import PPAC.Migration.Internal.PureSyntaxConsRule

/-! 纯检查轨迹合并及nil／cons局部构造的原核证书；完整列表归纳仍待完成。 -/
namespace PPAC.Migration.Internal.ObjectPureSyntaxListSteps
open Source SourceAlgebra SourceLogic OmegaSyntax
open YesMetaZFC.Automation.ObjectHorn (Rule)

def binaryUnionExistsSentence {m} (R S : Fin m) : Source.Sentence := ((BinaryUnionSyntax.exists_join R S)).close

theorem source_binaryUnionExists {m} (R S : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binaryUnionExistsSentence R S) := by
  apply close_derives
  let Δ : Context m := Source.SetLanguage.ZF.at m
  have hZ : ZFContext.Evidence Δ := by
    exact ZFContext.source_ZF m
  exact BinaryUnionSyntax.exists_joined hZ R S

theorem binaryUnionExists_kernel_certificate {m} (R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binaryUnionExistsSentence R S)) := TheoryTransport.sentence (source_binaryUnionExists R S)

theorem native_binaryUnionExists {m} (R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binaryUnionExistsSentence R S)) := ZFReplay.replay (binaryUnionExists_kernel_certificate R S)

def pureTraceInsertionConditionSentence {m} (w R r : Fin m) : Source.Sentence := ((RestrictionSyntax.subset R w).imp ((Formula.mem r w).imp ((PureSyntaxTrace.closed w R).imp ((HornStepSyntax.step PureSyntaxRules.rules w r R).imp ((PureSyntaxTrace.condition w r)))))).close

theorem source_pureTraceInsertionCondition {m} (w R r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (pureTraceInsertionConditionSentence w R r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornStepSyntax.step PureSyntaxRules.rules w r R) (Context.add (PureSyntaxTrace.closed w R) (Context.add (Formula.mem r w) (Context.add (RestrictionSyntax.subset R w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (RestrictionSyntax.subset R w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (Formula.mem r w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (PureSyntaxTrace.closed w R) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (HornStepSyntax.step PureSyntaxRules.rules w r R) := .hyp (Or.inl rfl)
  exact PureSyntaxTraceExtension.condition hZ w R r h0 h1 h2 h3

theorem pureTraceInsertionCondition_kernel_certificate {m} (w R r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (pureTraceInsertionConditionSentence w R r)) := TheoryTransport.sentence (source_pureTraceInsertionCondition w R r)

theorem native_pureTraceInsertionCondition {m} (w R r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (pureTraceInsertionConditionSentence w R r)) := ZFReplay.replay (pureTraceInsertionCondition_kernel_certificate w R r)

def pureTracePairConditionSentence {m} (w r s : Fin m) : Source.Sentence := ((PureSyntaxTrace.condition w r).imp ((PureSyntaxTrace.condition w s).imp ((PureSyntaxTraceMerge.pairCondition w r s)))).close

theorem source_pureTracePairCondition {m} (w r s : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (pureTracePairConditionSentence w r s) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PureSyntaxTrace.condition w s) (Context.add (PureSyntaxTrace.condition w r) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (PureSyntaxTrace.condition w r) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PureSyntaxTrace.condition w s) := .hyp (Or.inl rfl)
  exact PureSyntaxTraceMerge.two_conditions hZ w r s h0 h1

theorem pureTracePairCondition_kernel_certificate {m} (w r s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (pureTracePairConditionSentence w r s)) := TheoryTransport.sentence (source_pureTracePairCondition w r s)

theorem native_pureTracePairCondition {m} (w r s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (pureTracePairConditionSentence w r s)) := ZFReplay.replay (pureTracePairCondition_kernel_certificate w r s)

def pureNilExpressionIffSentence {m} (w n e0 e1 : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 2 w (Fin.cases e0 (fun _ => e1) : Fin 2 → Fin m)).imp (((HornExprSyntax.graph (YesMetaZFC.Automation.ObjectHorn.Expr.list []) w (Fin.cases e0 (fun _ => e1) : Fin 2 → Fin m) n).iff (StructuralListSyntax.nilCode w n))))).close

theorem source_pureNilExpressionIff {m} (w n e0 e1 : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (pureNilExpressionIffSentence w n e0 e1) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.environmentNat 2 w (Fin.cases e0 (fun _ => e1) : Fin 2 → Fin m)) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 2 w (Fin.cases e0 (fun _ => e1) : Fin 2 → Fin m)) := .hyp (Or.inl rfl)
  exact PureSyntaxNilRule.nil_iff hZ w n (Fin.cases e0 (fun _ => e1) : Fin 2 → Fin m) h0 h1

theorem pureNilExpressionIff_kernel_certificate {m} (w n e0 e1 : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (pureNilExpressionIffSentence w n e0 e1)) := TheoryTransport.sentence (source_pureNilExpressionIff w n e0 e1)

theorem native_pureNilExpressionIff {m} (w n e0 e1 : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (pureNilExpressionIffSentence w n e0 e1)) := ZFReplay.replay (pureNilExpressionIff_kernel_certificate w n e0 e1)

def pureNilApplicationSoundSentence {m} (w b f k n r R : Fin m) : Source.Sentence := ((omega w).imp ((PureSyntaxTrace.argumentRow w b f k n r).imp ((HornApplicationSyntax.application YesMetaZFC.Automation.ObjectTermSyntax.nilRule w r R).imp ((SyntaxMixedImageCodeSyntax.termList w k b f n))))).close

theorem source_pureNilApplicationSound {m} (w b f k n r R : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (pureNilApplicationSoundSentence w b f k n r R) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornApplicationSyntax.application YesMetaZFC.Automation.ObjectTermSyntax.nilRule w r R) (Context.add (PureSyntaxTrace.argumentRow w b f k n r) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (PureSyntaxTrace.argumentRow w b f k n r) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (HornApplicationSyntax.application YesMetaZFC.Automation.ObjectTermSyntax.nilRule w r R) := .hyp (Or.inl rfl)
  exact PureSyntaxNilRule.application_sound hZ w b f k n r R h0 h1 h2

theorem pureNilApplicationSound_kernel_certificate {m} (w b f k n r R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (pureNilApplicationSoundSentence w b f k n r R)) := TheoryTransport.sentence (source_pureNilApplicationSound w b f k n r R)

theorem native_pureNilApplicationSound {m} (w b f k n r R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (pureNilApplicationSoundSentence w b f k n r R)) := ZFReplay.replay (pureNilApplicationSound_kernel_certificate w b f k n r R)

def pureNilApplicationCompleteSentence {m} (w b f k n r R : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 2 w (Fin.cases b (fun _ => f) : Fin 2 → Fin m)).imp ((empty k).imp ((StructuralListSyntax.nilCode w n).imp ((PureSyntaxTrace.argumentRow w b f k n r).imp ((HornApplicationSyntax.application YesMetaZFC.Automation.ObjectTermSyntax.nilRule w r R))))))).close

theorem source_pureNilApplicationComplete {m} (w b f k n r R : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (pureNilApplicationCompleteSentence w b f k n r R) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PureSyntaxTrace.argumentRow w b f k n r) (Context.add (StructuralListSyntax.nilCode w n) (Context.add (empty k) (Context.add (HornExprSyntax.environmentNat 2 w (Fin.cases b (fun _ => f) : Fin 2 → Fin m)) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 2 w (Fin.cases b (fun _ => f) : Fin 2 → Fin m)) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (empty k) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (StructuralListSyntax.nilCode w n) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (PureSyntaxTrace.argumentRow w b f k n r) := .hyp (Or.inl rfl)
  let env : Fin 2 → Fin m := (Fin.cases b (fun _ => f) : Fin 2 → Fin m)
  change Derives Δ (HornExprSyntax.environmentNat 2 w env) at h1
  exact @PureSyntaxNilRule.application_complete m Δ hZ w k n r R env h0 h1 h2 h3 h4

theorem pureNilApplicationComplete_kernel_certificate {m} (w b f k n r R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (pureNilApplicationCompleteSentence w b f k n r R)) := TheoryTransport.sentence (source_pureNilApplicationComplete w b f k n r R)

theorem native_pureNilApplicationComplete {m} (w b f k n r R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (pureNilApplicationCompleteSentence w b f k n r R)) := ZFReplay.replay (pureNilApplicationComplete_kernel_certificate w b f k n r R)

def pureNilCheckedSentence {m} (w b f k n : Fin m) : Source.Sentence := ((omega w).imp ((empty k).imp ((SyntaxTermSyntax.contexts w b f).imp ((StructuralListSyntax.nilCode w n).imp ((PureSyntaxTrace.arguments w b f k n)))))).close

theorem source_pureNilChecked {m} (w b f k n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (pureNilCheckedSentence w b f k n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralListSyntax.nilCode w n) (Context.add (SyntaxTermSyntax.contexts w b f) (Context.add (empty k) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (empty k) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxTermSyntax.contexts w b f) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (StructuralListSyntax.nilCode w n) := .hyp (Or.inl rfl)
  exact PureSyntaxNilComplete.checked_nil hZ w b f k n h0 h1 h2 h3

theorem pureNilChecked_kernel_certificate {m} (w b f k n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (pureNilCheckedSentence w b f k n)) := TheoryTransport.sentence (source_pureNilChecked w b f k n)

theorem native_pureNilChecked {m} (w b f k n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (pureNilCheckedSentence w b f k n)) := ZFReplay.replay (pureNilChecked_kernel_certificate w b f k n)

def pureTypedNilCheckedSentence {m} (w b f k n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMixedImageCodeSyntax.termList w k b f n).imp ((StructuralListSyntax.nilCode w n).imp ((PureSyntaxTrace.arguments w b f k n))))).close

theorem source_pureTypedNilChecked {m} (w b f k n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (pureTypedNilCheckedSentence w b f k n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralListSyntax.nilCode w n) (Context.add (SyntaxMixedImageCodeSyntax.termList w k b f n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxMixedImageCodeSyntax.termList w k b f n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (StructuralListSyntax.nilCode w n) := .hyp (Or.inl rfl)
  exact PureSyntaxNilComplete.typed_nil_checked hZ w b f k n h0 h1 h2

theorem pureTypedNilChecked_kernel_certificate {m} (w b f k n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (pureTypedNilCheckedSentence w b f k n)) := TheoryTransport.sentence (source_pureTypedNilChecked w b f k n)

theorem native_pureTypedNilChecked {m} (w b f k n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (pureTypedNilCheckedSentence w b f k n)) := ZFReplay.replay (pureTypedNilChecked_kernel_certificate w b f k n)

def pureConsApplicationCompleteSentence {m} (w k n r R p q b f ell h t : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 5 w (Fin.cases b (Fin.cases f (Fin.cases ell (Fin.cases h (Fin.cases t Fin.elim0)))) : Fin 5 → Fin m)).imp ((successor k ell).imp ((StructuralListSyntax.consCode w h t n).imp ((PureSyntaxTrace.argumentRow w b f k n r).imp ((PureSyntaxTrace.termRow w b f h p).imp ((PureSyntaxTrace.argumentRow w b f ell t q).imp ((Formula.mem p R).imp ((Formula.mem q R).imp ((HornApplicationSyntax.application YesMetaZFC.Automation.ObjectTermSyntax.consRule w r R))))))))))).close

theorem source_pureConsApplicationComplete {m} (w k n r R p q b f ell h t : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (pureConsApplicationCompleteSentence w k n r R p q b f ell h t) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem q R) (Context.add (Formula.mem p R) (Context.add (PureSyntaxTrace.argumentRow w b f ell t q) (Context.add (PureSyntaxTrace.termRow w b f h p) (Context.add (PureSyntaxTrace.argumentRow w b f k n r) (Context.add (StructuralListSyntax.consCode w h t n) (Context.add (successor k ell) (Context.add (HornExprSyntax.environmentNat 5 w (Fin.cases b (Fin.cases f (Fin.cases ell (Fin.cases h (Fin.cases t Fin.elim0)))) : Fin 5 → Fin m)) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 5 w (Fin.cases b (Fin.cases f (Fin.cases ell (Fin.cases h (Fin.cases t Fin.elim0)))) : Fin 5 → Fin m)) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  have h2 : Derives Δ (successor k ell) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h3 : Derives Δ (StructuralListSyntax.consCode w h t n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h4 : Derives Δ (PureSyntaxTrace.argumentRow w b f k n r) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h5 : Derives Δ (PureSyntaxTrace.termRow w b f h p) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h6 : Derives Δ (PureSyntaxTrace.argumentRow w b f ell t q) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h7 : Derives Δ (Formula.mem p R) := .hyp (Or.inr (Or.inl rfl))
  have h8 : Derives Δ (Formula.mem q R) := .hyp (Or.inl rfl)
  let env : Fin 5 → Fin m := (Fin.cases b (Fin.cases f (Fin.cases ell (Fin.cases h (Fin.cases t Fin.elim0)))) : Fin 5 → Fin m)
  change Derives Δ (HornExprSyntax.environmentNat 5 w env) at h1
  exact @PureSyntaxConsRule.application_complete m Δ hZ w k n r R p q env h0 h1 h2 h3 h4 h5 h6 h7 h8

theorem pureConsApplicationComplete_kernel_certificate {m} (w k n r R p q b f ell h t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (pureConsApplicationCompleteSentence w k n r R p q b f ell h t)) := TheoryTransport.sentence (source_pureConsApplicationComplete w k n r R p q b f ell h t)

theorem native_pureConsApplicationComplete {m} (w k n r R p q b f ell h t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (pureConsApplicationCompleteSentence w k n r R p q b f ell h t)) := ZFReplay.replay (pureConsApplicationComplete_kernel_certificate w k n r R p q b f ell h t)

def pureConsConditionCompleteSentence {m} (w k n r p q b f ell h t : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 5 w (Fin.cases b (Fin.cases f (Fin.cases ell (Fin.cases h (Fin.cases t Fin.elim0)))) : Fin 5 → Fin m)).imp ((successor k ell).imp ((StructuralListSyntax.consCode w h t n).imp ((PureSyntaxTrace.argumentRow w b f k n r).imp ((PureSyntaxTrace.termRow w b f h p).imp ((PureSyntaxTrace.argumentRow w b f ell t q).imp ((PureSyntaxTrace.condition w p).imp ((PureSyntaxTrace.condition w q).imp ((PureSyntaxTrace.condition w r))))))))))).close

theorem source_pureConsConditionComplete {m} (w k n r p q b f ell h t : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (pureConsConditionCompleteSentence w k n r p q b f ell h t) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PureSyntaxTrace.condition w q) (Context.add (PureSyntaxTrace.condition w p) (Context.add (PureSyntaxTrace.argumentRow w b f ell t q) (Context.add (PureSyntaxTrace.termRow w b f h p) (Context.add (PureSyntaxTrace.argumentRow w b f k n r) (Context.add (StructuralListSyntax.consCode w h t n) (Context.add (successor k ell) (Context.add (HornExprSyntax.environmentNat 5 w (Fin.cases b (Fin.cases f (Fin.cases ell (Fin.cases h (Fin.cases t Fin.elim0)))) : Fin 5 → Fin m)) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 5 w (Fin.cases b (Fin.cases f (Fin.cases ell (Fin.cases h (Fin.cases t Fin.elim0)))) : Fin 5 → Fin m)) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  have h2 : Derives Δ (successor k ell) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h3 : Derives Δ (StructuralListSyntax.consCode w h t n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h4 : Derives Δ (PureSyntaxTrace.argumentRow w b f k n r) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h5 : Derives Δ (PureSyntaxTrace.termRow w b f h p) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h6 : Derives Δ (PureSyntaxTrace.argumentRow w b f ell t q) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h7 : Derives Δ (PureSyntaxTrace.condition w p) := .hyp (Or.inr (Or.inl rfl))
  have h8 : Derives Δ (PureSyntaxTrace.condition w q) := .hyp (Or.inl rfl)
  let env : Fin 5 → Fin m := (Fin.cases b (Fin.cases f (Fin.cases ell (Fin.cases h (Fin.cases t Fin.elim0)))) : Fin 5 → Fin m)
  change Derives Δ (HornExprSyntax.environmentNat 5 w env) at h1
  exact @PureSyntaxConsRule.condition_complete m Δ hZ w k n r p q env h0 h1 h2 h3 h4 h5 h6 h7 h8

theorem pureConsConditionComplete_kernel_certificate {m} (w k n r p q b f ell h t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (pureConsConditionCompleteSentence w k n r p q b f ell h t)) := TheoryTransport.sentence (source_pureConsConditionComplete w k n r p q b f ell h t)

theorem native_pureConsConditionComplete {m} (w k n r p q b f ell h t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (pureConsConditionCompleteSentence w k n r p q b f ell h t)) := ZFReplay.replay (pureConsConditionComplete_kernel_certificate w k n r p q b f ell h t)

end PPAC.Migration.Internal.ObjectPureSyntaxListSteps
