import PPAC.Migration.Internal.ProofTreeInduction

/-! 原ZF内部证明树结构归纳模式；对象局部闭包前提明确保留，完整Proof与最终Con未完成。 -/
namespace PPAC.Migration.Internal.ObjectProofTreeInduction
open Source SourceAlgebra SourceLogic OmegaSyntax

def proofTreePropertyStepWithMemberIHSentence {m} (test : Source.Formula 1) (P : Source.Formula 2) (w code : Fin m) : Source.Sentence := ((omega w).imp ((ProofTreeInductionSyntax.closure test P w).imp ((ProofTreeInductionSyntax.allIH test P w code).imp ((ProofTreeInductionSyntax.correct test P w code))))).close

theorem source_proofTreePropertyStepWithMemberIH {m} (test : Source.Formula 1) (P : Source.Formula 2) (w code : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (proofTreePropertyStepWithMemberIHSentence test P w code) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ProofTreeInductionSyntax.allIH test P w code) (Context.add (ProofTreeInductionSyntax.closure test P w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (ProofTreeInductionSyntax.closure test P w) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (ProofTreeInductionSyntax.allIH test P w code) := .hyp (Or.inl rfl)
  exact ProofTreeInductionStep.from_induction test P hZ w code h0 h1 h2

theorem proofTreePropertyStepWithMemberIH_kernel_certificate {m} (test : Source.Formula 1) (P : Source.Formula 2) (w code : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (proofTreePropertyStepWithMemberIHSentence test P w code)) := TheoryTransport.sentence (source_proofTreePropertyStepWithMemberIH test P w code)

theorem native_proofTreePropertyStepWithMemberIH {m} (test : Source.Formula 1) (P : Source.Formula 2) (w code : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (proofTreePropertyStepWithMemberIHSentence test P w code)) := ZFReplay.replay (proofTreePropertyStepWithMemberIH_kernel_certificate test P w code)

def proofTreePropertyProgressiveSentence {m} (test : Source.Formula 1) (P : Source.Formula 2) (w : Fin m) : Source.Sentence := ((omega w).imp ((ProofTreeInductionSyntax.closure test P w).imp ((SetInductionSyntax.progressive (ProofTreeInduction.inductionMatrix test P) (fun _ : Fin 1 => w))))).close

theorem source_proofTreePropertyProgressive {m} (test : Source.Formula 1) (P : Source.Formula 2) (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (proofTreePropertyProgressiveSentence test P w) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ProofTreeInductionSyntax.closure test P w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (ProofTreeInductionSyntax.closure test P w) := .hyp (Or.inl rfl)
  exact ProofTreeInduction.progressive test P hZ w h0 h1

theorem proofTreePropertyProgressive_kernel_certificate {m} (test : Source.Formula 1) (P : Source.Formula 2) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (proofTreePropertyProgressiveSentence test P w)) := TheoryTransport.sentence (source_proofTreePropertyProgressive test P w)

theorem native_proofTreePropertyProgressive {m} (test : Source.Formula 1) (P : Source.Formula 2) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (proofTreePropertyProgressiveSentence test P w)) := ZFReplay.replay (proofTreePropertyProgressive_kernel_certificate test P w)

def proofTreeInternalInductionSentence {m} (test : Source.Formula 1) (P : Source.Formula 2) (w : Fin m) : Source.Sentence := ((omega w).imp ((ProofTreeInductionSyntax.closure test P w).imp ((Formula.all (ProofTreeInductionSyntax.correct test P w.castSucc (Fin.last m)))))).close

theorem source_proofTreeInternalInduction {m} (test : Source.Formula 1) (P : Source.Formula 2) (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (proofTreeInternalInductionSentence test P w) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ProofTreeInductionSyntax.closure test P w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (ProofTreeInductionSyntax.closure test P w) := .hyp (Or.inl rfl)
  exact ProofTreeInduction.all_correct test P hZ w h0 h1

theorem proofTreeInternalInduction_kernel_certificate {m} (test : Source.Formula 1) (P : Source.Formula 2) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (proofTreeInternalInductionSentence test P w)) := TheoryTransport.sentence (source_proofTreeInternalInduction test P w)

theorem native_proofTreeInternalInduction {m} (test : Source.Formula 1) (P : Source.Formula 2) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (proofTreeInternalInductionSentence test P w)) := ZFReplay.replay (proofTreeInternalInduction_kernel_certificate test P w)

def proofTreePointInductionSentence {m} (test : Source.Formula 1) (P : Source.Formula 2) (w code : Fin m) : Source.Sentence := ((omega w).imp ((ProofTreeInductionSyntax.closure test P w).imp ((ProofTreeInductionSyntax.correct test P w code)))).close

theorem source_proofTreePointInduction {m} (test : Source.Formula 1) (P : Source.Formula 2) (w code : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (proofTreePointInductionSentence test P w code) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ProofTreeInductionSyntax.closure test P w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (ProofTreeInductionSyntax.closure test P w) := .hyp (Or.inl rfl)
  exact ProofTreeInduction.at_node test P hZ w code h0 h1

theorem proofTreePointInduction_kernel_certificate {m} (test : Source.Formula 1) (P : Source.Formula 2) (w code : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (proofTreePointInductionSentence test P w code)) := TheoryTransport.sentence (source_proofTreePointInduction test P w code)

theorem native_proofTreePointInduction {m} (test : Source.Formula 1) (P : Source.Formula 2) (w code : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (proofTreePointInductionSentence test P w code)) := ZFReplay.replay (proofTreePointInduction_kernel_certificate test P w code)

def proofTreeRootPropertySentence {m} (test : Source.Formula 1) (P : Source.Formula 2) (w code conclusion : Fin m) : Source.Sentence := ((omega w).imp ((ProofTreeInductionSyntax.closure test P w).imp ((ProofTreeEntrySyntax.root test w code conclusion).imp ((ProofTreeInductionSyntax.property P w code))))).close

theorem source_proofTreeRootProperty {m} (test : Source.Formula 1) (P : Source.Formula 2) (w code conclusion : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (proofTreeRootPropertySentence test P w code conclusion) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ProofTreeEntrySyntax.root test w code conclusion) (Context.add (ProofTreeInductionSyntax.closure test P w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (ProofTreeInductionSyntax.closure test P w) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (ProofTreeEntrySyntax.root test w code conclusion) := .hyp (Or.inl rfl)
  exact ProofTreeInduction.at_root test P hZ w code conclusion h0 h1 h2

theorem proofTreeRootProperty_kernel_certificate {m} (test : Source.Formula 1) (P : Source.Formula 2) (w code conclusion : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (proofTreeRootPropertySentence test P w code conclusion)) := TheoryTransport.sentence (source_proofTreeRootProperty test P w code conclusion)

theorem native_proofTreeRootProperty {m} (test : Source.Formula 1) (P : Source.Formula 2) (w code conclusion : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (proofTreeRootPropertySentence test P w code conclusion)) := ZFReplay.replay (proofTreeRootProperty_kernel_certificate test P w code conclusion)

def proofTreeRejectNodeFromPropertySentence {m} (test : Source.Formula 1) (P : Source.Formula 2) (w code : Fin m) : Source.Sentence := ((omega w).imp ((ProofTreeInductionSyntax.closure test P w).imp (((ProofTreeInductionSyntax.property P w code).neg).imp (((ProofTreeEntrySyntax.node test w code).neg))))).close

theorem source_proofTreeRejectNodeFromProperty {m} (test : Source.Formula 1) (P : Source.Formula 2) (w code : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (proofTreeRejectNodeFromPropertySentence test P w code) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add ((ProofTreeInductionSyntax.property P w code).neg) (Context.add (ProofTreeInductionSyntax.closure test P w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (ProofTreeInductionSyntax.closure test P w) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ ((ProofTreeInductionSyntax.property P w code).neg) := .hyp (Or.inl rfl)
  exact ProofTreeInduction.reject_node test P hZ w code h0 h1 h2

theorem proofTreeRejectNodeFromProperty_kernel_certificate {m} (test : Source.Formula 1) (P : Source.Formula 2) (w code : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (proofTreeRejectNodeFromPropertySentence test P w code)) := TheoryTransport.sentence (source_proofTreeRejectNodeFromProperty test P w code)

theorem native_proofTreeRejectNodeFromProperty {m} (test : Source.Formula 1) (P : Source.Formula 2) (w code : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (proofTreeRejectNodeFromPropertySentence test P w code)) := ZFReplay.replay (proofTreeRejectNodeFromProperty_kernel_certificate test P w code)

def proofTreeRejectRootFromPropertySentence {m} (test : Source.Formula 1) (P : Source.Formula 2) (w code conclusion : Fin m) : Source.Sentence := ((omega w).imp ((ProofTreeInductionSyntax.closure test P w).imp (((ProofTreeInductionSyntax.property P w code).neg).imp (((ProofTreeEntrySyntax.root test w code conclusion).neg))))).close

theorem source_proofTreeRejectRootFromProperty {m} (test : Source.Formula 1) (P : Source.Formula 2) (w code conclusion : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (proofTreeRejectRootFromPropertySentence test P w code conclusion) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add ((ProofTreeInductionSyntax.property P w code).neg) (Context.add (ProofTreeInductionSyntax.closure test P w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (ProofTreeInductionSyntax.closure test P w) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ ((ProofTreeInductionSyntax.property P w code).neg) := .hyp (Or.inl rfl)
  exact ProofTreeInduction.reject_root test P hZ w code conclusion h0 h1 h2

theorem proofTreeRejectRootFromProperty_kernel_certificate {m} (test : Source.Formula 1) (P : Source.Formula 2) (w code conclusion : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (proofTreeRejectRootFromPropertySentence test P w code conclusion)) := TheoryTransport.sentence (source_proofTreeRejectRootFromProperty test P w code conclusion)

theorem native_proofTreeRejectRootFromProperty {m} (test : Source.Formula 1) (P : Source.Formula 2) (w code conclusion : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (proofTreeRejectRootFromPropertySentence test P w code conclusion)) := ZFReplay.replay (proofTreeRejectRootFromProperty_kernel_certificate test P w code conclusion)

end PPAC.Migration.Internal.ObjectProofTreeInduction
