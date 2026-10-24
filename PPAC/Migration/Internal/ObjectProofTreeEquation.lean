import PPAC.Migration.Internal.ProofTreeEquationCanonical

/-! 原六分支递归方程唯一性及实际Node模板的无方程前提证书；专用Bool／Proof与最终Con未完成。 -/
namespace PPAC.Migration.Internal.ObjectProofTreeEquation
open Source SourceAlgebra SourceLogic OmegaSyntax

def proofTreeEquationImpliesLocalClosureSentence {m} (test : Source.Formula 1) (P : Source.Formula 2) (w : Fin m) : Source.Sentence := ((ProofTreeEquationSyntax.equation test P w).imp ((ProofTreeInductionSyntax.closure test P w))).close

theorem source_proofTreeEquationImpliesLocalClosure {m} (test : Source.Formula 1) (P : Source.Formula 2) (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (proofTreeEquationImpliesLocalClosureSentence test P w) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (ProofTreeEquationSyntax.equation test P w) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (ProofTreeEquationSyntax.equation test P w) := .hyp (Or.inl rfl)
  exact ProofTreeEquationSyntax.closure_from_equation test P w h0

theorem proofTreeEquationImpliesLocalClosure_kernel_certificate {m} (test : Source.Formula 1) (P : Source.Formula 2) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (proofTreeEquationImpliesLocalClosureSentence test P w)) := TheoryTransport.sentence (source_proofTreeEquationImpliesLocalClosure test P w)

theorem native_proofTreeEquationImpliesLocalClosure {m} (test : Source.Formula 1) (P : Source.Formula 2) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (proofTreeEquationImpliesLocalClosureSentence test P w)) := ZFReplay.replay (proofTreeEquationImpliesLocalClosure_kernel_certificate test P w)

def proofTreeEquationReverseProgressiveSentence {m} (test : Source.Formula 1) (P : Source.Formula 2) (w : Fin m) : Source.Sentence := ((omega w).imp ((ProofTreeEquationSyntax.equation test P w).imp ((SetInductionSyntax.progressive (ProofTreeEquationUnique.inductionMatrix test P) (fun _ : Fin 1 => w))))).close

theorem source_proofTreeEquationReverseProgressive {m} (test : Source.Formula 1) (P : Source.Formula 2) (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (proofTreeEquationReverseProgressiveSentence test P w) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ProofTreeEquationSyntax.equation test P w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (ProofTreeEquationSyntax.equation test P w) := .hyp (Or.inl rfl)
  exact ProofTreeEquationUnique.progressive test P hZ w h0 h1

theorem proofTreeEquationReverseProgressive_kernel_certificate {m} (test : Source.Formula 1) (P : Source.Formula 2) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (proofTreeEquationReverseProgressiveSentence test P w)) := TheoryTransport.sentence (source_proofTreeEquationReverseProgressive test P w)

theorem native_proofTreeEquationReverseProgressive {m} (test : Source.Formula 1) (P : Source.Formula 2) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (proofTreeEquationReverseProgressiveSentence test P w)) := ZFReplay.replay (proofTreeEquationReverseProgressive_kernel_certificate test P w)

def proofTreeEquationAllCodeUniqueSentence {m} (test : Source.Formula 1) (P : Source.Formula 2) (w : Fin m) : Source.Sentence := ((omega w).imp ((ProofTreeEquationSyntax.equation test P w).imp ((Formula.all ((ProofTreeEntrySyntax.node test w.castSucc (Fin.last m)).iff (ProofTreeInductionSyntax.property P w.castSucc (Fin.last m))))))).close

theorem source_proofTreeEquationAllCodeUnique {m} (test : Source.Formula 1) (P : Source.Formula 2) (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (proofTreeEquationAllCodeUniqueSentence test P w) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ProofTreeEquationSyntax.equation test P w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (ProofTreeEquationSyntax.equation test P w) := .hyp (Or.inl rfl)
  exact ProofTreeEquationUnique.all_iff test P hZ w h0 h1

theorem proofTreeEquationAllCodeUnique_kernel_certificate {m} (test : Source.Formula 1) (P : Source.Formula 2) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (proofTreeEquationAllCodeUniqueSentence test P w)) := TheoryTransport.sentence (source_proofTreeEquationAllCodeUnique test P w)

theorem native_proofTreeEquationAllCodeUnique {m} (test : Source.Formula 1) (P : Source.Formula 2) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (proofTreeEquationAllCodeUniqueSentence test P w)) := ZFReplay.replay (proofTreeEquationAllCodeUnique_kernel_certificate test P w)

def proofTreeEquationPointUniqueSentence {m} (test : Source.Formula 1) (P : Source.Formula 2) (w code : Fin m) : Source.Sentence := ((omega w).imp ((ProofTreeEquationSyntax.equation test P w).imp (((ProofTreeEntrySyntax.node test w code).iff (ProofTreeInductionSyntax.property P w code))))).close

theorem source_proofTreeEquationPointUnique {m} (test : Source.Formula 1) (P : Source.Formula 2) (w code : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (proofTreeEquationPointUniqueSentence test P w code) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ProofTreeEquationSyntax.equation test P w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (ProofTreeEquationSyntax.equation test P w) := .hyp (Or.inl rfl)
  exact ProofTreeEquationUnique.point_iff test P hZ w code h0 h1

theorem proofTreeEquationPointUnique_kernel_certificate {m} (test : Source.Formula 1) (P : Source.Formula 2) (w code : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (proofTreeEquationPointUniqueSentence test P w code)) := TheoryTransport.sentence (source_proofTreeEquationPointUnique test P w code)

theorem native_proofTreeEquationPointUnique {m} (test : Source.Formula 1) (P : Source.Formula 2) (w code : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (proofTreeEquationPointUniqueSentence test P w code)) := ZFReplay.replay (proofTreeEquationPointUnique_kernel_certificate test P w code)

def proofTreeEquationRootUniqueSentence {m} (test : Source.Formula 1) (P : Source.Formula 2) (w code conclusion : Fin m) : Source.Sentence := ((omega w).imp ((ProofTreeEquationSyntax.equation test P w).imp (((ProofTreeEntrySyntax.root test w code conclusion).iff ((ProofTreeInductionSyntax.property P w code).conj (ProofTreeRootSyntax.closedPayload w code conclusion)))))).close

theorem source_proofTreeEquationRootUnique {m} (test : Source.Formula 1) (P : Source.Formula 2) (w code conclusion : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (proofTreeEquationRootUniqueSentence test P w code conclusion) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ProofTreeEquationSyntax.equation test P w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (ProofTreeEquationSyntax.equation test P w) := .hyp (Or.inl rfl)
  exact ProofTreeEquationUnique.root_iff test P hZ w code conclusion h0 h1

theorem proofTreeEquationRootUnique_kernel_certificate {m} (test : Source.Formula 1) (P : Source.Formula 2) (w code conclusion : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (proofTreeEquationRootUniqueSentence test P w code conclusion)) := TheoryTransport.sentence (source_proofTreeEquationRootUnique test P w code conclusion)

theorem native_proofTreeEquationRootUnique {m} (test : Source.Formula 1) (P : Source.Formula 2) (w code conclusion : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (proofTreeEquationRootUniqueSentence test P w code conclusion)) := ZFReplay.replay (proofTreeEquationRootUnique_kernel_certificate test P w code conclusion)

def proofTreeEquationTwoSolutionsSentence {m} (test : Source.Formula 1) (P Q : Source.Formula 2) (w code : Fin m) : Source.Sentence := ((omega w).imp ((ProofTreeEquationSyntax.equation test P w).imp ((ProofTreeEquationSyntax.equation test Q w).imp (((ProofTreeInductionSyntax.property P w code).iff (ProofTreeInductionSyntax.property Q w code)))))).close

theorem source_proofTreeEquationTwoSolutions {m} (test : Source.Formula 1) (P Q : Source.Formula 2) (w code : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (proofTreeEquationTwoSolutionsSentence test P Q w code) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ProofTreeEquationSyntax.equation test Q w) (Context.add (ProofTreeEquationSyntax.equation test P w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (ProofTreeEquationSyntax.equation test P w) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (ProofTreeEquationSyntax.equation test Q w) := .hyp (Or.inl rfl)
  exact ProofTreeEquationUnique.two_solutions test P Q hZ w code h0 h1 h2

theorem proofTreeEquationTwoSolutions_kernel_certificate {m} (test : Source.Formula 1) (P Q : Source.Formula 2) (w code : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (proofTreeEquationTwoSolutionsSentence test P Q w code)) := TheoryTransport.sentence (source_proofTreeEquationTwoSolutions test P Q w code)

theorem native_proofTreeEquationTwoSolutions {m} (test : Source.Formula 1) (P Q : Source.Formula 2) (w code : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (proofTreeEquationTwoSolutionsSentence test P Q w code)) := ZFReplay.replay (proofTreeEquationTwoSolutions_kernel_certificate test P Q w code)

def proofTreeEquationNodeNaturalSentence {m} (test : Source.Formula 1) (w code : Fin m) : Source.Sentence := ((omega w).imp ((ProofTreeEntrySyntax.node test w code).imp ((Formula.mem code w)))).close

theorem source_proofTreeEquationNodeNatural {m} (test : Source.Formula 1) (w code : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (proofTreeEquationNodeNaturalSentence test w code) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ProofTreeEntrySyntax.node test w code) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (ProofTreeEntrySyntax.node test w code) := .hyp (Or.inl rfl)
  exact ProofTreeEquationUnique.node_natural test hZ w code h0 h1

theorem proofTreeEquationNodeNatural_kernel_certificate {m} (test : Source.Formula 1) (w code : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (proofTreeEquationNodeNaturalSentence test w code)) := TheoryTransport.sentence (source_proofTreeEquationNodeNatural test w code)

theorem native_proofTreeEquationNodeNatural {m} (test : Source.Formula 1) (w code : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (proofTreeEquationNodeNaturalSentence test w code)) := ZFReplay.replay (proofTreeEquationNodeNatural_kernel_certificate test w code)

def proofTreeEquationSolutionNaturalSentence {m} (test : Source.Formula 1) (P : Source.Formula 2) (w code : Fin m) : Source.Sentence := ((omega w).imp ((ProofTreeEquationSyntax.equation test P w).imp ((ProofTreeInductionSyntax.property P w code).imp ((Formula.mem code w))))).close

theorem source_proofTreeEquationSolutionNatural {m} (test : Source.Formula 1) (P : Source.Formula 2) (w code : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (proofTreeEquationSolutionNaturalSentence test P w code) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ProofTreeInductionSyntax.property P w code) (Context.add (ProofTreeEquationSyntax.equation test P w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (ProofTreeEquationSyntax.equation test P w) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (ProofTreeInductionSyntax.property P w code) := .hyp (Or.inl rfl)
  exact ProofTreeEquationUnique.property_natural test P hZ w code h0 h1 h2

theorem proofTreeEquationSolutionNatural_kernel_certificate {m} (test : Source.Formula 1) (P : Source.Formula 2) (w code : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (proofTreeEquationSolutionNaturalSentence test P w code)) := TheoryTransport.sentence (source_proofTreeEquationSolutionNatural test P w code)

theorem native_proofTreeEquationSolutionNatural {m} (test : Source.Formula 1) (P : Source.Formula 2) (w code : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (proofTreeEquationSolutionNaturalSentence test P w code)) := ZFReplay.replay (proofTreeEquationSolutionNatural_kernel_certificate test P w code)

def proofTreeCanonicalNodeEquationSentence {m} (test : Source.Formula 1) (w : Fin m) : Source.Sentence := ((omega w).imp ((ProofTreeEquationSyntax.equation test (ProofTreeEquationCanonical.nodeTemplate test) w))).close

theorem source_proofTreeCanonicalNodeEquation {m} (test : Source.Formula 1) (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (proofTreeCanonicalNodeEquationSentence test w) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact ProofTreeEquationCanonical.equation_proved test hZ w h0

theorem proofTreeCanonicalNodeEquation_kernel_certificate {m} (test : Source.Formula 1) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (proofTreeCanonicalNodeEquationSentence test w)) := TheoryTransport.sentence (source_proofTreeCanonicalNodeEquation test w)

theorem native_proofTreeCanonicalNodeEquation {m} (test : Source.Formula 1) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (proofTreeCanonicalNodeEquationSentence test w)) := ZFReplay.replay (proofTreeCanonicalNodeEquation_kernel_certificate test w)

end PPAC.Migration.Internal.ObjectProofTreeEquation
