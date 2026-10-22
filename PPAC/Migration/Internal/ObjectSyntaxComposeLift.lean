import PPAC.Migration.Internal.SyntaxComposeLiftCodeLaws

/-! 真实binder提升与实际图/自然码复合相容及完整候选识别的源和YesMetaZFC原核闭句。 -/
namespace PPAC.Migration.Internal.ObjectSyntaxComposeLift
open Source SourceAlgebra SourceLogic OmegaSyntax

def zeroSentence {m} (w r t a c e A C E ρ τ i j : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxIndexLiftSyntax.lifted w r a c A C ρ).imp ((SyntaxIndexLiftSyntax.lifted w t c e C E τ).imp ((empty i).imp ((empty j).imp (SyntaxComposeSyntax.value ρ τ i j)))))).close

theorem source_zero {m} (w r t a c e A C E ρ τ i j : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (zeroSentence w r t a c e A C E ρ τ i j) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (empty j) (Context.add (empty i) (Context.add (SyntaxIndexLiftSyntax.lifted w t c e C E τ) (Context.add (SyntaxIndexLiftSyntax.lifted w r a c A C ρ) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxIndexLiftSyntax.lifted w r a c A C ρ) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (SyntaxIndexLiftSyntax.lifted w t c e C E τ) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (empty i) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (empty j) := .hyp (Or.inl rfl)
  exact SyntaxComposeLiftPoint.zero hZ w r t a c e A C E ρ τ i j h0 h1 h2 h3 h4

theorem zero_kernel_certificate {m} (w r t a c e A C E ρ τ i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (zeroSentence w r t a c e A C E ρ τ i j)) := TheoryTransport.sentence (source_zero w r t a c e A C E ρ τ i j)

theorem native_zero {m} (w r t a c e A C E ρ τ i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (zeroSentence w r t a c e A C E ρ τ i j)) := ZFReplay.replay (zero_kernel_certificate w r t a c e A C E ρ τ i j)

def shiftedSentence {m} (w r t a c e g A C E ρ τ i j : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxComposeSyntax.composed w r t a c e g).imp ((SyntaxIndexLiftSyntax.lifted w r a c A C ρ).imp ((SyntaxIndexLiftSyntax.lifted w t c e C E τ).imp ((SyntaxIndexLiftSyntax.shifted g a i j).imp (SyntaxComposeSyntax.value ρ τ i j)))))).close

theorem source_shifted {m} (w r t a c e g A C E ρ τ i j : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (shiftedSentence w r t a c e g A C E ρ τ i j) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxIndexLiftSyntax.shifted g a i j) (Context.add (SyntaxIndexLiftSyntax.lifted w t c e C E τ) (Context.add (SyntaxIndexLiftSyntax.lifted w r a c A C ρ) (Context.add (SyntaxComposeSyntax.composed w r t a c e g) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxComposeSyntax.composed w r t a c e g) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (SyntaxIndexLiftSyntax.lifted w r a c A C ρ) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (SyntaxIndexLiftSyntax.lifted w t c e C E τ) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (SyntaxIndexLiftSyntax.shifted g a i j) := .hyp (Or.inl rfl)
  exact SyntaxComposeLiftPoint.shifted hZ w r t a c e g A C E ρ τ i j h0 h1 h2 h3 h4

theorem shifted_kernel_certificate {m} (w r t a c e g A C E ρ τ i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (shiftedSentence w r t a c e g A C E ρ τ i j)) := TheoryTransport.sentence (source_shifted w r t a c e g A C E ρ τ i j)

theorem native_shifted {m} (w r t a c e g A C E ρ τ i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (shiftedSentence w r t a c e g A C E ρ τ i j)) := ZFReplay.replay (shifted_kernel_certificate w r t a c e g A C E ρ τ i j)

def valueForwardSentence {m} (w r t a c e g A C E ρ τ i j : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxComposeSyntax.composed w r t a c e g).imp ((SyntaxIndexLiftSyntax.lifted w r a c A C ρ).imp ((SyntaxIndexLiftSyntax.lifted w t c e C E τ).imp ((SyntaxIndexLiftSyntax.value g a i j).imp (SyntaxComposeSyntax.value ρ τ i j)))))).close

theorem source_valueForward {m} (w r t a c e g A C E ρ τ i j : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (valueForwardSentence w r t a c e g A C E ρ τ i j) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxIndexLiftSyntax.value g a i j) (Context.add (SyntaxIndexLiftSyntax.lifted w t c e C E τ) (Context.add (SyntaxIndexLiftSyntax.lifted w r a c A C ρ) (Context.add (SyntaxComposeSyntax.composed w r t a c e g) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxComposeSyntax.composed w r t a c e g) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (SyntaxIndexLiftSyntax.lifted w r a c A C ρ) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (SyntaxIndexLiftSyntax.lifted w t c e C E τ) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (SyntaxIndexLiftSyntax.value g a i j) := .hyp (Or.inl rfl)
  exact SyntaxComposeLiftPoint.value_forward hZ w r t a c e g A C E ρ τ i j h0 h1 h2 h3 h4

theorem valueForward_kernel_certificate {m} (w r t a c e g A C E ρ τ i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (valueForwardSentence w r t a c e g A C E ρ τ i j)) := TheoryTransport.sentence (source_valueForward w r t a c e g A C E ρ τ i j)

theorem native_valueForward {m} (w r t a c e g A C E ρ τ i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (valueForwardSentence w r t a c e g A C E ρ τ i j)) := ZFReplay.replay (valueForward_kernel_certificate w r t a c e g A C E ρ τ i j)

def edgeForwardSentence {m} (w r t a c e g A C E ρ τ γ i j : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxComposeSyntax.composed w r t a c e g).imp ((SyntaxIndexLiftSyntax.lifted w r a c A C ρ).imp ((SyntaxIndexLiftSyntax.lifted w t c e C E τ).imp ((SyntaxIndexLiftSyntax.lifted w g a e A E γ).imp ((GraphSyntax.edge γ i j).imp (SyntaxComposeSyntax.value ρ τ i j))))))).close

theorem source_edgeForward {m} (w r t a c e g A C E ρ τ γ i j : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (edgeForwardSentence w r t a c e g A C E ρ τ γ i j) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (GraphSyntax.edge γ i j) (Context.add (SyntaxIndexLiftSyntax.lifted w g a e A E γ) (Context.add (SyntaxIndexLiftSyntax.lifted w t c e C E τ) (Context.add (SyntaxIndexLiftSyntax.lifted w r a c A C ρ) (Context.add (SyntaxComposeSyntax.composed w r t a c e g) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (SyntaxComposeSyntax.composed w r t a c e g) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (SyntaxIndexLiftSyntax.lifted w r a c A C ρ) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (SyntaxIndexLiftSyntax.lifted w t c e C E τ) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (SyntaxIndexLiftSyntax.lifted w g a e A E γ) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (GraphSyntax.edge γ i j) := .hyp (Or.inl rfl)
  exact SyntaxComposeLiftPoint.edge_forward hZ w r t a c e g A C E ρ τ γ i j h0 h1 h2 h3 h4 h5

theorem edgeForward_kernel_certificate {m} (w r t a c e g A C E ρ τ γ i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (edgeForwardSentence w r t a c e g A C E ρ τ γ i j)) := TheoryTransport.sentence (source_edgeForward w r t a c e g A C E ρ τ γ i j)

theorem native_edgeForward {m} (w r t a c e g A C E ρ τ γ i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (edgeForwardSentence w r t a c e g A C E ρ τ γ i j)) := ZFReplay.replay (edgeForward_kernel_certificate w r t a c e g A C E ρ τ γ i j)

def includedAgreementSentence {m} (f g d : Fin m) : Source.Sentence := ((GraphSyntax.functionOn g d).imp ((GraphPointwiseSyntax.edgeIncluded f g).imp (GraphFamilySyntax.agrees f g))).close

theorem source_includedAgreement {m} (f g d : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (includedAgreementSentence f g d) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (GraphPointwiseSyntax.edgeIncluded f g) (Context.add (GraphSyntax.functionOn g d) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (GraphSyntax.functionOn g d) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (GraphPointwiseSyntax.edgeIncluded f g) := .hyp (Or.inl rfl)
  exact SyntaxComposeLiftGraph.agrees_of_included hZ f g d h0 h1

theorem includedAgreement_kernel_certificate {m} (f g d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (includedAgreementSentence f g d)) := TheoryTransport.sentence (source_includedAgreement f g d)

theorem native_includedAgreement {m} (f g d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (includedAgreementSentence f g d)) := ZFReplay.replay (includedAgreement_kernel_certificate f g d)

def includedSentence {m} (w r t a c e g A C E ρ τ γ k : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxComposeSyntax.composed w r t a c e g).imp ((SyntaxIndexLiftSyntax.lifted w r a c A C ρ).imp ((SyntaxIndexLiftSyntax.lifted w t c e C E τ).imp ((SyntaxIndexLiftSyntax.lifted w g a e A E γ).imp ((SyntaxComposeSyntax.composed w ρ τ A C E k).imp (GraphPointwiseSyntax.edgeIncluded γ k))))))).close

theorem source_included {m} (w r t a c e g A C E ρ τ γ k : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (includedSentence w r t a c e g A C E ρ τ γ k) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxComposeSyntax.composed w ρ τ A C E k) (Context.add (SyntaxIndexLiftSyntax.lifted w g a e A E γ) (Context.add (SyntaxIndexLiftSyntax.lifted w t c e C E τ) (Context.add (SyntaxIndexLiftSyntax.lifted w r a c A C ρ) (Context.add (SyntaxComposeSyntax.composed w r t a c e g) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (SyntaxComposeSyntax.composed w r t a c e g) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (SyntaxIndexLiftSyntax.lifted w r a c A C ρ) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (SyntaxIndexLiftSyntax.lifted w t c e C E τ) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (SyntaxIndexLiftSyntax.lifted w g a e A E γ) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (SyntaxComposeSyntax.composed w ρ τ A C E k) := .hyp (Or.inl rfl)
  exact SyntaxComposeLiftGraph.included hZ w r t a c e g A C E ρ τ γ k h0 h1 h2 h3 h4 h5

theorem included_kernel_certificate {m} (w r t a c e g A C E ρ τ γ k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (includedSentence w r t a c e g A C E ρ τ γ k)) := TheoryTransport.sentence (source_included w r t a c e g A C E ρ τ γ k)

theorem native_included {m} (w r t a c e g A C E ρ τ γ k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (includedSentence w r t a c e g A C E ρ τ γ k)) := ZFReplay.replay (included_kernel_certificate w r t a c e g A C E ρ τ γ k)

def equalGraphsSentence {m} (w r t a c e g A C E ρ τ γ k : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxComposeSyntax.composed w r t a c e g).imp ((SyntaxIndexLiftSyntax.lifted w r a c A C ρ).imp ((SyntaxIndexLiftSyntax.lifted w t c e C E τ).imp ((SyntaxIndexLiftSyntax.lifted w g a e A E γ).imp ((SyntaxComposeSyntax.composed w ρ τ A C E k).imp (Formula.equal γ k))))))).close

theorem source_equalGraphs {m} (w r t a c e g A C E ρ τ γ k : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (equalGraphsSentence w r t a c e g A C E ρ τ γ k) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxComposeSyntax.composed w ρ τ A C E k) (Context.add (SyntaxIndexLiftSyntax.lifted w g a e A E γ) (Context.add (SyntaxIndexLiftSyntax.lifted w t c e C E τ) (Context.add (SyntaxIndexLiftSyntax.lifted w r a c A C ρ) (Context.add (SyntaxComposeSyntax.composed w r t a c e g) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (SyntaxComposeSyntax.composed w r t a c e g) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (SyntaxIndexLiftSyntax.lifted w r a c A C ρ) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (SyntaxIndexLiftSyntax.lifted w t c e C E τ) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (SyntaxIndexLiftSyntax.lifted w g a e A E γ) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (SyntaxComposeSyntax.composed w ρ τ A C E k) := .hyp (Or.inl rfl)
  exact SyntaxComposeLiftGraph.equal_to_composite hZ w r t a c e g A C E ρ τ γ k h0 h1 h2 h3 h4 h5

theorem equalGraphs_kernel_certificate {m} (w r t a c e g A C E ρ τ γ k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (equalGraphsSentence w r t a c e g A C E ρ τ γ k)) := TheoryTransport.sentence (source_equalGraphs w r t a c e g A C E ρ τ γ k)

theorem native_equalGraphs {m} (w r t a c e g A C E ρ τ γ k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (equalGraphsSentence w r t a c e g A C E ρ τ γ k)) := ZFReplay.replay (equalGraphs_kernel_certificate w r t a c e g A C E ρ τ γ k)

def graphCompositionSentence {m} (w r t a c e g A C E ρ τ γ : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxComposeSyntax.composed w r t a c e g).imp ((SyntaxIndexLiftSyntax.lifted w r a c A C ρ).imp ((SyntaxIndexLiftSyntax.lifted w t c e C E τ).imp ((SyntaxIndexLiftSyntax.lifted w g a e A E γ).imp (SyntaxComposeSyntax.composed w ρ τ A C E γ)))))).close

theorem source_graphComposition {m} (w r t a c e g A C E ρ τ γ : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (graphCompositionSentence w r t a c e g A C E ρ τ γ) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxIndexLiftSyntax.lifted w g a e A E γ) (Context.add (SyntaxIndexLiftSyntax.lifted w t c e C E τ) (Context.add (SyntaxIndexLiftSyntax.lifted w r a c A C ρ) (Context.add (SyntaxComposeSyntax.composed w r t a c e g) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxComposeSyntax.composed w r t a c e g) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (SyntaxIndexLiftSyntax.lifted w r a c A C ρ) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (SyntaxIndexLiftSyntax.lifted w t c e C E τ) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (SyntaxIndexLiftSyntax.lifted w g a e A E γ) := .hyp (Or.inl rfl)
  exact SyntaxComposeLiftGraph.composition hZ w r t a c e g A C E ρ τ γ h0 h1 h2 h3 h4

theorem graphComposition_kernel_certificate {m} (w r t a c e g A C E ρ τ γ : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (graphCompositionSentence w r t a c e g A C E ρ τ γ)) := TheoryTransport.sentence (source_graphComposition w r t a c e g A C E ρ τ γ)

theorem native_graphComposition {m} (w r t a c e g A C E ρ τ γ : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (graphCompositionSentence w r t a c e g A C E ρ τ γ)) := ZFReplay.replay (graphComposition_kernel_certificate w r t a c e g A C E ρ τ γ)

def graphEdgesSentence {m} (w r t a c e g A C E ρ τ γ i j : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxComposeSyntax.composed w r t a c e g).imp ((SyntaxIndexLiftSyntax.lifted w r a c A C ρ).imp ((SyntaxIndexLiftSyntax.lifted w t c e C E τ).imp ((SyntaxIndexLiftSyntax.lifted w g a e A E γ).imp ((GraphSyntax.edge γ i j).iff (SyntaxComposeSyntax.value ρ τ i j))))))).close

theorem source_graphEdges {m} (w r t a c e g A C E ρ τ γ i j : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (graphEdgesSentence w r t a c e g A C E ρ τ γ i j) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxIndexLiftSyntax.lifted w g a e A E γ) (Context.add (SyntaxIndexLiftSyntax.lifted w t c e C E τ) (Context.add (SyntaxIndexLiftSyntax.lifted w r a c A C ρ) (Context.add (SyntaxComposeSyntax.composed w r t a c e g) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxComposeSyntax.composed w r t a c e g) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (SyntaxIndexLiftSyntax.lifted w r a c A C ρ) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (SyntaxIndexLiftSyntax.lifted w t c e C E τ) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (SyntaxIndexLiftSyntax.lifted w g a e A E γ) := .hyp (Or.inl rfl)
  exact SyntaxComposeLiftGraph.edge_iff hZ w r t a c e g A C E ρ τ γ i j h0 h1 h2 h3 h4

theorem graphEdges_kernel_certificate {m} (w r t a c e g A C E ρ τ γ i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (graphEdgesSentence w r t a c e g A C E ρ τ γ i j)) := TheoryTransport.sentence (source_graphEdges w r t a c e g A C E ρ τ γ i j)

theorem native_graphEdges {m} (w r t a c e g A C E ρ τ γ i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (graphEdgesSentence w r t a c e g A C E ρ τ γ i j)) := ZFReplay.replay (graphEdges_kernel_certificate w r t a c e g A C E ρ τ γ i j)

def graphValuesSentence {m} (w r t a c e g A C E ρ τ γ i j : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxComposeSyntax.composed w r t a c e g).imp ((SyntaxIndexLiftSyntax.lifted w r a c A C ρ).imp ((SyntaxIndexLiftSyntax.lifted w t c e C E τ).imp ((SyntaxIndexLiftSyntax.lifted w g a e A E γ).imp ((SyntaxIndexLiftSyntax.value g a i j).iff (SyntaxComposeSyntax.value ρ τ i j))))))).close

theorem source_graphValues {m} (w r t a c e g A C E ρ τ γ i j : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (graphValuesSentence w r t a c e g A C E ρ τ γ i j) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxIndexLiftSyntax.lifted w g a e A E γ) (Context.add (SyntaxIndexLiftSyntax.lifted w t c e C E τ) (Context.add (SyntaxIndexLiftSyntax.lifted w r a c A C ρ) (Context.add (SyntaxComposeSyntax.composed w r t a c e g) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxComposeSyntax.composed w r t a c e g) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (SyntaxIndexLiftSyntax.lifted w r a c A C ρ) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (SyntaxIndexLiftSyntax.lifted w t c e C E τ) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (SyntaxIndexLiftSyntax.lifted w g a e A E γ) := .hyp (Or.inl rfl)
  exact SyntaxComposeLiftGraph.value_iff hZ w r t a c e g A C E ρ τ γ i j h0 h1 h2 h3 h4

theorem graphValues_kernel_certificate {m} (w r t a c e g A C E ρ τ γ i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (graphValuesSentence w r t a c e g A C E ρ τ γ i j)) := TheoryTransport.sentence (source_graphValues w r t a c e g A C E ρ τ γ i j)

theorem native_graphValues {m} (w r t a c e g A C E ρ τ γ i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (graphValuesSentence w r t a c e g A C E ρ τ γ i j)) := ZFReplay.replay (graphValues_kernel_certificate w r t a c e g A C E ρ τ γ i j)

def liftedIffComposedSentence {m} (w r t a c e g A C E ρ τ γ : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxComposeSyntax.composed w r t a c e g).imp ((SyntaxIndexLiftSyntax.lifted w r a c A C ρ).imp ((SyntaxIndexLiftSyntax.lifted w t c e C E τ).imp ((SyntaxIndexLiftSyntax.lifted w g a e A E γ).iff (SyntaxComposeSyntax.composed w ρ τ A C E γ)))))).close

theorem source_liftedIffComposed {m} (w r t a c e g A C E ρ τ γ : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (liftedIffComposedSentence w r t a c e g A C E ρ τ γ) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxIndexLiftSyntax.lifted w t c e C E τ) (Context.add (SyntaxIndexLiftSyntax.lifted w r a c A C ρ) (Context.add (SyntaxComposeSyntax.composed w r t a c e g) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxComposeSyntax.composed w r t a c e g) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxIndexLiftSyntax.lifted w r a c A C ρ) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxIndexLiftSyntax.lifted w t c e C E τ) := .hyp (Or.inl rfl)
  exact SyntaxComposeLiftGraph.lifted_iff_composed hZ w r t a c e g A C E ρ τ γ h0 h1 h2 h3

theorem liftedIffComposed_kernel_certificate {m} (w r t a c e g A C E ρ τ γ : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (liftedIffComposedSentence w r t a c e g A C E ρ τ γ)) := TheoryTransport.sentence (source_liftedIffComposed w r t a c e g A C E ρ τ γ)

theorem native_liftedIffComposed {m} (w r t a c e g A C E ρ τ γ : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (liftedIffComposedSentence w r t a c e g A C E ρ τ γ)) := ZFReplay.replay (liftedIffComposed_kernel_certificate w r t a c e g A C E ρ τ γ)

def atSourcesSentence {m} (w r t g a c e R T K A C E Lr Lt Lk : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxComposeSyntax.composed w r t a c e g).imp ((SyntaxMapCodeSyntax.encoded w r a c R).imp ((SyntaxMapCodeSyntax.encoded w t c e T).imp ((SyntaxMapCodeSyntax.encoded w g a e K).imp ((SyntaxMapLiftSyntax.codedLift w a c R A C Lr).imp ((SyntaxMapLiftSyntax.codedLift w c e T C E Lt).imp ((SyntaxMapLiftSyntax.codedLift w a e K A E Lk).imp (SyntaxComposeCodeSyntax.coded w A C E Lr Lt Lk))))))))).close

theorem source_atSources {m} (w r t g a c e R T K A C E Lr Lt Lk : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (atSourcesSentence w r t g a c e R T K A C E Lr Lt Lk) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMapLiftSyntax.codedLift w a e K A E Lk) (Context.add (SyntaxMapLiftSyntax.codedLift w c e T C E Lt) (Context.add (SyntaxMapLiftSyntax.codedLift w a c R A C Lr) (Context.add (SyntaxMapCodeSyntax.encoded w g a e K) (Context.add (SyntaxMapCodeSyntax.encoded w t c e T) (Context.add (SyntaxMapCodeSyntax.encoded w r a c R) (Context.add (SyntaxComposeSyntax.composed w r t a c e g) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  have h1 : Derives Δ (SyntaxComposeSyntax.composed w r t a c e g) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h2 : Derives Δ (SyntaxMapCodeSyntax.encoded w r a c R) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h3 : Derives Δ (SyntaxMapCodeSyntax.encoded w t c e T) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h4 : Derives Δ (SyntaxMapCodeSyntax.encoded w g a e K) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h5 : Derives Δ (SyntaxMapLiftSyntax.codedLift w a c R A C Lr) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h6 : Derives Δ (SyntaxMapLiftSyntax.codedLift w c e T C E Lt) := .hyp (Or.inr (Or.inl rfl))
  have h7 : Derives Δ (SyntaxMapLiftSyntax.codedLift w a e K A E Lk) := .hyp (Or.inl rfl)
  exact SyntaxComposeLiftCode.at_sources hZ w r t g a c e R T K A C E Lr Lt Lk h0 h1 h2 h3 h4 h5 h6 h7

theorem atSources_kernel_certificate {m} (w r t g a c e R T K A C E Lr Lt Lk : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (atSourcesSentence w r t g a c e R T K A C E Lr Lt Lk)) := TheoryTransport.sentence (source_atSources w r t g a c e R T K A C E Lr Lt Lk)

theorem native_atSources {m} (w r t g a c e R T K A C E Lr Lt Lk : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (atSourcesSentence w r t g a c e R T K A C E Lr Lt Lk)) := ZFReplay.replay (atSources_kernel_certificate w r t g a c e R T K A C E Lr Lt Lk)

def codedCompositionSentence {m} (w a c e R T K A C E Lr Lt Lk : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxComposeCodeSyntax.coded w a c e R T K).imp ((SyntaxMapLiftSyntax.codedLift w a c R A C Lr).imp ((SyntaxMapLiftSyntax.codedLift w c e T C E Lt).imp ((SyntaxMapLiftSyntax.codedLift w a e K A E Lk).imp (SyntaxComposeCodeSyntax.coded w A C E Lr Lt Lk)))))).close

theorem source_codedComposition {m} (w a c e R T K A C E Lr Lt Lk : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (codedCompositionSentence w a c e R T K A C E Lr Lt Lk) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMapLiftSyntax.codedLift w a e K A E Lk) (Context.add (SyntaxMapLiftSyntax.codedLift w c e T C E Lt) (Context.add (SyntaxMapLiftSyntax.codedLift w a c R A C Lr) (Context.add (SyntaxComposeCodeSyntax.coded w a c e R T K) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxComposeCodeSyntax.coded w a c e R T K) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (SyntaxMapLiftSyntax.codedLift w a c R A C Lr) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (SyntaxMapLiftSyntax.codedLift w c e T C E Lt) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (SyntaxMapLiftSyntax.codedLift w a e K A E Lk) := .hyp (Or.inl rfl)
  exact SyntaxComposeLiftCode.composition hZ w a c e R T K A C E Lr Lt Lk h0 h1 h2 h3 h4

theorem codedComposition_kernel_certificate {m} (w a c e R T K A C E Lr Lt Lk : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (codedCompositionSentence w a c e R T K A C E Lr Lt Lk)) := TheoryTransport.sentence (source_codedComposition w a c e R T K A C E Lr Lt Lk)

theorem native_codedComposition {m} (w a c e R T K A C E Lr Lt Lk : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (codedCompositionSentence w a c e R T K A C E Lr Lt Lk)) := ZFReplay.replay (codedComposition_kernel_certificate w a c e R T K A C E Lr Lt Lk)

def codedIffSentence {m} (w a c e R T K A C E Lr Lt Lk : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxComposeCodeSyntax.coded w a c e R T K).imp ((SyntaxMapLiftSyntax.codedLift w a c R A C Lr).imp ((SyntaxMapLiftSyntax.codedLift w c e T C E Lt).imp ((SyntaxMapLiftSyntax.codedLift w a e K A E Lk).iff (SyntaxComposeCodeSyntax.coded w A C E Lr Lt Lk)))))).close

theorem source_codedIff {m} (w a c e R T K A C E Lr Lt Lk : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (codedIffSentence w a c e R T K A C E Lr Lt Lk) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMapLiftSyntax.codedLift w c e T C E Lt) (Context.add (SyntaxMapLiftSyntax.codedLift w a c R A C Lr) (Context.add (SyntaxComposeCodeSyntax.coded w a c e R T K) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxComposeCodeSyntax.coded w a c e R T K) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxMapLiftSyntax.codedLift w a c R A C Lr) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxMapLiftSyntax.codedLift w c e T C E Lt) := .hyp (Or.inl rfl)
  exact SyntaxComposeLiftCodeLaws.coded_iff hZ w a c e R T K A C E Lr Lt Lk h0 h1 h2 h3

theorem codedIff_kernel_certificate {m} (w a c e R T K A C E Lr Lt Lk : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (codedIffSentence w a c e R T K A C E Lr Lt Lk)) := TheoryTransport.sentence (source_codedIff w a c e R T K A C E Lr Lt Lk)

theorem native_codedIff {m} (w a c e R T K A C E Lr Lt Lk : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (codedIffSentence w a c e R T K A C E Lr Lt Lk)) := ZFReplay.replay (codedIff_kernel_certificate w a c e R T K A C E Lr Lt Lk)

def middleEqualSentence {m} (w a c e R T A C D E Lr Lt : Fin m) : Source.Sentence := ((SyntaxMapLiftSyntax.codedLift w a c R A C Lr).imp ((SyntaxMapLiftSyntax.codedLift w c e T D E Lt).imp (Formula.equal C D))).close

theorem source_middleEqual {m} (w a c e R T A C D E Lr Lt : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (middleEqualSentence w a c e R T A C D E Lr Lt) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMapLiftSyntax.codedLift w c e T D E Lt) (Context.add (SyntaxMapLiftSyntax.codedLift w a c R A C Lr) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (SyntaxMapLiftSyntax.codedLift w a c R A C Lr) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxMapLiftSyntax.codedLift w c e T D E Lt) := .hyp (Or.inl rfl)
  exact SyntaxComposeLiftCodeLaws.middle_equal hZ w a c e R T A C D E Lr Lt h0 h1

theorem middleEqual_kernel_certificate {m} (w a c e R T A C D E Lr Lt : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (middleEqualSentence w a c e R T A C D E Lr Lt)) := TheoryTransport.sentence (source_middleEqual w a c e R T A C D E Lr Lt)

theorem native_middleEqual {m} (w a c e R T A C D E Lr Lt : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (middleEqualSentence w a c e R T A C D E Lr Lt)) := ZFReplay.replay (middleEqual_kernel_certificate w a c e R T A C D E Lr Lt)

def mixedMiddleSentence {m} (w a c e R T K A C D E Lr Lt Lk : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxComposeCodeSyntax.coded w a c e R T K).imp ((SyntaxMapLiftSyntax.codedLift w a c R A C Lr).imp ((SyntaxMapLiftSyntax.codedLift w c e T D E Lt).imp ((SyntaxMapLiftSyntax.codedLift w a e K A E Lk).imp ((Formula.equal C D).conj (SyntaxComposeCodeSyntax.coded w A C E Lr Lt Lk))))))).close

theorem source_mixedMiddle {m} (w a c e R T K A C D E Lr Lt Lk : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (mixedMiddleSentence w a c e R T K A C D E Lr Lt Lk) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMapLiftSyntax.codedLift w a e K A E Lk) (Context.add (SyntaxMapLiftSyntax.codedLift w c e T D E Lt) (Context.add (SyntaxMapLiftSyntax.codedLift w a c R A C Lr) (Context.add (SyntaxComposeCodeSyntax.coded w a c e R T K) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxComposeCodeSyntax.coded w a c e R T K) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (SyntaxMapLiftSyntax.codedLift w a c R A C Lr) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (SyntaxMapLiftSyntax.codedLift w c e T D E Lt) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (SyntaxMapLiftSyntax.codedLift w a e K A E Lk) := .hyp (Or.inl rfl)
  exact SyntaxComposeLiftCodeLaws.mixed_middle hZ w a c e R T K A C D E Lr Lt Lk h0 h1 h2 h3 h4

theorem mixedMiddle_kernel_certificate {m} (w a c e R T K A C D E Lr Lt Lk : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (mixedMiddleSentence w a c e R T K A C D E Lr Lt Lk)) := TheoryTransport.sentence (source_mixedMiddle w a c e R T K A C D E Lr Lt Lk)

theorem native_mixedMiddle {m} (w a c e R T K A C D E Lr Lt Lk : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (mixedMiddleSentence w a c e R T K A C D E Lr Lt Lk)) := ZFReplay.replay (mixedMiddle_kernel_certificate w a c e R T K A C D E Lr Lt Lk)

def mixedIffSentence {m} (w a c e R T K A C D E Lr Lt Lk : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxComposeCodeSyntax.coded w a c e R T K).imp ((SyntaxMapLiftSyntax.codedLift w a c R A C Lr).imp ((SyntaxMapLiftSyntax.codedLift w c e T D E Lt).imp ((Formula.equal C D).conj ((SyntaxMapLiftSyntax.codedLift w a e K A E Lk).iff (SyntaxComposeCodeSyntax.coded w A C E Lr Lt Lk))))))).close

theorem source_mixedIff {m} (w a c e R T K A C D E Lr Lt Lk : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (mixedIffSentence w a c e R T K A C D E Lr Lt Lk) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMapLiftSyntax.codedLift w c e T D E Lt) (Context.add (SyntaxMapLiftSyntax.codedLift w a c R A C Lr) (Context.add (SyntaxComposeCodeSyntax.coded w a c e R T K) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxComposeCodeSyntax.coded w a c e R T K) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxMapLiftSyntax.codedLift w a c R A C Lr) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxMapLiftSyntax.codedLift w c e T D E Lt) := .hyp (Or.inl rfl)
  exact SyntaxComposeLiftCodeLaws.mixed_iff hZ w a c e R T K A C D E Lr Lt Lk h0 h1 h2 h3

theorem mixedIff_kernel_certificate {m} (w a c e R T K A C D E Lr Lt Lk : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (mixedIffSentence w a c e R T K A C D E Lr Lt Lk)) := TheoryTransport.sentence (source_mixedIff w a c e R T K A C D E Lr Lt Lk)

theorem native_mixedIff {m} (w a c e R T K A C D E Lr Lt Lk : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (mixedIffSentence w a c e R T K A C D E Lr Lt Lk)) := ZFReplay.replay (mixedIff_kernel_certificate w a c e R T K A C D E Lr Lt Lk)

end PPAC.Migration.Internal.ObjectSyntaxComposeLift
