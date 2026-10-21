import PPAC.Migration.GraphPointwiseDomain

/-! 任意完整函数图的逐点外延性：六个全参数闭句和原核证书。 -/
namespace PPAC.Migration.ObjectGraphPointwise
open Source SourceAlgebra SourceLogic GraphSyntax GraphFamilySyntax GraphPointwiseSyntax RestrictionSyntax

def assumptions : Theory := fun q => q = Source.SetLanguage.extensionality

def subsetSentence : Source.Sentence := ((entriesOn (0 : Fin 3) 2).imp
  ((edgeIncluded 0 1).imp (subset 0 1))).close

def edgesSentence : Source.Sentence := ((entriesOn (0 : Fin 4) 2).imp
  ((entriesOn 1 3).imp ((sameEdges 0 1).imp (.equal 0 1)))).close

def inclusionSentence : Source.Sentence := ((functionOn (0 : Fin 4) 2).imp
  ((functionOn 1 3).imp ((subset 2 3).imp ((agrees 0 1).imp (subset 0 1))))).close

def equalitySentence : Source.Sentence := ((functionOn (0 : Fin 3) 2).imp
  ((functionOn 1 2).imp ((agrees 0 1).imp (.equal 0 1)))).close

def domainSentence : Source.Sentence := ((functionOn (0 : Fin 2) 1).imp (GraphDomainSyntax.domain 1 0)).close

def domainUniqueSentence : Source.Sentence := ((functionOn (0 : Fin 3) 1).imp
  ((functionOn 0 2).imp (.equal 1 2))).close

theorem source_subset : Derives (assumptions.at 0) subsetSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  have he : Derives (assumptions.at 3) (Source.SetLanguage.extensionality.rename Fin.elim0) := .hyp ⟨_, rfl, rfl⟩
  exact GraphPointwiseEntries.graph_subset 0 1 2 (add (add he _) _) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem source_edges : Derives (assumptions.at 0) edgesSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  have he : Derives (assumptions.at 4) (Source.SetLanguage.extensionality.rename Fin.elim0) := .hyp ⟨_, rfl, rfl⟩
  exact GraphPointwiseEntries.equal_of_edges 0 1 2 3 (add (add (add he _) _) _)
    (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem source_inclusion : Derives (assumptions.at 0) inclusionSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  have he : Derives (assumptions.at 4) (Source.SetLanguage.extensionality.rename Fin.elim0) := .hyp ⟨_, rfl, rfl⟩
  exact GraphPointwise.subset_of_agrees 0 1 2 3 (add (add (add (add he _) _) _) _)
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem source_equality : Derives (assumptions.at 0) equalitySentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  have he : Derives (assumptions.at 3) (Source.SetLanguage.extensionality.rename Fin.elim0) := .hyp ⟨_, rfl, rfl⟩
  exact GraphPointwise.equal_of_agrees 0 1 2 (add (add (add he _) _) _)
    (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem source_domain : Derives (assumptions.at 0) domainSentence := by
  apply close_derives
  apply Derives.impI
  have he : Derives (assumptions.at 2) (Source.SetLanguage.extensionality.rename Fin.elim0) := .hyp ⟨_, rfl, rfl⟩
  exact GraphPointwiseDomain.from_function 0 1 (add he _) (.hyp (Or.inl rfl))

theorem source_domainUnique : Derives (assumptions.at 0) domainUniqueSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  have he : Derives (assumptions.at 3) (Source.SetLanguage.extensionality.rename Fin.elim0) := .hyp ⟨_, rfl, rfl⟩
  exact GraphPointwiseDomain.unique 0 1 2 (add (add he _) _) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem source_ZF_replay {p : Source.Sentence} (h : Derives (assumptions.at 0) p) : Derives (Source.SetLanguage.ZF.at 0) p := by
  refine Derives.weaken ?_ h
  rintro q ⟨_, rfl, rfl⟩
  exact ⟨_, Source.SetLanguage.IsZFAxiom.extensionality, rfl⟩

theorem native_replay {free : Syntax.Ctx}
    {Γ : YesMetaZFC.Logic.FirstOrder.Context YesMetaZFC.SetTheory.PureSetLanguage free} {p : Syntax.Fm [] free}
    (h : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory assumptions) Γ p) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF Γ p := by
  apply YesMetaZFC.Logic.FirstOrder.Derives.theory_cut (hFormula := h)
  rintro q ⟨_, rfl, rfl⟩
  exact ZFEquivalence.source_extensionality

theorem subset_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory assumptions) []
    (Translation.sentence subsetSentence) := TheoryTransport.sentence source_subset

theorem source_ZF_subset : Derives (Source.SetLanguage.ZF.at 0) subsetSentence := source_ZF_replay source_subset

theorem native_subset : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence subsetSentence) :=
  native_replay subset_kernel_certificate

theorem edges_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory assumptions) []
    (Translation.sentence edgesSentence) := TheoryTransport.sentence source_edges

theorem source_ZF_edges : Derives (Source.SetLanguage.ZF.at 0) edgesSentence := source_ZF_replay source_edges

theorem native_edges : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence edgesSentence) :=
  native_replay edges_kernel_certificate

theorem inclusion_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory assumptions) []
    (Translation.sentence inclusionSentence) := TheoryTransport.sentence source_inclusion

theorem source_ZF_inclusion : Derives (Source.SetLanguage.ZF.at 0) inclusionSentence := source_ZF_replay source_inclusion

theorem native_inclusion : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence inclusionSentence) :=
  native_replay inclusion_kernel_certificate

theorem equality_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory assumptions) []
    (Translation.sentence equalitySentence) := TheoryTransport.sentence source_equality

theorem source_ZF_equality : Derives (Source.SetLanguage.ZF.at 0) equalitySentence := source_ZF_replay source_equality

theorem native_equality : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence equalitySentence) :=
  native_replay equality_kernel_certificate

theorem domain_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory assumptions) []
    (Translation.sentence domainSentence) := TheoryTransport.sentence source_domain

theorem source_ZF_domain : Derives (Source.SetLanguage.ZF.at 0) domainSentence := source_ZF_replay source_domain

theorem native_domain : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence domainSentence) :=
  native_replay domain_kernel_certificate

theorem domainUnique_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory assumptions) []
    (Translation.sentence domainUniqueSentence) := TheoryTransport.sentence source_domainUnique

theorem source_ZF_domainUnique : Derives (Source.SetLanguage.ZF.at 0) domainUniqueSentence := source_ZF_replay source_domainUnique

theorem native_domainUnique : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence domainUniqueSentence) :=
  native_replay domainUnique_kernel_certificate
end PPAC.Migration.ObjectGraphPointwise
