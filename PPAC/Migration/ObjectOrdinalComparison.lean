import PPAC.Migration.OrdinalTrichotomy

/-! 原对象序数的初段、任意两序数比较和三歧闭句；实际原Hilbert核证书。 -/
namespace PPAC.Migration.ObjectOrdinalComparison
open Source SourceAlgebra SourceLogic OrdinalSyntax OrdinalDifference RestrictionSyntax

def assumptions : Theory := fun q => q = Source.SetLanguage.extensionality ∨
  q = Source.SetLanguage.foundation ∨ q = Source.SetLanguage.separation outsideMatrix

def differenceSentence : Source.Sentence := ((subset (0 : Fin 2) 1).neg.imp (minimalExists 0 1)).close

def initialSentence : Source.Sentence := ((ordinal (0 : Fin 2)).imp ((transitiveSet 1).imp
  ((subset 1 0).imp ((Formula.equal 1 0).disj (.mem 1 0))))).close

def comparisonSentence : Source.Sentence := ((ordinal (0 : Fin 2)).imp
  ((ordinal 1).imp (OrdinalComparison.comparison 0 1))).close

def trichotomySentence : Source.Sentence := ((ordinal (0 : Fin 2)).imp
  ((ordinal 1).imp (OrdinalTrichotomy.trichotomy 0 1))).close

def subsetSentence : Source.Sentence := ((ordinal (0 : Fin 2)).imp ((ordinal 1).imp
  ((subset 0 1).iff ((Formula.equal 0 1).disj (.mem 0 1))))).close

def asymmetricSentence : Source.Sentence := ((ordinal (0 : Fin 2)).imp
  ((Formula.mem 0 1).imp (Formula.mem 1 0).neg)).close

theorem ext_at (m : Nat) : Derives (assumptions.at m) (Source.SetLanguage.extensionality.rename Fin.elim0) :=
  .hyp ⟨_, Or.inl rfl, rfl⟩

theorem foundation_at (m : Nat) : Derives (assumptions.at m) (Source.SetLanguage.foundation.rename Fin.elim0) :=
  .hyp ⟨_, Or.inr (Or.inl rfl), rfl⟩

theorem separation_at (m : Nat) : Derives (assumptions.at m) ((Source.SetLanguage.separation outsideMatrix).rename Fin.elim0) :=
  .hyp ⟨_, Or.inr (Or.inr rfl), rfl⟩

theorem source_difference : Derives (assumptions.at 0) differenceSentence := by
  apply close_derives
  apply Derives.impI
  exact exists_minimal 0 1 (add (separation_at 2) _) (add (foundation_at 2) _)
    (has_of_not_subset 0 1 (.hyp (Or.inl rfl)))

theorem source_initial : Derives (assumptions.at 0) initialSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact OrdinalInitialSegment.initial_segment 0 1
    (add (add (add (ext_at 2) _) _) _) (add (add (add (foundation_at 2) _) _) _) (add (add (add (separation_at 2) _) _) _)
    (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem source_comparison : Derives (assumptions.at 0) comparisonSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  exact OrdinalComparison.compare 0 1
    (add (add (ext_at 2) _) _) (add (add (foundation_at 2) _) _) (add (add (separation_at 2) _) _)
    (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem source_trichotomy : Derives (assumptions.at 0) trichotomySentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  exact OrdinalTrichotomy.prove 0 1
    (add (add (ext_at 2) _) _) (add (add (foundation_at 2) _) _) (add (add (separation_at 2) _) _)
    (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem source_subset : Derives (assumptions.at 0) subsetSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  exact OrdinalComparison.subset_iff 0 1
    (add (add (ext_at 2) _) _) (add (add (foundation_at 2) _) _) (add (add (separation_at 2) _) _)
    (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem source_asymmetric : Derives (assumptions.at 0) asymmetricSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  exact OrdinalComparison.asymmetric 0 1 (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem source_ZF_replay {p : Source.Sentence} (h : Derives (assumptions.at 0) p) : Derives (Source.SetLanguage.ZF.at 0) p := by
  refine Derives.weaken ?_ h
  rintro q ⟨_, hr, rfl⟩
  rcases hr with rfl | rfl | rfl
  · exact ⟨_, Source.SetLanguage.IsZFAxiom.extensionality, rfl⟩
  · exact ⟨_, Source.SetLanguage.IsZFAxiom.foundation, rfl⟩
  · exact ⟨_, Source.SetLanguage.IsZFAxiom.separation outsideMatrix, rfl⟩

theorem native_replay {free : Syntax.Ctx}
    {Γ : YesMetaZFC.Logic.FirstOrder.Context YesMetaZFC.SetTheory.PureSetLanguage free} {p : Syntax.Fm [] free}
    (h : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory assumptions) Γ p) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF Γ p := by
  apply YesMetaZFC.Logic.FirstOrder.Derives.theory_cut (hFormula := h)
  rintro q ⟨_, hr, rfl⟩
  rcases hr with rfl | rfl | rfl
  · exact ZFEquivalence.source_extensionality
  · exact ZFEquivalence.source_foundation
  · exact SeparationSyntax.source_separation outsideMatrix

theorem difference_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory assumptions) []
    (Translation.sentence differenceSentence) := TheoryTransport.sentence source_difference

theorem source_ZF_difference : Derives (Source.SetLanguage.ZF.at 0) differenceSentence := source_ZF_replay source_difference

theorem native_difference : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence differenceSentence) :=
  native_replay difference_kernel_certificate

theorem initial_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory assumptions) []
    (Translation.sentence initialSentence) := TheoryTransport.sentence source_initial

theorem source_ZF_initial : Derives (Source.SetLanguage.ZF.at 0) initialSentence := source_ZF_replay source_initial

theorem native_initial : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence initialSentence) :=
  native_replay initial_kernel_certificate

theorem comparison_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory assumptions) []
    (Translation.sentence comparisonSentence) := TheoryTransport.sentence source_comparison

theorem source_ZF_comparison : Derives (Source.SetLanguage.ZF.at 0) comparisonSentence := source_ZF_replay source_comparison

theorem native_comparison : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence comparisonSentence) :=
  native_replay comparison_kernel_certificate

theorem trichotomy_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory assumptions) []
    (Translation.sentence trichotomySentence) := TheoryTransport.sentence source_trichotomy

theorem source_ZF_trichotomy : Derives (Source.SetLanguage.ZF.at 0) trichotomySentence := source_ZF_replay source_trichotomy

theorem native_trichotomy : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence trichotomySentence) :=
  native_replay trichotomy_kernel_certificate

theorem subset_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory assumptions) []
    (Translation.sentence subsetSentence) := TheoryTransport.sentence source_subset

theorem source_ZF_subset : Derives (Source.SetLanguage.ZF.at 0) subsetSentence := source_ZF_replay source_subset

theorem native_subset : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence subsetSentence) :=
  native_replay subset_kernel_certificate

theorem asymmetric_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory assumptions) []
    (Translation.sentence asymmetricSentence) := TheoryTransport.sentence source_asymmetric

theorem source_ZF_asymmetric : Derives (Source.SetLanguage.ZF.at 0) asymmetricSentence := source_ZF_replay source_asymmetric

theorem native_asymmetric : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence asymmetricSentence) :=
  native_replay asymmetric_kernel_certificate
end PPAC.Migration.ObjectOrdinalComparison
