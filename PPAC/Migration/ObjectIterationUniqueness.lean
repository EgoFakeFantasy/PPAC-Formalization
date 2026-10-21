import PPAC.Migration.IterationCompatibility

/-! 给定真实对象迭代轨迹的共同值、相容性和唯一性；不假定或宣称轨迹存在。 -/
namespace PPAC.Migration.ObjectIterationUniqueness
open Source SourceAlgebra SourceLogic OmegaSyntax OmegaStructureSyntax IterationSyntax

def assumptions : Theory := fun q => q = Source.SetLanguage.extensionality ∨ q = Source.SetLanguage.separation agreementMatrix

def commonSentence : Source.Sentence := ((omega (6 : Fin 7)).imp ((empty 4).imp
  ((track 0 2 4 5).imp ((track 1 3 4 5).imp ((transitive 2).imp ((transitive 3).imp (allCommon 0 1 2 3 6))))))).close

def compatibleSentence : Source.Sentence := ((omega (6 : Fin 7)).imp ((empty 4).imp
  ((track 0 2 4 5).imp ((track 1 3 4 5).imp ((transitive 2).imp ((transitive 3).imp
    ((RestrictionSyntax.subset 2 6).imp (GraphFamilySyntax.agrees 0 1)))))))).close

def uniqueSentence : Source.Sentence := ((omega (5 : Fin 6)).imp ((empty 3).imp
  ((track 0 2 3 4).imp ((track 1 2 3 4).imp ((transitive 2).imp
    ((RestrictionSyntax.subset 2 5).imp (.equal 0 1))))))).close

theorem source_common : Derives (assumptions.at 0) commonSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  have he : Derives (assumptions.at 7) (Source.SetLanguage.extensionality.rename Fin.elim0) := .hyp ⟨_, Or.inl rfl, rfl⟩
  have hs : Derives (assumptions.at 7) ((Source.SetLanguage.separation agreementMatrix).rename Fin.elim0) := .hyp ⟨_, Or.inr rfl, rfl⟩
  exact IterationInduction.all_common 0 1 2 3 4 5 6
    (add (add (add (add (add (add he _) _) _) _) _) _) (add (add (add (add (add (add hs _) _) _) _) _) _)
    (.hyp (by simp [Context.add])) (.hyp (by simp [Context.add]))
    (.hyp (by simp [Context.add])) (.hyp (by simp [Context.add]))
    (.hyp (by simp [Context.add])) (.hyp (by simp [Context.add]))

theorem source_compatible : Derives (assumptions.at 0) compatibleSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  have he : Derives (assumptions.at 7) (Source.SetLanguage.extensionality.rename Fin.elim0) := .hyp ⟨_, Or.inl rfl, rfl⟩
  have hs : Derives (assumptions.at 7) ((Source.SetLanguage.separation agreementMatrix).rename Fin.elim0) := .hyp ⟨_, Or.inr rfl, rfl⟩
  exact IterationCompatibility.compatible 0 1 2 3 4 5 6
    (add (add (add (add (add (add (add he _) _) _) _) _) _) _) (add (add (add (add (add (add (add hs _) _) _) _) _) _) _)
    (.hyp (by simp [Context.add])) (.hyp (by simp [Context.add]))
    (.hyp (by simp [Context.add])) (.hyp (by simp [Context.add]))
    (.hyp (by simp [Context.add])) (.hyp (by simp [Context.add])) (.hyp (by simp [Context.add]))

theorem source_unique : Derives (assumptions.at 0) uniqueSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  have he : Derives (assumptions.at 6) (Source.SetLanguage.extensionality.rename Fin.elim0) := .hyp ⟨_, Or.inl rfl, rfl⟩
  have hs : Derives (assumptions.at 6) ((Source.SetLanguage.separation agreementMatrix).rename Fin.elim0) := .hyp ⟨_, Or.inr rfl, rfl⟩
  exact IterationCompatibility.unique_same_domain 0 1 2 3 4 5
    (add (add (add (add (add (add he _) _) _) _) _) _) (add (add (add (add (add (add hs _) _) _) _) _) _)
    (.hyp (by simp [Context.add])) (.hyp (by simp [Context.add]))
    (.hyp (by simp [Context.add])) (.hyp (by simp [Context.add]))
    (.hyp (by simp [Context.add])) (.hyp (by simp [Context.add]))

theorem source_ZF_replay {p : Source.Sentence} (h : Derives (assumptions.at 0) p) : Derives (Source.SetLanguage.ZF.at 0) p := by
  refine Derives.weaken ?_ h
  rintro q ⟨_, hr, rfl⟩
  rcases hr with rfl | rfl
  · exact ⟨_, Source.SetLanguage.IsZFAxiom.extensionality, rfl⟩
  · exact ⟨_, Source.SetLanguage.IsZFAxiom.separation agreementMatrix, rfl⟩

theorem native_replay {free : Syntax.Ctx}
    {Γ : YesMetaZFC.Logic.FirstOrder.Context YesMetaZFC.SetTheory.PureSetLanguage free} {p : Syntax.Fm [] free}
    (h : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory assumptions) Γ p) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF Γ p := by
  apply YesMetaZFC.Logic.FirstOrder.Derives.theory_cut (hFormula := h)
  rintro q ⟨_, hr, rfl⟩
  rcases hr with rfl | rfl
  · exact ZFEquivalence.source_extensionality
  · exact SeparationSyntax.source_separation agreementMatrix

theorem common_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory assumptions) []
    (Translation.sentence commonSentence) := TheoryTransport.sentence source_common

theorem source_ZF_common : Derives (Source.SetLanguage.ZF.at 0) commonSentence := source_ZF_replay source_common

theorem native_common : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence commonSentence) :=
  native_replay common_kernel_certificate

theorem compatible_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory assumptions) []
    (Translation.sentence compatibleSentence) := TheoryTransport.sentence source_compatible

theorem source_ZF_compatible : Derives (Source.SetLanguage.ZF.at 0) compatibleSentence := source_ZF_replay source_compatible

theorem native_compatible : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence compatibleSentence) :=
  native_replay compatible_kernel_certificate

theorem unique_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory assumptions) []
    (Translation.sentence uniqueSentence) := TheoryTransport.sentence source_unique

theorem source_ZF_unique : Derives (Source.SetLanguage.ZF.at 0) uniqueSentence := source_ZF_replay source_unique

theorem native_unique : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence uniqueSentence) :=
  native_replay unique_kernel_certificate
end PPAC.Migration.ObjectIterationUniqueness
