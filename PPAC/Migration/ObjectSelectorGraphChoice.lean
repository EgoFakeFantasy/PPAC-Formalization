import PPAC.Migration.SelectorChoiceToGraph

/-! 五个明确原公理推出标签族、反向AC；AC仅作为蕴含前件。 -/
namespace PPAC.Migration.ObjectSelectorGraphChoice
open Source SourceAlgebra SourceLogic ChoiceSyntax

def assumptions : Theory := fun q => q = Source.SetLanguage.extensionality ∨ q = Source.SetLanguage.pairing ∨
  q = Source.SetLanguage.replacement TaggedRowSyntax.pairMatrix ∨
  q = Source.SetLanguage.replacement TaggedFamilySyntax.matrix ∨
  q = Source.SetLanguage.replacement SelectedPairSyntax.matrix

def familySentence : Source.Sentence := ((familyNonempty (0 : Fin 1)).imp (TaggedFamilySyntax.admissibleExists 0)).close
def reverseSentence : Source.Sentence := selectorAC.imp Source.SetLanguage.AC

theorem evidence (m : Nat) : TaggedFamilyContext.Evidence (assumptions.at m) :=
  ⟨.hyp ⟨_, Or.inl rfl, rfl⟩,
   .hyp ⟨_, Or.inr (Or.inl rfl), rfl⟩,
   .hyp ⟨_, Or.inr (Or.inr (Or.inl rfl)), rfl⟩,
   .hyp ⟨_, Or.inr (Or.inr (Or.inr (Or.inl rfl))), rfl⟩⟩

theorem replacement_at (m : Nat) : Derives (assumptions.at m)
    ((Source.SetLanguage.replacement SelectedPairSyntax.matrix).rename Fin.elim0) :=
  .hyp ⟨_, Or.inr (Or.inr (Or.inr (Or.inr rfl))), rfl⟩

theorem source_family : Derives (assumptions.at 0) familySentence := by
  apply close_derives
  apply Derives.impI
  exact TaggedFamilyLogic.exists_admissible (TaggedFamilyContext.add (evidence 1) _) 0 (.hyp (Or.inl rfl))

theorem source_reverse : Derives (assumptions.at 0) reverseSentence := by
  apply Derives.impI
  rw [graphAC_original]
  apply Derives.allI
  let Γ0 := Context.add selectorAC (assumptions.at 0)
  let Γ1 := Context.image Formula.raise Γ0
  have hAC1 : Derives Γ1 (selectorAC.rename Fin.elim0) := by
    refine Derives.hyp ⟨selectorAC, Or.inl rfl, ?_⟩
    simp only [Formula.raise, HierarchyLayerSyntax.empty_parameters]
  have hA1 : TaggedFamilyContext.Evidence Γ1 := TaggedFamilyContext.rename (TaggedFamilyContext.add (evidence 0) selectorAC) Fin.castSucc
  have hRep1 : Derives Γ1 ((Source.SetLanguage.replacement SelectedPairSyntax.matrix).rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc (add (replacement_at 0) selectorAC)
  apply Derives.impI
  exact SelectorChoiceToGraph.from_AC (TaggedFamilyContext.add hA1 _) 0 (add hRep1 _) (add hAC1 _) (.hyp (Or.inl rfl))

theorem source_ZF_replay {p : Source.Sentence} (h : Derives (assumptions.at 0) p) : Derives (Source.SetLanguage.ZF.at 0) p := by
  refine Derives.weaken ?_ h
  rintro q ⟨s, hs, rfl⟩
  rcases hs with rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, Source.SetLanguage.IsZFAxiom.extensionality, rfl⟩
  · exact ⟨_, Source.SetLanguage.IsZFAxiom.pairing, rfl⟩
  · exact ⟨_, Source.SetLanguage.IsZFAxiom.replacement TaggedRowSyntax.pairMatrix, rfl⟩
  · exact ⟨_, Source.SetLanguage.IsZFAxiom.replacement TaggedFamilySyntax.matrix, rfl⟩
  · exact ⟨_, Source.SetLanguage.IsZFAxiom.replacement SelectedPairSyntax.matrix, rfl⟩

theorem native_replay {p : YesMetaZFC.Logic.FirstOrder.Sentence ℒ}
    (h : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory assumptions) [] p) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] p := by
  apply YesMetaZFC.Logic.FirstOrder.Derives.theory_cut (hFormula := h)
  rintro q ⟨s, hs, rfl⟩
  rcases hs with rfl | rfl | rfl | rfl | rfl
  · exact ZFEquivalence.source_extensionality
  · exact ZFEquivalence.source_pairing
  · exact ReplacementFromCollection.native_replacement TaggedRowSyntax.pairMatrix
  · exact ReplacementFromCollection.native_replacement TaggedFamilySyntax.matrix
  · exact ReplacementFromCollection.native_replacement SelectedPairSyntax.matrix

theorem family_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory assumptions) []
    (Translation.sentence familySentence) := TheoryTransport.sentence source_family

theorem source_ZF_family : Derives (Source.SetLanguage.ZF.at 0) familySentence := source_ZF_replay source_family

theorem native_family : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence familySentence) :=
  native_replay family_kernel_certificate

theorem reverse_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory assumptions) []
    (Translation.sentence reverseSentence) := TheoryTransport.sentence source_reverse

theorem source_ZF_reverse : Derives (Source.SetLanguage.ZF.at 0) reverseSentence := source_ZF_replay source_reverse

theorem native_reverse : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence reverseSentence) :=
  native_replay reverse_kernel_certificate

theorem source_ZF_equivalence : Derives (Source.SetLanguage.ZF.at 0) (Source.SetLanguage.AC.iff selectorAC) :=
  .conjI ObjectGraphChoiceSelector.source_ZF_forward source_ZF_reverse

theorem equivalence_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (Source.SetLanguage.AC.iff selectorAC)) := TheoryTransport.sentence source_ZF_equivalence
end PPAC.Migration.ObjectSelectorGraphChoice
