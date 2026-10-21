import PPAC.Migration.GraphChoiceToSelector

/-! 图AC推出原选择集AC；背景仅一个明确原Replacement实例，AC作为对象蕴含前件。 -/
namespace PPAC.Migration.ObjectGraphChoiceSelector
open Source SourceAlgebra SourceLogic GraphSyntax ChoiceSyntax

def assumptions : Theory := fun q => q = Source.SetLanguage.replacement GraphRangeSyntax.matrix

def rangeSentence : Source.Sentence := ((functionOn (0 : Fin 2) 1).imp (GraphRangeSyntax.rangeExists 0 1)).close

def selectorSentence : Source.Sentence := ((choiceOn (0 : Fin 2) 1).imp ((disjoint 1).imp (selectorExists 1))).close

def forwardSentence : Source.Sentence := Source.SetLanguage.AC.imp selectorAC

theorem replacement_at (m : Nat) : Derives (assumptions.at m)
    ((Source.SetLanguage.replacement GraphRangeSyntax.matrix).rename Fin.elim0) := .hyp ⟨_, rfl, rfl⟩

theorem source_range : Derives (assumptions.at 0) rangeSentence := by
  apply close_derives
  apply Derives.impI
  exact GraphRangeCollection.exists_range 0 1 (add (replacement_at 2) _) (.hyp (Or.inl rfl))

theorem source_selector : Derives (assumptions.at 0) selectorSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  exact GraphChoiceToSelector.from_graph 0 1 (add (add (replacement_at 2) _) _)
    (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem source_forward : Derives (assumptions.at 0) forwardSentence := by
  apply Derives.impI
  apply Derives.allI
  let Γ0 := Context.add Source.SetLanguage.AC (assumptions.at 0)
  let Γ1 := Context.image Formula.raise Γ0
  have hAC1 : Derives Γ1 (Source.SetLanguage.AC.rename Fin.elim0) := by
    refine Derives.hyp ⟨Source.SetLanguage.AC, Or.inl rfl, ?_⟩
    simp only [Formula.raise, HierarchyLayerSyntax.empty_parameters]
  have hRep1 : Derives Γ1 ((Source.SetLanguage.replacement GraphRangeSyntax.matrix).rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc (add (replacement_at 0) Source.SetLanguage.AC)
  apply Derives.impI
  let M := (familyNonempty (0 : Fin 1)).conj (disjoint 0)
  have hM : Derives (Context.add M Γ1) M := .hyp (Or.inl rfl)
  exact GraphChoiceToSelector.from_AC 0 (add hRep1 M) (add hAC1 M) (.conjL hM) (.conjR hM)

theorem source_ZF_replay {p : Source.Sentence} (h : Derives (assumptions.at 0) p) : Derives (Source.SetLanguage.ZF.at 0) p := by
  refine Derives.weaken ?_ h
  rintro q ⟨s, hs, rfl⟩
  rcases hs with rfl
  exact ⟨_, Source.SetLanguage.IsZFAxiom.replacement GraphRangeSyntax.matrix, rfl⟩

theorem native_replay {p : YesMetaZFC.Logic.FirstOrder.Sentence ℒ}
    (h : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory assumptions) [] p) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] p := by
  apply YesMetaZFC.Logic.FirstOrder.Derives.theory_cut (hFormula := h)
  rintro q ⟨s, hs, rfl⟩
  rcases hs with rfl
  exact ReplacementFromCollection.native_replacement GraphRangeSyntax.matrix

theorem range_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory assumptions) []
    (Translation.sentence rangeSentence) := TheoryTransport.sentence source_range

theorem source_ZF_range : Derives (Source.SetLanguage.ZF.at 0) rangeSentence := source_ZF_replay source_range

theorem native_range : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence rangeSentence) :=
  native_replay range_kernel_certificate

theorem selector_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory assumptions) []
    (Translation.sentence selectorSentence) := TheoryTransport.sentence source_selector

theorem source_ZF_selector : Derives (Source.SetLanguage.ZF.at 0) selectorSentence := source_ZF_replay source_selector

theorem native_selector : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence selectorSentence) :=
  native_replay selector_kernel_certificate

theorem forward_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory assumptions) []
    (Translation.sentence forwardSentence) := TheoryTransport.sentence source_forward

theorem source_ZF_forward : Derives (Source.SetLanguage.ZF.at 0) forwardSentence := source_ZF_replay source_forward

theorem native_forward : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence forwardSentence) :=
  native_replay forward_kernel_certificate
end PPAC.Migration.ObjectGraphChoiceSelector
