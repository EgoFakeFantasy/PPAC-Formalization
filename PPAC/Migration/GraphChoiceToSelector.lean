import PPAC.Migration.ChoiceSelectorPoints

/-! 实际选择图的精确输出集合满足原不交族选择集公式。 -/
namespace PPAC.Migration.GraphChoiceToSelector
open Source SourceAlgebra SourceLogic GraphSyntax ChoiceSyntax GraphRangeSyntax

theorem selector_of_range {m} {Γ : Context m} (c f a : Fin m)
    (hr : Derives Γ (range c f a)) (hc : Derives Γ (choiceOn f a)) (hd : Derives Γ (disjoint a)) :
    Derives Γ (selector c a) := by
  apply Derives.allI
  let Δ := Context.image Formula.raise Γ
  have hr' : Derives Δ (range c.castSucc f.castSucc a.castSucc) := by
    simpa only [Formula.raise, range_rename] using Derives.rename Fin.castSucc hr
  have hc' : Derives Δ (choiceOn f.castSucc a.castSucc) := by
    simpa only [Formula.raise, choiceOn_rename] using Derives.rename Fin.castSucc hc
  have hd' : Derives Δ (disjoint a.castSucc) := by
    simpa only [Formula.raise, disjoint_rename] using Derives.rename Fin.castSucc hd
  apply Derives.impI
  exact ChoiceSelectorPoints.exists_selected c.castSucc f.castSucc a.castSucc (Fin.last m)
    (add hr' _) (add hc' _) (add hd' _) (.hyp (Or.inl rfl))

theorem from_graph {m} {Γ : Context m} (f a : Fin m)
    (hRep : Derives Γ ((Source.SetLanguage.replacement GraphRangeSyntax.matrix).rename Fin.elim0))
    (hc : Derives Γ (choiceOn f a)) (hd : Derives Γ (disjoint a)) : Derives Γ (selectorExists a) := by
  have hx := GraphRangeCollection.exists_range f a hRep (.conjL hc)
  let C := range (Fin.last m) f.castSucc a.castSucc
  let Ξ := Context.add C (Context.image Formula.raise Γ)
  change Derives Γ (.ex C) at hx
  apply Derives.exE (p := C) hx
  have hcC : Derives Ξ (choiceOn f.castSucc a.castSucc) := by
    simpa only [Formula.raise, choiceOn_rename] using under hc C
  have hdC : Derives Ξ (disjoint a.castSucc) := by
    simpa only [Formula.raise, disjoint_rename] using under hd C
  have hC : Derives Ξ C := .hyp (Or.inl rfl)
  have hs := selector_of_range (Fin.last m) f.castSucc a.castSucc hC hcC hdC
  have hout : Derives Ξ (selectorExists a.castSucc) := by
    apply Derives.exI (Fin.last m)
    simp only [Formula.instantiate, selector_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
    exact hs
  simpa only [Formula.raise, selectorExists_rename] using hout

theorem from_AC {m} {Γ : Context m} (a : Fin m)
    (hRep : Derives Γ ((Source.SetLanguage.replacement GraphRangeSyntax.matrix).rename Fin.elim0))
    (hAC : Derives Γ (Source.SetLanguage.AC.rename Fin.elim0))
    (ha : Derives Γ (familyNonempty a)) (hd : Derives Γ (disjoint a)) : Derives Γ (selectorExists a) := by
  have hf := Derives.impE (graph_ac_at a hAC) ha
  let F := choiceOn (Fin.last m) a.castSucc
  let Ξ := Context.add F (Context.image Formula.raise Γ)
  change Derives Γ (.ex F) at hf
  apply Derives.exE (p := F) hf
  have hRepF : Derives Ξ ((Source.SetLanguage.replacement GraphRangeSyntax.matrix).rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hRep F
  have hdF : Derives Ξ (disjoint a.castSucc) := by
    simpa only [Formula.raise, disjoint_rename] using under hd F
  have hF : Derives Ξ F := .hyp (Or.inl rfl)
  simpa only [Formula.raise, selectorExists_rename] using from_graph (Fin.last m) a.castSucc hRepF hF hdF
end PPAC.Migration.GraphChoiceToSelector
