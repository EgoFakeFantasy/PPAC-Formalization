import PPAC.Migration.ChoiceLogic

/-! 精确值域在每个不交族成员中的交点存在唯一，所有见证仍为内部集合。 -/
namespace PPAC.Migration.ChoiceSelectorPoints
open Source SourceAlgebra SourceLogic GraphSyntax ChoiceSyntax GraphRangeSyntax

theorem unique_intersection {m} {Γ : Context m} (c f a u y z : Fin m)
    (hr : Derives Γ (range c f a)) (hc : Derives Γ (choiceOn f a)) (hd : Derives Γ (disjoint a))
    (hu : Derives Γ (.mem u a)) (hy : Derives Γ (edge f u y)) (hz : Derives Γ (chosen c u z)) : Derives Γ (.equal z y) := by
  have hi := Derives.impE (.conjL (range_at c f a z hr)) (.conjL hz)
  let V := (Formula.mem (Fin.last m) a.castSucc).conj (edge f.castSucc (Fin.last m) z.castSucc)
  let Ξ := Context.add V (Context.image Formula.raise Γ)
  change Derives Γ (.ex V) at hi
  apply Derives.exE (p := V) hi
  have hcV : Derives Ξ (choiceOn f.castSucc a.castSucc) := by
    simpa only [Formula.raise, choiceOn_rename] using under hc V
  have hdV : Derives Ξ (disjoint a.castSucc) := by
    simpa only [Formula.raise, disjoint_rename] using under hd V
  have huV : Derives Ξ (.mem u.castSucc a.castSucc) := under hu V
  have hyV : Derives Ξ (edge f.castSucc u.castSucc y.castSucc) := by
    simpa only [Formula.raise, edge_rename] using under hy V
  have hzV : Derives Ξ (.mem z.castSucc u.castSucc) := under (.conjR hz) V
  have hV : Derives Ξ V := .hyp (Or.inl rfl)
  have hzIn := ChoiceLogic.edge_member f.castSucc a.castSucc (Fin.last m) z.castSucc hcV (.conjL hV) (.conjR hV)
  have he := ChoiceLogic.intersecting_equal a.castSucc u.castSucc (Fin.last m) z.castSucc hdV huV (.conjL hV) hzV hzIn
  have hzEdge := IterationValues.edge_subst_input f.castSucc (Fin.last m) u.castSucc z.castSucc (eq_symm he) (.conjR hV)
  exact ChoiceLogic.unique_on_input f.castSucc a.castSucc u.castSucc z.castSucc y.castSucc (.conjL hcV) huV hzEdge hyV

theorem selected_point {m} {Γ : Context m} (c f a u y : Fin m)
    (hr : Derives Γ (range c f a)) (hc : Derives Γ (choiceOn f a)) (hd : Derives Γ (disjoint a))
    (hu : Derives Γ (.mem u a)) (hy : Derives Γ (edge f u y)) (hm : Derives Γ (.mem y u)) : Derives Γ (selected c u y) := by
  have hcy := Derives.impE (.conjR (range_at c f a y hr)) (intro_image f a u y hu hy)
  apply Derives.conjI (.conjI hcy hm)
  apply Derives.allI
  let Δ := Context.image Formula.raise Γ
  have hr' : Derives Δ (range c.castSucc f.castSucc a.castSucc) := by
    simpa only [Formula.raise, range_rename] using Derives.rename Fin.castSucc hr
  have hc' : Derives Δ (choiceOn f.castSucc a.castSucc) := by
    simpa only [Formula.raise, choiceOn_rename] using Derives.rename Fin.castSucc hc
  have hd' : Derives Δ (disjoint a.castSucc) := by
    simpa only [Formula.raise, disjoint_rename] using Derives.rename Fin.castSucc hd
  have hu' : Derives Δ (.mem u.castSucc a.castSucc) := Derives.rename Fin.castSucc hu
  have hy' : Derives Δ (edge f.castSucc u.castSucc y.castSucc) := by
    simpa only [Formula.raise, edge_rename] using Derives.rename Fin.castSucc hy
  apply Derives.impI
  exact unique_intersection c.castSucc f.castSucc a.castSucc u.castSucc y.castSucc (Fin.last m)
    (add hr' _) (add hc' _) (add hd' _) (add hu' _) (add hy' _) (.hyp (Or.inl rfl))

theorem exists_selected {m} {Γ : Context m} (c f a u : Fin m)
    (hr : Derives Γ (range c f a)) (hc : Derives Γ (choiceOn f a)) (hd : Derives Γ (disjoint a))
    (hu : Derives Γ (.mem u a)) : Derives Γ (selectedExists c u) := by
  have hy := Derives.impE (choice_at f a u hc) hu
  let Y := (edge f.castSucc u.castSucc (Fin.last m)).conj (.mem (Fin.last m) u.castSucc)
  let Ξ := Context.add Y (Context.image Formula.raise Γ)
  change Derives Γ (.ex Y) at hy
  apply Derives.exE (p := Y) hy
  have hrY : Derives Ξ (range c.castSucc f.castSucc a.castSucc) := by
    simpa only [Formula.raise, range_rename] using under hr Y
  have hcY : Derives Ξ (choiceOn f.castSucc a.castSucc) := by
    simpa only [Formula.raise, choiceOn_rename] using under hc Y
  have hdY : Derives Ξ (disjoint a.castSucc) := by
    simpa only [Formula.raise, disjoint_rename] using under hd Y
  have huY : Derives Ξ (.mem u.castSucc a.castSucc) := under hu Y
  have hY : Derives Ξ Y := .hyp (Or.inl rfl)
  have hs := selected_point c.castSucc f.castSucc a.castSucc u.castSucc (Fin.last m) hrY hcY hdY huY (.conjL hY) (.conjR hY)
  have hout : Derives Ξ (selectedExists c.castSucc u.castSucc) := by
    apply Derives.exI (Fin.last m)
    simp only [Formula.instantiate, selected_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
    exact hs
  simpa only [Formula.raise, selectedExists_rename] using hout
end PPAC.Migration.ChoiceSelectorPoints
