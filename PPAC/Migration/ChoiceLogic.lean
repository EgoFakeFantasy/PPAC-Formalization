import PPAC.Migration.GraphRangeCollection

/-! 完整选择图的任意域内输出确在对应成员中；相交的不交族成员必须相等。 -/
namespace PPAC.Migration.ChoiceLogic
open Source SourceAlgebra SourceLogic GraphSyntax ChoiceSyntax

theorem unique_on_input {m} {Γ : Context m} (f a x y z : Fin m)
    (hf : Derives Γ (functionOn f a)) (hx : Derives Γ (.mem x a))
    (hy : Derives Γ (edge f x y)) (hz : Derives Γ (edge f x z)) : Derives Γ (.equal y z) := by
  have hv := Derives.impE (total_at f a x (.conjR hf)) hx
  let V := valueAt f.castSucc x.castSucc (Fin.last m)
  let Ξ := Context.add V (Context.image Formula.raise Γ)
  change Derives Γ (.ex V) at hv
  apply Derives.exE (p := V) hv
  have hyV : Derives Ξ (edge f.castSucc x.castSucc y.castSucc) := by
    simpa only [Formula.raise, edge_rename] using under hy V
  have hzV : Derives Ξ (edge f.castSucc x.castSucc z.castSucc) := by
    simpa only [Formula.raise, edge_rename] using under hz V
  have hV : Derives Ξ V := .hyp (Or.inl rfl)
  exact eq_trans (.impE (unique_at f.castSucc x.castSucc (Fin.last m) y.castSucc hV) hyV)
    (eq_symm (.impE (unique_at f.castSucc x.castSucc (Fin.last m) z.castSucc hV) hzV))

theorem edge_member {m} {Γ : Context m} (f a x y : Fin m)
    (hc : Derives Γ (choiceOn f a)) (hx : Derives Γ (.mem x a)) (hy : Derives Γ (edge f x y)) : Derives Γ (.mem y x) := by
  have hv := Derives.impE (choice_at f a x hc) hx
  let V := (edge f.castSucc x.castSucc (Fin.last m)).conj (.mem (Fin.last m) x.castSucc)
  let Ξ := Context.add V (Context.image Formula.raise Γ)
  change Derives Γ (.ex V) at hv
  apply Derives.exE (p := V) hv
  have hcV : Derives Ξ (choiceOn f.castSucc a.castSucc) := by
    simpa only [Formula.raise, choiceOn_rename] using under hc V
  have hxV : Derives Ξ (.mem x.castSucc a.castSucc) := under hx V
  have hyV : Derives Ξ (edge f.castSucc x.castSucc y.castSucc) := by
    simpa only [Formula.raise, edge_rename] using under hy V
  have hV : Derives Ξ V := .hyp (Or.inl rfl)
  have he := unique_on_input f.castSucc a.castSucc x.castSucc y.castSucc (Fin.last m) (.conjL hcV) hxV hyV (.conjL hV)
  exact mem_subst (eq_symm he) (.conjR hV)

theorem intro_intersection {m} {Γ : Context m} (u v z : Fin m)
    (hu : Derives Γ (.mem z u)) (hv : Derives Γ (.mem z v)) : Derives Γ (intersection u v) := by
  apply Derives.exI z
  simp only [Formula.instantiate, Formula.rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI hu hv

theorem intersecting_equal {m} {Γ : Context m} (a u v z : Fin m)
    (hd : Derives Γ (disjoint a)) (hu : Derives Γ (.mem u a)) (hv : Derives Γ (.mem v a))
    (hzu : Derives Γ (.mem z u)) (hzv : Derives Γ (.mem z v)) : Derives Γ (.equal u v) := by
  apply Derives.classical
  have hn := Derives.impE (Derives.impE (Derives.impE (add (disjoint_at a u v hd) _) (add hu _)) (add hv _)) (.hyp (Or.inl rfl))
  exact .impE hn (intro_intersection u v z (add hzu _) (add hzv _))
end PPAC.Migration.ChoiceLogic
