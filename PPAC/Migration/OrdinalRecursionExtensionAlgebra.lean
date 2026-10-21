import PPAC.Migration.GraphInsertElimination
import PPAC.Migration.OrdinalRecursionTotal

/-! 后继扩展的旧历史复合和新位置实际历史；不假定递归方程自动保持。 -/
namespace PPAC.Migration.OrdinalRecursionExtensionAlgebra
open Source SourceAlgebra SourceLogic PairSyntax GraphSyntax RestrictionSyntax InsertSyntax OrdinalSyntax OrdinalRecursionSyntax
open ReplacementPredicates (paramsUp)

theorem operator_subst_output {n m} {Γ : Context m} (p : Formula (n+3)) (ρ : Fin n → Fin m) (x h u v : Fin m)
    (he : Derives Γ (.equal u v)) (hu : Derives Γ (operator p ρ x h u)) : Derives Γ (operator p ρ x h v) := by
  have hi : Derives Γ ((operator p (paramsUp ρ) x.castSucc h.castSucc (Fin.last m)).instantiate u) := by
    simpa only [Formula.instantiate, operator_rename, paramsUp, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hu
  have hr := Derives.eqSubst (operator p (paramsUp ρ) x.castSucc h.castSucc (Fin.last m)) he hi
  simpa only [Formula.instantiate, operator_rename, paramsUp, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hr

theorem history_subst_index {n m} {Γ : Context m} (p : Formula (n+3)) (ρ : Fin n → Fin m) (g x z y : Fin m)
    (he : Derives Γ (.equal x z)) (hx : Derives Γ (history p ρ g x y)) : Derives Γ (history p ρ g z y) := by
  have hi : Derives Γ ((history p (paramsUp ρ) g.castSucc (Fin.last m) y.castSucc).instantiate x) := by
    simpa only [Formula.instantiate, history_rename, paramsUp, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hx
  have hr := Derives.eqSubst (history p (paramsUp ρ) g.castSucc (Fin.last m) y.castSucc) he hi
  simpa only [Formula.instantiate, history_rename, paramsUp, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hr

theorem lift_history {n m} {Γ : Context m} (p : Formula (n+3)) (ρ : Fin n → Fin m) (g f d x y : Fin m)
    (hs : Derives Γ (subset x d)) (hr : Derives Γ (restrict f g d))
    (hh : Derives Γ (history p ρ f x y)) : Derives Γ (history p ρ g x y) := by
  let H := (restrict (Fin.last m) f.castSucc x.castSucc).conj
    (operator p (paramsUp ρ) x.castSucc (Fin.last m) y.castSucc)
  let Ξ := Context.add H (Context.image Formula.raise Γ)
  change Derives Γ (.ex H) at hh
  apply Derives.exE (p := H) hh
  have hs' : Derives Ξ (subset x.castSucc d.castSucc) := by
    simpa only [Formula.raise, subset_rename] using under hs H
  have hr' : Derives Ξ (restrict f.castSucc g.castSucc d.castSucc) := by
    simpa only [Formula.raise, restrict_rename] using under hr H
  have hH : Derives Ξ H := .hyp (Or.inl rfl)
  have hnew := RestrictionAlgebra.compose (Fin.last m) f.castSucc g.castSucc d.castSucc x.castSucc hs' hr' (.conjL hH)
  simpa only [Formula.raise, history_rename] using history_intro p (paramsUp ρ) g.castSucc x.castSucc (Fin.last m) y.castSucc hnew (.conjR hH)

theorem old_history {n m} {Γ : Context m} (p : Formula (n+3)) (ρ : Fin n → Fin m) (g f d x y : Fin m)
    (hd : Derives Γ (ordinal d)) (hf : Derives Γ (recursor p ρ f d))
    (hr : Derives Γ (restrict f g d)) (hx : Derives Γ (.mem x d)) (hy : Derives Γ (edge g x y)) :
    Derives Γ (history p ρ g x y) := by
  have hxy := RestrictionEdges.restricted_edge f g d x y hr hy hx
  have hh := Derives.impE (Derives.impE (equations_at p ρ f d x y (.conjR hf)) hx) hxy
  exact lift_history p ρ g f d x y (OrdinalTransitivity.subset_of_member d x (.conjL hd) hx) hr hh

theorem new_history {n m} {Γ : Context m} (p : Formula (n+3)) (ρ : Fin n → Fin m) (g f d c y v : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hd : Derives Γ (ordinal d)) (hf : Derives Γ (recursor p ρ f d))
    (hi : Derives Γ (insert g f c)) (hc : Derives Γ (ordered c d y))
    (hr : Derives Γ (restrict f g d)) (hy : Derives Γ (operator p ρ d f y))
    (hv : Derives Γ (edge g d v)) : Derives Γ (history p ρ g d v) := by
  have hn := OrdinalEmpty.no_self d (.conjL (.conjR hd))
  have hval := GraphInsertValues.new_value g f d c d y he (.conjL hf) hn hi hc
  have hveq := Derives.impE (GraphSyntax.unique_at g d y v hval) hv
  exact history_intro p ρ g d f v hr (operator_subst_output p ρ d f y v (eq_symm hveq) hy)

theorem point_history {n m} {Γ : Context m} (p : Formula (n+3)) (ρ : Fin n → Fin m) (g s c f d y x v : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hd : Derives Γ (ordinal d)) (hf : Derives Γ (recursor p ρ f d))
    (hw : Derives Γ (GraphInsertSyntax.witness g s c f d d y))
    (hy : Derives Γ (operator p ρ d f y)) (hx : Derives Γ (.mem x s)) (hv : Derives Γ (edge g x v)) :
    Derives Γ (history p ρ g x v) := by
  have hi := Derives.conjL (Derives.conjR (Derives.conjR hw))
  have hc := Derives.conjL hw
  have hn := OrdinalEmpty.no_self d (.conjL (.conjR hd))
  have hr := GraphInsertRestriction.old_restriction g f d c d y he (.conjL hf) hn hi hc
  have hcases := InsertLogic.member_cases s d d x (.conjL (.conjR hw)) hx
  apply Derives.disjE hcases
  · exact old_history p ρ g f d x v (add hd _) (add hf _) (add hr _) (.hyp (Or.inl rfl)) (add hv _)
  · let Ξ := Context.add (.equal x d) Γ
    have hxd : Derives Ξ (.equal x d) := .hyp (Or.inl rfl)
    have hgv := IterationValues.edge_subst_input g x d v hxd (add hv _)
    have hh := new_history p ρ g f d c y v (add he _) (add hd _) (add hf _) (add hi _) (add hc _) (add hr _) (add hy _) hgv
    exact history_subst_index p ρ g d x v (eq_symm hxd) hh
end PPAC.Migration.OrdinalRecursionExtensionAlgebra
