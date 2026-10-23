import PPAC.Migration.Internal.LookupTableState

/-! 真实Separation集合的任意二字段状态查询，精确等于合法运行时参数及程序分支。 -/
namespace PPAC.Migration.Internal.LookupTableOperatorMembership
open Source SourceAlgebra SourceLogic OmegaSyntax LookupTableProgramSyntax LookupTableOperatorSyntax
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem row_at_state {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n h p i y : Fin m)
    (hw : Derives Γ (omega w)) (hp : Derives Γ (state w i y p)) (hr : Derives Γ (row w n h p)) :
    Derives Γ (run w h n i y) := by
  let B := rowBody w n h p
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply SyntaxRenameBinders.eliminate_2 B _ hr
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ B
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw B)
  have hp2 : Derives Δ (state w.castSucc.castSucc i.castSucc.castSucc y.castSucc.castSucc p.castSucc.castSucc) := of_eq (by simp only [Formula.raise, state_rename]) (SyntaxRenameBinders.under_2 hp B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hEq := LookupTableState.same_fields hZ2 w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) i.castSucc.castSucc y.castSucc.castSucc p.castSucc.castSucc hw2 (.conjL hB) hp2
  have hRun := LookupTableState.run_subst_index w.castSucc.castSucc h.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) i.castSucc.castSucc (.conjL hEq) (.conjR hB)
  exact of_eq (by simp only [Formula.raise, run_rename])
    (LookupTableState.run_subst_output w.castSucc.castSucc h.castSucc.castSucc n.castSucc.castSucc i.castSucc.castSucc (Fin.last (m+1)) y.castSucc.castSucc (.conjR hEq) hRun)

theorem member_at_state {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n h v p i y : Fin m)
    (hw : Derives Γ (omega w)) (hv : Derives Γ (value w n h v)) (hp : Derives Γ (state w i y p)) :
    Derives Γ ((Formula.mem p v).iff (run w h n i y)) := by
  have hh := value_at w n h v p hv
  apply Derives.conjI
  · apply Derives.impI
    exact row_at_state (ZFContext.add hZ _) w n h p i y (add hw _) (add hp _)
      (.conjR (.impE (add (.conjL hh) _) (.hyp (Or.inl rfl))))
  · apply Derives.impI
    exact .impE (add (.conjR hh) _) (.conjI (add (.conjL (.conjR hp)) _)
      (intro_row w n h p i y (add hp _) (.hyp (Or.inl rfl))))

theorem contains_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n h v i y : Fin m)
    (hw : Derives Γ (omega w)) (hv : Derives Γ (value w n h v)) :
    Derives Γ ((contains w v i y).iff ((legal w i y).conj (run w h n i y))) := by
  apply Derives.conjI
  · apply Derives.impI
    let C := contains w v i y
    let P := (Formula.mem (Fin.last m) v.castSucc).conj (state w.castSucc i.castSucc y.castSucc (Fin.last m))
    let Δ := Context.add P (Context.image Formula.raise (Context.add C Γ))
    apply Derives.exE (p := P) (.hyp (Or.inl rfl))
    have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under (add hw C) P)
    have hv1 : Derives Δ (value w.castSucc n.castSucc h.castSucc v.castSucc) := of_eq (value_rename w n h v Fin.castSucc) (under (add hv C) P)
    have hP : Derives Δ P := .hyp (Or.inl rfl)
    have hRun := Derives.impE (.conjL (member_at_state (ZFContext.under (ZFContext.add hZ C) P) w.castSucc n.castSucc h.castSucc v.castSucc (Fin.last m) i.castSucc y.castSucc hw1 hv1 (.conjR hP))) (.conjL hP)
    exact of_eq (by simp only [Formula.raise, Formula.rename, legal_rename, run_rename]) (.conjI (.conjL (.conjR hP)) hRun)
  · apply Derives.impI
    let C := (legal w i y).conj (run w h n i y)
    let P := state w.castSucc i.castSucc y.castSucc (Fin.last m)
    let Δ := Context.add P (Context.image Formula.raise (Context.add C Γ))
    have hC : Derives (Context.add C Γ) C := .hyp (Or.inl rfl)
    apply Derives.exE (p := P) (LookupTableState.exists_state (ZFContext.add hZ C) w i y (add hw C) (.conjL hC))
    have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under (add hw C) P)
    have hv1 : Derives Δ (value w.castSucc n.castSucc h.castSucc v.castSucc) := of_eq (value_rename w n h v Fin.castSucc) (under (add hv C) P)
    have hr1 : Derives Δ (run w.castSucc h.castSucc n.castSucc i.castSucc y.castSucc) := of_eq (run_rename w h n i y Fin.castSucc) (under (.conjR hC) P)
    have hP : Derives Δ P := .hyp (Or.inl rfl)
    have hMem := Derives.impE (.conjR (member_at_state (ZFContext.under (ZFContext.add hZ C) P) w.castSucc n.castSucc h.castSucc v.castSucc (Fin.last m) i.castSucc y.castSucc hw1 hv1 hP)) hr1
    exact of_eq (contains_rename w v i y Fin.castSucc).symm (intro_contains w.castSucc v.castSucc i.castSucc y.castSucc (Fin.last m) hMem hP)

end PPAC.Migration.Internal.LookupTableOperatorMembership
