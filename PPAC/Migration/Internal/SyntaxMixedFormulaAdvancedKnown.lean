import PPAC.Migration.Internal.SyntaxMixedFormulaBinderAlign

/-! 真正的四见证混合量词查询在任意实际binder提升上识别同一子查询；两份环境码均对齐。 -/
namespace PPAC.Migration.Internal.SyntaxMixedFormulaAdvancedKnown
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxMixedFormulaQuerySyntax
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem subst_bound_code {m} {Γ : Context m} (w h x r s a b c d q V : Fin m)
    (he : Derives Γ (.equal r V)) (hl : Derives Γ (read w h x r s a b c d q)) : Derives Γ (read w h x V s a b c d q) := by
  let P := read w.castSucc h.castSucc x.castSucc (Fin.last m) s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc q.castSucc
  have e0 : P.instantiate r = read w h x r s a b c d q := by
    simp only [P, Formula.instantiate, read_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have e1 : P.instantiate V = read w h x V s a b c d q := by
    simp only [P, Formula.instantiate, read_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq e1 (Derives.eqSubst P he (of_eq e0.symm hl))

theorem subst_free_code {m} {Γ : Context m} (w h x r s a b c d q V : Fin m)
    (he : Derives Γ (.equal s V)) (hl : Derives Γ (read w h x r s a b c d q)) : Derives Γ (read w h x r V a b c d q) := by
  let P := read w.castSucc h.castSucc x.castSucc r.castSucc (Fin.last m) a.castSucc b.castSucc c.castSucc d.castSucc q.castSucc
  have e0 : P.instantiate s = read w h x r s a b c d q := by
    simp only [P, Formula.instantiate, read_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have e1 : P.instantiate V = read w h x r V a b c d q := by
    simp only [P, Formula.instantiate, read_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq e1 (Derives.eqSubst P he (of_eq e0.symm hl))

theorem subst_source_size {m} {Γ : Context m} (w h x r s a b c d q V : Fin m)
    (he : Derives Γ (.equal a V)) (hl : Derives Γ (read w h x r s a b c d q)) : Derives Γ (read w h x r s V b c d q) := by
  let P := read w.castSucc h.castSucc x.castSucc r.castSucc s.castSucc (Fin.last m) b.castSucc c.castSucc d.castSucc q.castSucc
  have e0 : P.instantiate a = read w h x r s a b c d q := by
    simp only [P, Formula.instantiate, read_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have e1 : P.instantiate V = read w h x r s V b c d q := by
    simp only [P, Formula.instantiate, read_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq e1 (Derives.eqSubst P he (of_eq e0.symm hl))

theorem subst_target_size {m} {Γ : Context m} (w h x r s a b c d q V : Fin m)
    (he : Derives Γ (.equal c V)) (hl : Derives Γ (read w h x r s a b c d q)) : Derives Γ (read w h x r s a b V d q) := by
  let P := read w.castSucc h.castSucc x.castSucc r.castSucc s.castSucc a.castSucc b.castSucc (Fin.last m) d.castSucc q.castSucc
  have e0 : P.instantiate c = read w h x r s a b c d q := by
    simp only [P, Formula.instantiate, read_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have e1 : P.instantiate V = read w h x r s a b V d q := by
    simp only [P, Formula.instantiate, read_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq e1 (Derives.eqSubst P he (of_eq e0.symm hl))

theorem at_lift {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h x r s a b c d q A C K H : Fin m)
    (hw : Derives Γ (omega w)) (hl : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w r s a b c d A C K H)) :
    Derives Γ ((advanced w h x r s a b c d q).iff (read w h x K H A b C d q)) := by
  apply Derives.conjI
  · apply Derives.impI
    let T := advanced w h x r s a b c d q
    let B := advancedBody w h x r s a b c d q
    let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.add T Γ)))))
    apply eliminate_advanced w h x r s a b c d q _ (.hyp (Or.inl rfl))
    have hZ4 := SyntaxRenameBinders.zf_under_4 (ZFContext.add hZ T) B
    have hw4 : Derives Δ (omega w.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_4 (add hw T) B)
    have hl4 : Derives Δ (SyntaxCodedMixedBinderSyntax.lifted w.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc.castSucc K.castSucc.castSucc.castSucc.castSucc H.castSucc.castSucc.castSucc.castSucc) :=
      of_eq (by simp only [Formula.raise, SyntaxCodedMixedBinderSyntax.lifted_rename]) (SyntaxRenameBinders.under_4 (add hl T) B)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have eq := SyntaxMixedFormulaBinderAlign.all_targets_unique hZ4 w.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc
      (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+3)) A.castSucc.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc.castSucc K.castSucc.castSucc.castSucc.castSucc H.castSucc.castSucc.castSucc.castSucc hw4 (.conjL hB) hl4
    have hr := subst_bound_code w.castSucc.castSucc.castSucc.castSucc h.castSucc.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+3))
      (Fin.last m).castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc.castSucc K.castSucc.castSucc.castSucc.castSucc (.conjL (.conjR (.conjR eq))) (.conjR hB)
    have hs := subst_free_code w.castSucc.castSucc.castSucc.castSucc h.castSucc.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc.castSucc K.castSucc.castSucc.castSucc.castSucc (Fin.last (m+3))
      (Fin.last m).castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc.castSucc H.castSucc.castSucc.castSucc.castSucc (.conjR (.conjR (.conjR eq))) hr
    have ha := subst_source_size w.castSucc.castSucc.castSucc.castSucc h.castSucc.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc.castSucc K.castSucc.castSucc.castSucc.castSucc H.castSucc.castSucc.castSucc.castSucc
      (Fin.last m).castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc.castSucc (.conjL eq) hs
    have hc := subst_target_size w.castSucc.castSucc.castSucc.castSucc h.castSucc.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc.castSucc K.castSucc.castSucc.castSucc.castSucc H.castSucc.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc.castSucc (.conjL (.conjR eq)) ha
    exact of_eq (by simp only [Formula.raise, read_rename]) hc
  · apply Derives.impI
    exact intro_advanced w h x r s a b c d q A C K H (add hl _) (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.SyntaxMixedFormulaAdvancedKnown
