import PPAC.Migration.Internal.SyntaxMixedFormulaBinderAlign
import PPAC.Migration.Internal.SyntaxMixedFormulaJudgmentSubst

/-! 真正的四见证混合量词查询在任意实际binder提升上识别同一子查询；两份环境码均对齐。 -/
namespace PPAC.Migration.Internal.SyntaxMixedFormulaAdvancedOutput
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxMixedFormulaRecursiveSyntax SyntaxMixedFormulaJudgmentSyntax
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem subst_bound_code {m} {Γ : Context m} (w x r s a b c d q V : Fin m)
    (he : Derives Γ (.equal r V)) (hl : Derives Γ (substituted w r s a b c d x q)) :
    Derives Γ (substituted w V s a b c d x q) :=
  SyntaxMixedFormulaJudgmentSubst.subst_r w r s a b c d x q V he hl

theorem subst_free_code {m} {Γ : Context m} (w x r s a b c d q V : Fin m)
    (he : Derives Γ (.equal s V)) (hl : Derives Γ (substituted w r s a b c d x q)) :
    Derives Γ (substituted w r V a b c d x q) :=
  SyntaxMixedFormulaJudgmentSubst.subst_s w r s a b c d x q V he hl

theorem subst_source_size {m} {Γ : Context m} (w x r s a b c d q V : Fin m)
    (he : Derives Γ (.equal a V)) (hl : Derives Γ (substituted w r s a b c d x q)) :
    Derives Γ (substituted w r s V b c d x q) :=
  SyntaxMixedFormulaJudgmentSubst.subst_a w r s a b c d x q V he hl

theorem subst_target_size {m} {Γ : Context m} (w x r s a b c d q V : Fin m)
    (he : Derives Γ (.equal c V)) (hl : Derives Γ (substituted w r s a b c d x q)) :
    Derives Γ (substituted w r s a b V d x q) :=
  SyntaxMixedFormulaJudgmentSubst.subst_c w r s a b c d x q V he hl

theorem intro_advanced {m} {Γ : Context m} (w x r s a b c d q A C K H : Fin m)
    (hl : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w r s a b c d A C K H))
    (hq : Derives Γ (substituted w K H A b C d x q)) :
    Derives Γ (advanced w x r s a b c d q) := by
  apply Derives.exI A
  apply Derives.exI C
  apply Derives.exI K
  apply Derives.exI H
  simp only [advancedBody, Formula.instantiate, Formula.rename, SyntaxCodedMixedBinderSyntax.lifted_rename,
    substituted_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI hl hq

theorem eliminate_advanced {m} {Γ : Context m} (w x r s a b c d q : Fin m) (P : Formula m)
    (he : Derives Γ (advanced w x r s a b c d q))
    (hc : Derives (Context.add (advancedBody w x r s a b c d q)
      (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ))))) P.raise.raise.raise.raise) : Derives Γ P :=
  SyntaxRenameBinders.eliminate_4 (advancedBody w x r s a b c d q) P he hc

theorem at_lift {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w x r s a b c d q A C K H : Fin m)
    (hw : Derives Γ (omega w)) (hl : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w r s a b c d A C K H)) :
    Derives Γ ((advanced w x r s a b c d q).iff (substituted w K H A b C d x q)) := by
  apply Derives.conjI
  · apply Derives.impI
    let T := advanced w x r s a b c d q
    let B := advancedBody w x r s a b c d q
    let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.add T Γ)))))
    apply eliminate_advanced w x r s a b c d q _ (.hyp (Or.inl rfl))
    have hZ4 := SyntaxRenameBinders.zf_under_4 (ZFContext.add hZ T) B
    have hw4 : Derives Δ (omega w.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_4 (add hw T) B)
    have hl4 : Derives Δ (SyntaxCodedMixedBinderSyntax.lifted w.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc.castSucc K.castSucc.castSucc.castSucc.castSucc H.castSucc.castSucc.castSucc.castSucc) :=
      of_eq (by simp only [Formula.raise, SyntaxCodedMixedBinderSyntax.lifted_rename]) (SyntaxRenameBinders.under_4 (add hl T) B)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have eq := SyntaxMixedFormulaBinderAlign.all_targets_unique hZ4 w.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc
      (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+3)) A.castSucc.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc.castSucc K.castSucc.castSucc.castSucc.castSucc H.castSucc.castSucc.castSucc.castSucc hw4 (.conjL hB) hl4
    have hr := subst_bound_code w.castSucc.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+3))
      (Fin.last m).castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc.castSucc K.castSucc.castSucc.castSucc.castSucc (.conjL (.conjR (.conjR eq))) (.conjR hB)
    have hs := subst_free_code w.castSucc.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc.castSucc K.castSucc.castSucc.castSucc.castSucc (Fin.last (m+3))
      (Fin.last m).castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc.castSucc H.castSucc.castSucc.castSucc.castSucc (.conjR (.conjR (.conjR eq))) hr
    have ha := subst_source_size w.castSucc.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc.castSucc K.castSucc.castSucc.castSucc.castSucc H.castSucc.castSucc.castSucc.castSucc
      (Fin.last m).castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc.castSucc (.conjL eq) hs
    have hc := subst_target_size w.castSucc.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc.castSucc K.castSucc.castSucc.castSucc.castSucc H.castSucc.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc.castSucc C.castSucc.castSucc.castSucc.castSucc (.conjL (.conjR eq)) ha
    exact of_eq (by simp only [Formula.raise, substituted_rename]) hc
  · apply Derives.impI
    exact intro_advanced w x r s a b c d q A C K H (add hl _) (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.SyntaxMixedFormulaAdvancedOutput
