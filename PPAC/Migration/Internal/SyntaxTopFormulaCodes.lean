import PPAC.Migration.Internal.SyntaxTopFormulaSyntax

/-! 任一实际合法首槽环境码对识别同一个首槽公式判断，消去所有候选环境见证。 -/
namespace PPAC.Migration.Internal.SyntaxTopFormulaCodes
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax SyntaxTopFormulaSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem instantiate_at_codes {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b A t n q R S : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w a b A t R S)) :
    Derives Γ ((instantiated w a b A t n q).iff (SyntaxMixedFormulaJudgmentSyntax.substituted w R S A b a b n q)) := by
  apply Derives.conjI
  · apply Derives.impI
    let T := instantiated w a b A t n q
    let E := instantiateBody w a b A t n q
    let Δ := Context.add E (Context.image Formula.raise (Context.image Formula.raise (Context.add T Γ)))
    apply SyntaxRenameBinders.eliminate_2 E _ (.hyp (Or.inl rfl))
    have hZ2 := SyntaxRenameBinders.zf_under_2 (ZFContext.add hZ T) E
    have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 (add hw T) E)
    have he2 : Derives Δ (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc t.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc) :=
      of_eq (by simp only [Formula.raise, SyntaxTopCodedEnvironmentSyntax.instantiateCoded_rename]) (SyntaxRenameBinders.under_2 (add he T) E)
    have hE : Derives Δ E := .hyp (Or.inl rfl)
    have eq := SyntaxTopCodedEnvironmentUnique.instantiate_unique hZ2 w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc t.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) R.castSucc.castSucc S.castSucc.castSucc hw2 (.conjL hE) he2
    have hr := SyntaxMixedFormulaJudgmentSubst.subst_r w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) A.castSucc.castSucc b.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc n.castSucc.castSucc q.castSucc.castSucc R.castSucc.castSucc (.conjL eq) (.conjR hE)
    have hs := SyntaxMixedFormulaJudgmentSubst.subst_s w.castSucc.castSucc R.castSucc.castSucc (Fin.last (m+1)) A.castSucc.castSucc b.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc n.castSucc.castSucc q.castSucc.castSucc S.castSucc.castSucc (.conjR eq) hr
    exact of_eq (by simp only [Formula.raise, SyntaxMixedFormulaJudgmentSyntax.substituted_rename]) hs
  · apply Derives.impI
    exact intro_instantiated w a b A t n q R S (add he _) (.hyp (Or.inl rfl))

theorem abstract_at_codes {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b A B n q R S : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S)) :
    Derives Γ ((abstracted w a b A B n q).iff (SyntaxMixedFormulaJudgmentSyntax.substituted w R S a B A b n q)) := by
  apply Derives.conjI
  · apply Derives.impI
    let T := abstracted w a b A B n q
    let E := abstractBody w a b A B n q
    let Δ := Context.add E (Context.image Formula.raise (Context.image Formula.raise (Context.add T Γ)))
    apply SyntaxRenameBinders.eliminate_2 E _ (.hyp (Or.inl rfl))
    have hZ2 := SyntaxRenameBinders.zf_under_2 (ZFContext.add hZ T) E
    have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 (add hw T) E)
    have he2 : Derives Δ (SyntaxTopCodedEnvironmentSyntax.abstractCoded w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc B.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc) :=
      of_eq (by simp only [Formula.raise, SyntaxTopCodedEnvironmentSyntax.abstractCoded_rename]) (SyntaxRenameBinders.under_2 (add he T) E)
    have hE : Derives Δ E := .hyp (Or.inl rfl)
    have eq := SyntaxTopCodedEnvironmentUnique.abstract_unique hZ2 w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc B.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) R.castSucc.castSucc S.castSucc.castSucc hw2 (.conjL hE) he2
    have hr := SyntaxMixedFormulaJudgmentSubst.subst_r w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) a.castSucc.castSucc B.castSucc.castSucc A.castSucc.castSucc b.castSucc.castSucc n.castSucc.castSucc q.castSucc.castSucc R.castSucc.castSucc (.conjL eq) (.conjR hE)
    have hs := SyntaxMixedFormulaJudgmentSubst.subst_s w.castSucc.castSucc R.castSucc.castSucc (Fin.last (m+1)) a.castSucc.castSucc B.castSucc.castSucc A.castSucc.castSucc b.castSucc.castSucc n.castSucc.castSucc q.castSucc.castSucc S.castSucc.castSucc (.conjR eq) hr
    exact of_eq (by simp only [Formula.raise, SyntaxMixedFormulaJudgmentSyntax.substituted_rename]) hs
  · apply Derives.impI
    exact intro_abstracted w a b A B n q R S (add he _) (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.SyntaxTopFormulaCodes
