import PPAC.Migration.Internal.SyntaxTopFormulaTyping

/-! 每个合法内部首槽输入实际取得公式输出；环境码和目标码全部由对象存在消去取得。 -/
namespace PPAC.Migration.Internal.SyntaxTopFormulaExistence
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax SyntaxTopFormulaSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem instantiate_at_codes_exists {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b A t n R S : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w a b A t R S))
    (hn : Derives Γ (FormulaCodeSyntax.formulaCode w n A b)) : Derives Γ (instantiateExists w a b A t n) := by
  let Q := SyntaxMixedFormulaJudgmentSyntax.substituted w.castSucc R.castSucc S.castSucc A.castSucc b.castSucc a.castSucc b.castSucc n.castSucc (Fin.last m)
  let Δ := Context.add Q (Context.image Formula.raise Γ)
  apply Derives.exE (p := Q) (SyntaxTopFormulaAtCodes.instantiate_formula_exists hZ w a b A t R S n hw he hn)
  have he1 : Derives Δ (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w.castSucc a.castSucc b.castSucc A.castSucc t.castSucc R.castSucc S.castSucc) := of_eq (SyntaxTopCodedEnvironmentSyntax.instantiateCoded_rename w a b A t R S Fin.castSucc) (under he Q)
  have hQ : Derives Δ Q := .hyp (Or.inl rfl)
  have hh := intro_instantiated w.castSucc a.castSucc b.castSucc A.castSucc t.castSucc n.castSucc (Fin.last m) R.castSucc S.castSucc he1 hQ
  have ho := intro_instantiate_exists w.castSucc a.castSucc b.castSucc A.castSucc t.castSucc n.castSucc (Fin.last m) hh
  exact of_eq (instantiateExists_rename w a b A t n Fin.castSucc).symm ho

theorem instantiate_exists {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b A t n : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (instantiateInput w a b A t n)) : Derives Γ (instantiateExists w a b A t n) := by
  let E := SyntaxTopCodedEnvironmentSyntax.instantiateCoded w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc t.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
  let Δ := Context.add E (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply SyntaxRenameBinders.eliminate_2 E _ (SyntaxTopCodedEnvironmentExistence.instantiate_exists hZ w a b A t hw (.conjL hi))
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ E
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw E)
  have hn2 : Derives Δ (FormulaCodeSyntax.formulaCode w.castSucc.castSucc n.castSucc.castSucc A.castSucc.castSucc b.castSucc.castSucc) := of_eq (by simp only [Formula.raise, FormulaCodeSyntax.formulaCode_rename]) (SyntaxRenameBinders.under_2 (.conjR hi) E)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have ho := instantiate_at_codes_exists hZ2 w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc t.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hw2 hE hn2
  exact of_eq (by simp only [Formula.raise, instantiateExists_rename]) ho

theorem abstract_at_codes_exists {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b A B n R S : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S))
    (hn : Derives Γ (FormulaCodeSyntax.formulaCode w n a B)) : Derives Γ (abstractExists w a b A B n) := by
  let Q := SyntaxMixedFormulaJudgmentSyntax.substituted w.castSucc R.castSucc S.castSucc a.castSucc B.castSucc A.castSucc b.castSucc n.castSucc (Fin.last m)
  let Δ := Context.add Q (Context.image Formula.raise Γ)
  apply Derives.exE (p := Q) (SyntaxTopFormulaAtCodes.abstract_formula_exists hZ w a b A B R S n hw he hn)
  have he1 : Derives Δ (SyntaxTopCodedEnvironmentSyntax.abstractCoded w.castSucc a.castSucc b.castSucc A.castSucc B.castSucc R.castSucc S.castSucc) := of_eq (SyntaxTopCodedEnvironmentSyntax.abstractCoded_rename w a b A B R S Fin.castSucc) (under he Q)
  have hQ : Derives Δ Q := .hyp (Or.inl rfl)
  have hh := intro_abstracted w.castSucc a.castSucc b.castSucc A.castSucc B.castSucc n.castSucc (Fin.last m) R.castSucc S.castSucc he1 hQ
  have ho := intro_abstract_exists w.castSucc a.castSucc b.castSucc A.castSucc B.castSucc n.castSucc (Fin.last m) hh
  exact of_eq (abstractExists_rename w a b A B n Fin.castSucc).symm ho

theorem abstract_exists {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b A B n : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (abstractInput w a b A B n)) : Derives Γ (abstractExists w a b A B n) := by
  let E := SyntaxTopCodedEnvironmentSyntax.abstractCoded w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc B.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
  let Δ := Context.add E (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply SyntaxRenameBinders.eliminate_2 E _ (SyntaxTopCodedEnvironmentExistence.abstract_exists hZ w a b A B hw (.conjL hi))
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ E
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw E)
  have hn2 : Derives Δ (FormulaCodeSyntax.formulaCode w.castSucc.castSucc n.castSucc.castSucc a.castSucc.castSucc B.castSucc.castSucc) := of_eq (by simp only [Formula.raise, FormulaCodeSyntax.formulaCode_rename]) (SyntaxRenameBinders.under_2 (.conjR hi) E)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have ho := abstract_at_codes_exists hZ2 w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc B.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hw2 hE hn2
  exact of_eq (by simp only [Formula.raise, abstractExists_rename]) ho

end PPAC.Migration.Internal.SyntaxTopFormulaExistence
