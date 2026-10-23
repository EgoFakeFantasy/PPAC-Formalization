import PPAC.Migration.Internal.IndexFormulaRenameInduction
import PPAC.Migration.Internal.SyntaxRenameOutputInduction
import PPAC.Migration.Internal.FormulaTransformProgramCode

/-! 任意内部公式码的双向索引重命名及独立程序对应；不要求标准源码或注入映射。 -/
namespace PPAC.Migration.Internal.IndexFormulaRenameBridge
open Source SourceAlgebra SourceLogic OmegaSyntax
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem output_subst {m} {Γ : Context m} (w I J a b c d n q v : Fin m)
    (he : Derives Γ (.equal q v)) (hq : Derives Γ (SyntaxRenameJudgmentSyntax.renamed w I J a b c d n q)) :
    Derives Γ (SyntaxRenameJudgmentSyntax.renamed w I J a b c d n v) := by
  let F := SyntaxRenameJudgmentSyntax.renamed w.castSucc I.castSucc J.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m)
  have h0 : F.instantiate q = SyntaxRenameJudgmentSyntax.renamed w I J a b c d n q := by
    simp only [F, Formula.instantiate, SyntaxRenameJudgmentSyntax.renamed_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have h1 : F.instantiate v = SyntaxRenameJudgmentSyntax.renamed w I J a b c d n v := by
    simp only [F, Formula.instantiate, SyntaxRenameJudgmentSyntax.renamed_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq h1 (Derives.eqSubst F he (of_eq h0.symm hq))

theorem reverse {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w I J R S a b c d n q : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (IndexTermImageCodeSyntax.environment w I J R S a b c d))
    (hq : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w R S a b c d n q)) :
    Derives Γ (SyntaxRenameJudgmentSyntax.renamed w I J a b c d n q) := by
  have hSource := SyntaxMixedFormulaRecursive.source_type hZ w R S a b c d n q hw hq
  have hCodes := IndexTermImageEnvironment.source_codes w I J R S a b c d he
  have hx := SyntaxRenameOutputInduction.actual_exists hZ w I J a b c d n hw (.conjI hSource hCodes)
  let B := SyntaxRenameJudgmentSyntax.renamed w.castSucc I.castSucc J.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE hx
  have hZ1 := ZFContext.under hZ B
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have he1 : Derives Δ (IndexTermImageCodeSyntax.environment w.castSucc I.castSucc J.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc) := of_eq (IndexTermImageCodeSyntax.environment_rename w I J R S a b c d Fin.castSucc) (under he B)
  have hq1 : Derives Δ (SyntaxMixedFormulaJudgmentSyntax.substituted w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc q.castSucc) := of_eq (SyntaxMixedFormulaJudgmentSyntax.substituted_rename w R S a b c d n q Fin.castSucc) (under hq B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hv := IndexFormulaRenameInduction.forward hZ1 w.castSucc I.castSucc J.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m) hw1 he1 hB
  have hEq := SyntaxMixedFormulaOutputInduction.unique hZ1 w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m) q.castSucc hw1 hv hq1
  have ho := output_subst w.castSucc I.castSucc J.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m) q.castSucc hEq hB
  exact of_eq (SyntaxRenameJudgmentSyntax.renamed_rename w I J a b c d n q Fin.castSucc).symm ho

theorem rename_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w I J R S a b c d n q : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (IndexTermImageCodeSyntax.environment w I J R S a b c d)) :
    Derives Γ ((SyntaxRenameJudgmentSyntax.renamed w I J a b c d n q).iff
      (SyntaxMixedFormulaJudgmentSyntax.substituted w R S a b c d n q)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact IndexFormulaRenameInduction.forward (ZFContext.add hZ _) w I J R S a b c d n q (add hw _) (add he _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact reverse (ZFContext.add hZ _) w I J R S a b c d n q (add hw _) (add he _) (.hyp (Or.inl rfl))

theorem program_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w I J R S a b c d n q : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (IndexTermImageCodeSyntax.environment w I J R S a b c d)) :
    Derives Γ ((FormulaTransformExecutionSyntax.executed w R S a b c d n q).iff
      (SyntaxRenameJudgmentSyntax.renamed w I J a b c d n q)) := by
  have h := rename_iff hZ w I J R S a b c d n q hw he
  exact SyntaxTypeLocalTransfer.iff_trans
    (FormulaTransformRecursionCorrectness.execution_iff hZ w R S a b c d n q hw) (.conjI (.conjR h) (.conjL h))

end PPAC.Migration.Internal.IndexFormulaRenameBridge
