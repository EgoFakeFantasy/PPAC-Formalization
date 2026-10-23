import PPAC.Migration.Internal.SyntaxMixedFormulaJudgment

/-! 混合公式判断从实际求值/分离状态恢复准确源与目标类型；不据此宣称每个合法源有唯一输出。 -/
namespace PPAC.Migration.Internal.SyntaxMixedFormulaJudgmentTyping
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax SyntaxMixedFormulaJudgmentSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

def input {m} (w r s a b c d n : Fin m) : Formula m :=
  (SyntaxMixedImageCodeSyntax.termLists w a b c d r s).conj (FormulaCodeSyntax.formulaCode w n a b)

theorem input_rename {m k} (w r s a b c d n : Fin m) (ρ : Fin m → Fin k) :
    (input w r s a b c d n).rename ρ = input (ρ w) (ρ r) (ρ s) (ρ a) (ρ b) (ρ c) (ρ d) (ρ n) := by
  simp only [input, Formula.rename, SyntaxMixedImageCodeSyntax.termLists_rename, FormulaCodeSyntax.formulaCode_rename]

theorem source_type {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s a b c d n q : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (substituted w r s a b c d n q)) :
    Derives Γ (FormulaCodeSyntax.formulaCode w n a b) := by
  let B := body w r s a b c d n q
  let Ξ := Context.add B (Context.image Formula.raise Γ)
  apply eliminate_substituted w r s a b c d n q _ hr
  have hZ1 := ZFContext.under hZ B
  have hw1 : Derives Ξ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hn1 : Derives Ξ (.mem n.castSucc w.castSucc) := under (.conjL hr) B
  have hB : Derives Ξ B := .hyp (Or.inl rfl)
  let H := (SyntaxMixedFormulaRecursionSyntax.graph w.castSucc.castSucc (Fin.last (m+1)) n.castSucc.castSucc).conj
    (SyntaxMixedFormulaOperatorSyntax.value w.castSucc.castSucc n.castSucc.castSucc (Fin.last (m+1)) (Fin.last m).castSucc)
  let Δ := Context.add H (Context.image Formula.raise Ξ)
  apply Derives.exE (p := H) (SyntaxMixedFormulaHistory.from_value hZ1 w.castSucc n.castSucc (Fin.last m)
    (NaturalOrderBasic.ordinal hZ1 w.castSucc n.castSucc hw1 hn1) (.conjL hB))
  have hZ2 := ZFContext.under hZ1 H
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (omega_rename w.castSucc Fin.castSucc) (under hw1 H)
  have hc2 : Derives Δ (SyntaxMixedFormulaQuerySyntax.contains w.castSucc.castSucc (Fin.last m).castSucc r.castSucc.castSucc s.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc q.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, SyntaxMixedFormulaQuerySyntax.contains_rename]) (under (.conjR hB) H)
  have hH : Derives Δ H := .hyp (Or.inl rfl)
  have hs := SyntaxMixedFormulaJudgmentState.contains_content hZ2 w.castSucc.castSucc n.castSucc.castSucc (Fin.last (m+1)) (Fin.last m).castSucc r.castSucc.castSucc s.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc q.castSucc.castSucc hw2 (.conjR hH) hc2
  exact of_eq (by simp only [Formula.raise, FormulaCodeSyntax.formulaCode_rename]) (.conjL hs)

theorem input_of_substituted {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s a b c d n q : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (substituted w r s a b c d n q)) : Derives Γ (input w r s a b c d n) :=
  .conjI (.conjL (SyntaxMixedFormulaJudgment.legal w r s a b c d n q hr)) (source_type hZ w r s a b c d n q hw hr)

theorem output_natural {m} {Γ : Context m} (w r s a b c d n q : Fin m)
    (hr : Derives Γ (substituted w r s a b c d n q)) : Derives Γ (.mem q w) :=
  .conjL (FormulaCodeProperties.guards w q c d (SyntaxMixedFormulaJudgment.target_type w r s a b c d n q hr))

end PPAC.Migration.Internal.SyntaxMixedFormulaJudgmentTyping
