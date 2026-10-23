import PPAC.Migration.Internal.SyntaxMixedFormulaRawFields

/-! 合法输入及已知源标签下，正式 MixedFormulaSubst 精确等价于原分支，而非仅单向筛选。 -/
namespace PPAC.Migration.Internal.SyntaxMixedFormulaSelectedIff
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem source_case {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 11) (arity : Nat)
    (w R S a b c d n q : Fin m) (xs : Fin arity → Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (SyntaxMixedFormulaOutputSyntax.input w R S a b c d n))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor arity kind.val w xs n)) :
    Derives Γ ((SyntaxMixedFormulaJudgmentSyntax.substituted w R S a b c d n q).iff
      (SyntaxMixedFormulaTagCases.tagBranch kind w R S a b c d n q)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact SyntaxMixedFormulaTagCases.of_substituted (ZFContext.add hZ _) kind arity w R S a b c d n q xs (add hw _) (add hc _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    let B := SyntaxMixedFormulaTagCases.tagBranch kind w R S a b c d n q
    have hB : Derives (Context.add B Γ) B := .hyp (Or.inl rfl)
    have ht := SyntaxMixedFormulaCaseTyping.selected (ZFContext.add hZ B) kind w R S a b c d n q (add hw B) (add hi B) hB
    exact SyntaxMixedFormulaCases.intro_from_cases (ZFContext.add hZ B) w R S a b c d n q (add hw B) (add hi B) ht (SyntaxMixedFormulaBranchIntro.intro_cases kind w R S a b c d n q hB)
end PPAC.Migration.Internal.SyntaxMixedFormulaSelectedIff
