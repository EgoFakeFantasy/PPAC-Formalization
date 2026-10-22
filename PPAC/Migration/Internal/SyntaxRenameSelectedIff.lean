import PPAC.Migration.Internal.SyntaxRenameRawFields

/-! 合法输入及已知源标签下，正式 RenameFormula 精确等价于原分支，而非仅单向筛选。 -/
namespace PPAC.Migration.Internal.SyntaxRenameSelectedIff
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem source_case {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 11) (arity : Nat)
    (w R S r s a b c d n q : Fin m) (xs : Fin arity → Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (SyntaxRenameOutputSyntax.input w R S a b c d n))
    (hr : Derives Γ (SyntaxMapCodeSyntax.encoded w r a c R)) (hs : Derives Γ (SyntaxMapCodeSyntax.encoded w s b d S))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor arity kind.val w xs n)) :
    Derives Γ ((SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q).iff
      (SyntaxRenameTagCases.tagBranch kind w R S r s a b c d n q)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact SyntaxRenameTagCases.of_renamed (ZFContext.add hZ _) kind arity w R S r s a b c d n q xs (add hw _) (add hr _) (add hs _) (add hc _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    let B := SyntaxRenameTagCases.tagBranch kind w R S r s a b c d n q
    have hB : Derives (Context.add B Γ) B := .hyp (Or.inl rfl)
    have ht := SyntaxRenameCaseTyping.selected (ZFContext.add hZ B) kind w R S r s a b c d n q (add hw B) (add hi B) hB
    exact SyntaxRenameActualGraphs.intro_from_cases (ZFContext.add hZ B) w R S r s a b c d n q (add hw B) (add hi B) (add hr B) (add hs B) ht (SyntaxRenameBranchIntro.intro_cases kind w R S r s a b c d n q hB)
end PPAC.Migration.Internal.SyntaxRenameSelectedIff
