import PPAC.Migration.Internal.SyntaxMixedFormulaAtomUnique

/-! 从实际状态判断提取完整混合分支；从准确源/目标类型及该分支反向构造原核判断。 -/
namespace PPAC.Migration.Internal.SyntaxMixedFormulaCases
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax
open SyntaxMixedFormulaOutputSyntax SyntaxMixedFormulaJudgmentSyntax

theorem cases_of_substituted {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s a b c d n q : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (substituted w r s a b c d n q)) :
    Derives Γ (SyntaxMixedFormulaRecursiveSyntax.cases w r s a b c d n q) :=
  .conjR (.conjR (.conjR (.impE (.conjL (SyntaxMixedFormulaRecursive.recursive_iff hZ w r s a b c d n q hw)) hn)))

theorem atomic_of_substituted {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4) (arity : Nat)
    (w r s a b c d n q : Fin m) (xs : Fin arity → Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxNodeSyntax.constructor arity kind.val w xs n))
    (hn : Derives Γ (substituted w r s a b c d n q)) :
    Derives Γ (SyntaxMixedFormulaAtomicCases.atomicCase kind w r s a b c d n q) :=
  SyntaxMixedFormulaAtomicCases.filter hZ kind arity w r s a b c d n q xs hw hc
    (cases_of_substituted hZ w r s a b c d n q hw hn)

theorem intro_from_cases {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s a b c d n q : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (input w r s a b c d n))
    (ht : Derives Γ (FormulaCodeSyntax.formulaCode w q c d))
    (hc : Derives Γ (SyntaxMixedFormulaRecursiveSyntax.cases w r s a b c d n q)) :
    Derives Γ (substituted w r s a b c d n q) := by
  have hk : Derives Γ (SyntaxMixedFormulaRecursiveSyntax.criterion w r s a b c d n q) :=
    .conjI (SyntaxMixedFormulaOutput.input_natural w r s a b c d n hi)
      (.conjI (.conjI (.conjR hi) ht) (.conjI (.conjL hi) hc))
  exact .impE (.conjR (SyntaxMixedFormulaRecursive.recursive_iff hZ w r s a b c d n q hw)) hk
end PPAC.Migration.Internal.SyntaxMixedFormulaCases
