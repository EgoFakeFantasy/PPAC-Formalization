import PPAC.Migration.Internal.SyntaxMixedFormulaCaseTransfer

/-! 全11类混合局部判据双向消去历史参数；原数值项替换与四见证binder保持。 -/
namespace PPAC.Migration.Internal.SyntaxMixedFormulaLocalTransfer
open SyntaxRenameQuerySyntax (of_eq)
open Source SourceAlgebra SourceLogic OrdinalSyntax SyntaxMixedFormulaQuerySyntax FormulaCodeCongruence SyntaxTypeLocalTransfer
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem all_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S a b c d h n q : Fin m)
    (hn : Derives Γ (ordinal n)) (hg : Derives Γ (SyntaxMixedFormulaRecursionSyntax.graph w h n)) :
    Derives Γ ((SyntaxMixedFormulaLocalSyntax.cases w R S a b c d h n q).iff
      (SyntaxMixedFormulaRecursiveSyntax.cases w R S a b c d n q)) := by
  exact (disj_congr (iff_refl ((SyntaxMixedFormulaAtomSyntax.nullary false w a b c d n q).disj (SyntaxMixedFormulaAtomSyntax.nullary true w a b c d n q))) (disj_congr (iff_refl (SyntaxMixedFormulaAtomSyntax.membership w R S a b c d n q)) (disj_congr (iff_refl (SyntaxMixedFormulaAtomSyntax.equality w R S a b c d n q)) (disj_congr (SyntaxMixedFormulaCaseTransfer.single_iff hZ 4 false w h R S a b c d n q hn hg) (disj_congr (SyntaxMixedFormulaCaseTransfer.binary_iff hZ 0 w h R S a b c d n q hn hg) (disj_congr (SyntaxMixedFormulaCaseTransfer.binary_iff hZ 1 w h R S a b c d n q hn hg) (disj_congr (SyntaxMixedFormulaCaseTransfer.binary_iff hZ 2 w h R S a b c d n q hn hg) (disj_congr (SyntaxMixedFormulaCaseTransfer.binary_iff hZ 3 w h R S a b c d n q hn hg) (disj_congr (SyntaxMixedFormulaCaseTransfer.single_iff hZ 9 true w h R S a b c d n q hn hg) (SyntaxMixedFormulaCaseTransfer.single_iff hZ 10 true w h R S a b c d n q hn hg))))))))))

theorem content_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S a b c d h n q : Fin m)
    (hn : Derives Γ (ordinal n)) (hg : Derives Γ (SyntaxMixedFormulaRecursionSyntax.graph w h n)) :
    Derives Γ ((SyntaxMixedFormulaLocalSyntax.content w R S a b c d h n q).iff
      (SyntaxMixedFormulaRecursiveSyntax.content w R S a b c d n q)) :=
  conj_congr (iff_refl (FormulaCodeSyntax.formulaCode w n a b)) (all_iff hZ w R S a b c d h n q hn hg)
end PPAC.Migration.Internal.SyntaxMixedFormulaLocalTransfer
