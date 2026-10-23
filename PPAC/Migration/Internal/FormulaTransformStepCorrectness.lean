import PPAC.Migration.Internal.FormulaTransformAtomCorrectness

/-! 独立编译十一分支步骤与原递归算子步骤的对象双条件；不假设历史为标准对象。 -/
namespace PPAC.Migration.Internal.FormulaTransformStepCorrectness
open Source SourceAlgebra SourceLogic OmegaSyntax FormulaCodeCongruence SyntaxTypeLocalTransfer
open FormulaTransformProgramSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem nullary_iff {m} {Γ : Context m} (truth : Bool) (w a b c d n q : Fin m) :
    Derives Γ ((FormulaTransformAtomSyntax.nullary truth w a b c d n q).iff (SyntaxMixedFormulaAtomSyntax.nullary truth w a b c d n q)) := iff_refl _

theorem single_iff {m} {Γ : Context m} (tag : Nat) (advance : Bool) (w h R S a b c d n q : Fin m) :
    Derives Γ ((FormulaTransformLogicalSyntax.single tag advance w h R S a b c d n q).iff
      (SyntaxMixedFormulaLogicalSyntax.single tag advance w h R S a b c d n q)) := iff_refl _

theorem binary_iff {m} {Γ : Context m} (kind : Fin 4) (w h R S a b c d n q : Fin m) :
    Derives Γ ((FormulaTransformLogicalSyntax.binary kind w h R S a b c d n q).iff
      (SyntaxMixedFormulaLogicalSyntax.binary kind w h R S a b c d n q)) := iff_refl _

theorem program_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S a b c d h n q : Fin m)
    (hw : Derives Γ (omega w)) :
    Derives Γ ((run formulaProgram w R S a b c d h n q).iff (SyntaxMixedFormulaLocalSyntax.cases w R S a b c d h n q)) := by
  exact disj_congr (disj_congr (nullary_iff false w a b c d n q) (nullary_iff true w a b c d n q)) (disj_congr (FormulaTransformAtomCorrectness.membership_iff hZ w R S a b c d n q hw) (disj_congr (FormulaTransformAtomCorrectness.equality_iff hZ w R S a b c d n q hw) (disj_congr (single_iff 4 false w h R S a b c d n q) (disj_congr (binary_iff 0 w h R S a b c d n q) (disj_congr (binary_iff 1 w h R S a b c d n q) (disj_congr (binary_iff 2 w h R S a b c d n q) (disj_congr (binary_iff 3 w h R S a b c d n q) (disj_congr (single_iff 9 true w h R S a b c d n q) (single_iff 10 true w h R S a b c d n q)))))))))

theorem step_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S a b c d h n q : Fin m)
    (hw : Derives Γ (omega w)) :
    Derives Γ ((step w R S a b c d h n q).iff (SyntaxMixedFormulaLocalSyntax.content w R S a b c d h n q)) :=
  conj_congr (iff_refl (FormulaCodeSyntax.formulaCode w n a b)) (program_iff hZ w R S a b c d h n q hw)

end PPAC.Migration.Internal.FormulaTransformStepCorrectness
