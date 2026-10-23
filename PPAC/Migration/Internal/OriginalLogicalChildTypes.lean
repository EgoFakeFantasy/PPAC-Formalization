import PPAC.Migration.Internal.OriginalFormulaHistoryAgreementSyntax

/-! 原否定和四种二元连接词的实际子码完整FormulaCode类型。 -/
namespace PPAC.Migration.Internal.OriginalLogicalChildTypes
open Source SourceAlgebra SourceLogic OmegaSyntax

theorem negation {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b n x : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (FormulaCodeSyntax.formulaCode w n a b))
    (hc : Derives Γ (SyntaxLogicalSyntax.singleCode 4 w x n)) : Derives Γ (FormulaCodeSyntax.formulaCode w x a b) :=
  .conjR (.impE (.conjL (FormulaCodeKnownLogical.negation_iff hZ w a b x n hw hc)) hn)

theorem binary {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4) (w a b n x y : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (FormulaCodeSyntax.formulaCode w n a b))
    (hc : Derives Γ (SyntaxLogicalSyntax.binaryCode kind w x y n)) :
    Derives Γ ((FormulaCodeSyntax.formulaCode w x a b).conj (FormulaCodeSyntax.formulaCode w y a b)) := by
  have hcases : kind = 0 ∨ kind = 1 ∨ kind = 2 ∨ kind = 3 := by omega
  rcases hcases with rfl | rfl | rfl | rfl
  · exact .conjR (.impE (.conjL (FormulaCodeKnownLogical.binary0_iff hZ w a b x y n hw hc)) hn)
  · exact .conjR (.impE (.conjL (FormulaCodeKnownLogical.binary1_iff hZ w a b x y n hw hc)) hn)
  · exact .conjR (.impE (.conjL (FormulaCodeKnownLogical.binary2_iff hZ w a b x y n hw hc)) hn)
  · exact .conjR (.impE (.conjL (FormulaCodeKnownLogical.binary3_iff hZ w a b x y n hw hc)) hn)

end PPAC.Migration.Internal.OriginalLogicalChildTypes
