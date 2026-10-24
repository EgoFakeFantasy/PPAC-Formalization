import PPAC.Migration.Internal.ProjectCompilerTypingStep

/-! Original Foundation discharges all internal member induction hypotheses for compiler output typing. -/
namespace PPAC.Migration.Internal.ProjectCompilerTyping
open Source SourceAlgebra SourceLogic OmegaSyntax ProjectCompilerTypingSyntax
open FormulaCodeSyntax
open SyntaxRenameQuerySyntax (of_eq)
open ReplacementPredicates (paramsUp)

def inductionMatrix : Formula 2 := correct (0 : Fin 1).castSucc (Fin.last 1)

theorem matrix_pred {m} (ρ : Fin 1 → Fin m) (x : Fin m) :
    MinimalPredicates.pred inductionMatrix ρ x = correct (ρ 0) x := by
  simp only [inductionMatrix, MinimalPredicates.pred, correct_rename, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem progressive {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) (hw : Derives Γ (omega w)) :
    Derives Γ (SetInductionSyntax.progressive inductionMatrix (fun _ : Fin 1 => w)) := by
  simp only [SetInductionSyntax.progressive, SetInductionSyntax.below, matrix_pred, paramsUp]
  apply Derives.allI
  apply Derives.impI
  let I := allIH w.castSucc (Fin.last m)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw I)
  exact ProjectCompilerTypingStep.from_induction (ZFContext.under hZ I) w.castSucc (Fin.last m) hw1 (.hyp (Or.inl rfl))

theorem all_correct {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) (hw : Derives Γ (omega w)) :
    Derives Γ (.all (correct w.castSucc (Fin.last m))) := by
  have hh := SetInduction.all_holds inductionMatrix (fun _ : Fin 1 => w)
    (ZFContext.separation hZ inductionMatrix.neg) (ZFContext.arithmetic hZ).base.foundation
    (ZFContext.closed hZ ObjectTransitiveCover.source_cover) (progressive hZ w hw)
  exact of_eq (by simp only [SetInductionSyntax.holds, matrix_pred, paramsUp]) hh

theorem at_input {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m) (hw : Derives Γ (omega w)) :
    Derives Γ (correct w n) := of_eq
  (by simp only [Formula.instantiate, correct_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
  (Derives.allE n (all_correct hZ w hw))

theorem output_type {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n b q z : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hc : Derives Γ (ProjectCompilerCodeSyntax.compiled w n b q)) : Derives Γ (formulaCode w q b z) :=
  at_correct w n b q z (at_input hZ w n hw) hz hc

theorem reject_untyped {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n b q z : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (ht : Derives Γ (formulaCode w q b z).neg) :
    Derives Γ (ProjectCompilerCodeSyntax.compiled w n b q).neg := by
  apply Derives.impI
  exact .impE (add ht _) (output_type (ZFContext.add hZ _) w n b q z (add hw _) (add hz _) (.hyp (Or.inl rfl)))

end PPAC.Migration.Internal.ProjectCompilerTyping
