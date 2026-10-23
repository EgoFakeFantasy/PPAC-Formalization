import PPAC.Migration.Internal.PureSyntaxFormulaComplete
import PPAC.Migration.SetInduction

/-! 原ZF集合归纳消去全部内部公式的IH；查询双条件只有Omega前提。 -/
namespace PPAC.Migration.Internal.PureSyntaxFormulaInduction
open Source SourceAlgebra SourceLogic OmegaSyntax PureSyntaxFormulaInductionSyntax
open SyntaxRenameQuerySyntax (of_eq)
open ReplacementPredicates (paramsUp)

def matrix : Formula 2 := correct (0 : Fin 1).castSucc (Fin.last 1)

theorem matrix_pred {m} (ρ : Fin 1 → Fin m) (x : Fin m) :
    MinimalPredicates.pred matrix ρ x = correct (ρ 0) x := by
  simp only [matrix, MinimalPredicates.pred, correct_rename, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem progressive {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) (hw : Derives Γ (omega w)) :
    Derives Γ (SetInductionSyntax.progressive matrix (fun _ : Fin 1 => w)) := by
  simp only [SetInductionSyntax.progressive, SetInductionSyntax.below, matrix_pred, paramsUp]
  apply Derives.allI
  apply Derives.impI
  let I := allIH w.castSucc (Fin.last m)
  let Δ := Context.add I (Context.image Formula.raise Γ)
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw I)
  exact PureSyntaxFormulaComplete.correct_from_induction (ZFContext.under hZ I) w.castSucc (Fin.last m) hw1 (.hyp (Or.inl rfl))

theorem all_correct {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) (hw : Derives Γ (omega w)) :
    Derives Γ (.all (correct w.castSucc (Fin.last m))) := by
  have hh := SetInduction.all_holds matrix (fun _ : Fin 1 => w)
    (ZFContext.separation hZ matrix.neg) (ZFContext.arithmetic hZ).base.foundation
    (ZFContext.closed hZ ObjectTransitiveCover.source_cover) (progressive hZ w hw)
  exact of_eq (by simp only [SetInductionSyntax.holds, matrix_pred, paramsUp]) hh

theorem at_root {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m) (hw : Derives Γ (omega w)) :
    Derives Γ (correct w n) := of_eq
      (by simp only [Formula.instantiate, correct_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (Derives.allE n (all_correct hZ w hw))

theorem all_ih {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m) (hw : Derives Γ (omega w)) :
    Derives Γ (allIH w n) := by
  apply Derives.allI
  apply Derives.impI
  let M := Formula.mem (Fin.last m) n.castSucc
  have hw1 : Derives (Context.add M (Context.image Formula.raise Γ)) (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw M)
  exact at_root (ZFContext.under hZ M) w.castSucc (Fin.last m) hw1

theorem checked_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f n : Fin m)
    (hw : Derives Γ (omega w)) :
    Derives Γ ((PureSyntaxTrace.formula w b f n).iff (FormulaCodeSyntax.formulaCode w n b f)) :=
  correct_at w n b f (at_root hZ w n hw)

theorem checked_sound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f n : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (PureSyntaxTrace.formula w b f n)) :
    Derives Γ (FormulaCodeSyntax.formulaCode w n b f) := .impE (.conjL (checked_iff hZ w b f n hw)) ht

theorem checked_complete {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f n : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (FormulaCodeSyntax.formulaCode w n b f)) :
    Derives Γ (PureSyntaxTrace.formula w b f n) := .impE (.conjR (checked_iff hZ w b f n hw)) ht

theorem full_typing {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f k n : Fin m)
    (hw : Derives Γ (omega w)) :
    Derives Γ (((PureSyntaxTrace.term w b f n).iff (SyntaxTermSyntax.term w b f n)).conj
      (((PureSyntaxTrace.arguments w b f k n).iff (SyntaxMixedImageCodeSyntax.termList w k b f n)).conj
        ((PureSyntaxTrace.formula w b f n).iff (FormulaCodeSyntax.formulaCode w n b f)))) :=
  .conjI (PureSyntaxTermCorrectness.checked_iff hZ w b f n hw)
    (.conjI (PureSyntaxArgumentInduction.checked_iff hZ w b f k n hw) (checked_iff hZ w b f n hw))

end PPAC.Migration.Internal.PureSyntaxFormulaInduction
