import PPAC.Migration.Internal.ProjectCompilerUniqueStep

/-! Original Foundation establishes scalar functionality of the actual compiler on all internal inputs. -/
namespace PPAC.Migration.Internal.ProjectCompilerUnique
open Source SourceAlgebra SourceLogic OmegaSyntax ProjectCompilerUniqueSyntax
open SyntaxRenameQuerySyntax (of_eq)
open ReplacementPredicates (paramsUp)

def inductionMatrix : Formula 2 := functional (0 : Fin 1).castSucc (Fin.last 1)

theorem matrix_pred {m} (ρ : Fin 1 → Fin m) (x : Fin m) :
    MinimalPredicates.pred inductionMatrix ρ x = functional (ρ 0) x := by
  simp only [inductionMatrix, MinimalPredicates.pred, functional_rename, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem progressive {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) (hw : Derives Γ (omega w)) :
    Derives Γ (SetInductionSyntax.progressive inductionMatrix (fun _ : Fin 1 => w)) := by
  simp only [SetInductionSyntax.progressive, SetInductionSyntax.below, matrix_pred, paramsUp]
  apply Derives.allI
  apply Derives.impI
  let I := allIH w.castSucc (Fin.last m)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw I)
  exact ProjectCompilerUniqueStep.from_induction (ZFContext.under hZ I) w.castSucc (Fin.last m) hw1 (.hyp (Or.inl rfl))

theorem all_functional {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) (hw : Derives Γ (omega w)) :
    Derives Γ (.all (functional w.castSucc (Fin.last m))) := by
  have hh := SetInduction.all_holds inductionMatrix (fun _ : Fin 1 => w)
    (ZFContext.separation hZ inductionMatrix.neg) (ZFContext.arithmetic hZ).base.foundation
    (ZFContext.closed hZ ObjectTransitiveCover.source_cover) (progressive hZ w hw)
  exact of_eq (by simp only [SetInductionSyntax.holds, matrix_pred, paramsUp]) hh

theorem at_input {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m) (hw : Derives Γ (omega w)) :
    Derives Γ (functional w n) := of_eq
  (by simp only [Formula.instantiate, functional_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
  (Derives.allE n (all_functional hZ w hw))

theorem unique_outputs {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n b q r : Fin m)
    (hw : Derives Γ (omega w)) (hq : Derives Γ (ProjectCompilerCodeSyntax.compiled w n b q))
    (hr : Derives Γ (ProjectCompilerCodeSyntax.compiled w n b r)) : Derives Γ (.equal q r) :=
  unique_at w n b q r (at_input hZ w n hw) hq hr

end PPAC.Migration.Internal.ProjectCompilerUnique
