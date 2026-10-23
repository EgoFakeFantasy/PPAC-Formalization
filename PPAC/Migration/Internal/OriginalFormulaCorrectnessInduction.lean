import PPAC.Migration.Internal.OriginalFormulaCorrectnessPoint
import PPAC.Migration.SetInduction

/-! 原ZF的无界集合归纳消去统一IH；所有内部码、变化环境和候选输出均在对象公式内量化。 -/
namespace PPAC.Migration.Internal.OriginalFormulaCorrectnessInduction
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax
open OriginalUniformInductionSyntax
open ReplacementPredicates (paramsUp)
attribute [local irreducible] NaturalRecursionSyntax.matrix

def matrix (three : Bool) : Formula 2 := correct three (0 : Fin 1).castSucc (Fin.last 1)

theorem matrix_pred {m} (three : Bool) (ρ : Fin 1 → Fin m) (x : Fin m) :
    MinimalPredicates.pred (matrix three) ρ x = correct three (ρ 0) x := by
  simp only [matrix, MinimalPredicates.pred, correct_rename, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem progressive {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (three : Bool)
    (w : Fin m) (hw : Derives Γ (omega w)) :
    Derives Γ (SetInductionSyntax.progressive (matrix three) (fun _ : Fin 1 => w)) := by
  simp only [SetInductionSyntax.progressive, SetInductionSyntax.below, matrix_pred, paramsUp]
  apply Derives.allI
  apply Derives.impI
  let I := allFramesIH three w.castSucc (Fin.last m)
  let Δ := Context.add I (Context.image Formula.raise Γ)
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw I)
  exact OriginalFormulaCorrectnessPoint.correct_from_induction (ZFContext.under hZ I) three w.castSucc (Fin.last m) hw1 (.hyp (Or.inl rfl))

theorem all_correct {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (three : Bool)
    (w : Fin m) (hw : Derives Γ (omega w)) :
    Derives Γ (.all (correct three w.castSucc (Fin.last m))) := by
  have hh := SetInduction.all_holds (matrix three) (fun _ : Fin 1 => w)
    (ZFContext.separation hZ (matrix three).neg) (ZFContext.arithmetic hZ).base.foundation
    (ZFContext.closed hZ ObjectTransitiveCover.source_cover) (progressive hZ three w hw)
  exact of_eq (by simp only [SetInductionSyntax.holds, matrix_pred, paramsUp]) hh

theorem at_root {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (three : Bool)
    (w n : Fin m) (hw : Derives Γ (omega w)) : Derives Γ (correct three w n) :=
  of_eq (by simp only [Formula.instantiate, correct_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
    (Derives.allE n (all_correct hZ three w hw))

theorem all_frames_ih {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (three : Bool)
    (w n : Fin m) (hw : Derives Γ (omega w)) : Derives Γ (allFramesIH three w n) := by
  apply Derives.allI
  apply Derives.impI
  let M := Formula.mem (Fin.last m) n.castSucc
  have hw1 : Derives (Context.add M (Context.image Formula.raise Γ)) (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw M)
  exact at_root (ZFContext.under hZ M) three w.castSucc (Fin.last m) hw1

theorem run_iff_execution {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (three : Bool)
    (w n mode depth P a b c I J R S q : Fin m) (hw : Derives Γ (omega w))
    (hf : Derives Γ (OriginalOperationFrameSyntax.frame three w mode depth P a b c I J R S))
    (hn : Derives Γ (FormulaCodeSyntax.formulaCode w n a b)) :
    Derives Γ ((OriginalTransformRowSyntax.run 3 w mode depth (OriginalOperationFrameSyntax.parameter three P S) n q).iff
      (FormulaTransformExecutionSyntax.executed w R S a b a c n q)) :=
  correct_at three w n mode depth P a b c I J R S q (at_root hZ three w n hw) hf hn

theorem actual_history_agreement {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (three : Bool)
    (w n mode depth P a b c I J R S h : Fin m) (hw : Derives Γ (omega w))
    (ho : Derives Γ (OrdinalSyntax.ordinal n))
    (hg : Derives Γ (FormulaTransformRecursionSyntax.graph w h n))
    (hf : Derives Γ (OriginalOperationFrameSyntax.frame three w mode depth P a b c I J R S)) :
    Derives Γ (OriginalFormulaHistoryAgreementSyntax.agreement w mode depth (OriginalOperationFrameSyntax.parameter three P S) h R S a b a c n) :=
  OriginalUniformInductionRules.agreement_at_frame hZ three w n mode depth P a b c I J R S h hw ho hg (all_frames_ih hZ three w n hw) hf

theorem run_iff_program {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (three : Bool)
    (w n mode depth P a b c I J R S h q : Fin m) (hw : Derives Γ (omega w))
    (hf : Derives Γ (OriginalOperationFrameSyntax.frame three w mode depth P a b c I J R S))
    (hn : Derives Γ (FormulaCodeSyntax.formulaCode w n a b))
    (hg : Derives Γ (FormulaTransformRecursionSyntax.graph w h n)) :
    Derives Γ ((OriginalTransformRowSyntax.run 3 w mode depth (OriginalOperationFrameSyntax.parameter three P S) n q).iff
      (FormulaTransformProgramSyntax.run FormulaTransformProgramSyntax.formulaProgram w R S a b a c h n q)) :=
  OriginalFullFormulaProgram.program_iff hZ three w n mode depth P a b c I J R S h q hw (all_frames_ih hZ three w n hw) hf hn hg

theorem agreed_history_exists {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (three : Bool)
    (w n mode depth P a b c I J R S : Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (FormulaCodeSyntax.formulaCode w n a b))
    (hf : Derives Γ (OriginalOperationFrameSyntax.frame three w mode depth P a b c I J R S)) :
    Derives Γ (OriginalFormulaInductionSyntax.agreedHistory w mode depth (OriginalOperationFrameSyntax.parameter three P S) R S a b a c n) :=
  OriginalUniformInductionRules.agreed_history_at_frame hZ three w n mode depth P a b c I J R S hw hn (all_frames_ih hZ three w n hw) hf

end PPAC.Migration.Internal.OriginalFormulaCorrectnessInduction
