import PPAC.Migration.Internal.InstantiateFormulaCorrectnessPoint
import PPAC.Migration.SetInduction

/-! 原ZF的无界集合归纳消去统一IH；所有内部码、变化环境和候选输出均在对象公式内量化。 -/
namespace PPAC.Migration.Internal.InstantiateFormulaCorrectnessInduction
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax
open InstantiateUniformInductionSyntax
open ReplacementPredicates (paramsUp)
attribute [local irreducible] NaturalRecursionSyntax.matrix

def matrix  : Formula 2 := correct (0 : Fin 1).castSucc (Fin.last 1)

theorem matrix_pred {m}  (ρ : Fin 1 → Fin m) (x : Fin m) :
    MinimalPredicates.pred (matrix ) ρ x = correct (ρ 0) x := by
  simp only [matrix, MinimalPredicates.pred, correct_rename, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem progressive {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w : Fin m) (hw : Derives Γ (omega w)) :
    Derives Γ (SetInductionSyntax.progressive (matrix ) (fun _ : Fin 1 => w)) := by
  simp only [SetInductionSyntax.progressive, SetInductionSyntax.below, matrix_pred, paramsUp]
  apply Derives.allI
  apply Derives.impI
  let I := allFramesIH w.castSucc (Fin.last m)
  let Δ := Context.add I (Context.image Formula.raise Γ)
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw I)
  exact InstantiateFormulaCorrectnessPoint.correct_from_induction (ZFContext.under hZ I) w.castSucc (Fin.last m) hw1 (.hyp (Or.inl rfl))

theorem all_correct {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w : Fin m) (hw : Derives Γ (omega w)) :
    Derives Γ (.all (correct w.castSucc (Fin.last m))) := by
  have hh := SetInduction.all_holds (matrix ) (fun _ : Fin 1 => w)
    (ZFContext.separation hZ (matrix ).neg) (ZFContext.arithmetic hZ).base.foundation
    (ZFContext.closed hZ ObjectTransitiveCover.source_cover) (progressive hZ w hw)
  exact of_eq (by simp only [SetInductionSyntax.holds, matrix_pred, paramsUp]) hh

theorem at_root {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w n : Fin m) (hw : Derives Γ (omega w)) : Derives Γ (correct w n) :=
  of_eq (by simp only [Formula.instantiate, correct_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
    (Derives.allE n (all_correct hZ w hw))

theorem all_frames_ih {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w n : Fin m) (hw : Derives Γ (omega w)) : Derives Γ (allFramesIH w n) := by
  apply Derives.allI
  apply Derives.impI
  let M := Formula.mem (Fin.last m) n.castSucc
  have hw1 : Derives (Context.add M (Context.image Formula.raise Γ)) (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw M)
  exact at_root (ZFContext.under hZ M) w.castSucc (Fin.last m) hw1

theorem run_iff_execution {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w n mode depth P a b c e R S q : Fin m) (hw : Derives Γ (omega w))
    (hf : Derives Γ (InstantiateOperationFrameSyntax.frame w mode depth P a b c e R S))
    (hn : Derives Γ (FormulaCodeSyntax.formulaCode w n a b)) :
    Derives Γ ((OriginalTransformRowSyntax.run 3 w mode depth P n q).iff
      (FormulaTransformExecutionSyntax.executed w R S a b c e n q)) :=
  correct_at w n mode depth P a b c e R S q (at_root hZ w n hw) hf hn

theorem actual_history_agreement {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w n mode depth P a b c e R S h : Fin m) (hw : Derives Γ (omega w))
    (ho : Derives Γ (OrdinalSyntax.ordinal n))
    (hg : Derives Γ (FormulaTransformRecursionSyntax.graph w h n))
    (hf : Derives Γ (InstantiateOperationFrameSyntax.frame w mode depth P a b c e R S)) :
    Derives Γ (OriginalFormulaHistoryAgreementSyntax.agreement w mode depth P h R S a b c e n) :=
  InstantiateUniformInductionRules.agreement_at_frame hZ w n mode depth P a b c e R S h hw ho hg (all_frames_ih hZ w n hw) hf

theorem run_iff_program {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w n mode depth P a b c e R S h q : Fin m) (hw : Derives Γ (omega w))
    (hf : Derives Γ (InstantiateOperationFrameSyntax.frame w mode depth P a b c e R S))
    (hn : Derives Γ (FormulaCodeSyntax.formulaCode w n a b))
    (hg : Derives Γ (FormulaTransformRecursionSyntax.graph w h n)) :
    Derives Γ ((OriginalTransformRowSyntax.run 3 w mode depth P n q).iff
      (FormulaTransformProgramSyntax.run FormulaTransformProgramSyntax.formulaProgram w R S a b c e h n q)) :=
  InstantiateFullFormulaProgram.program_iff hZ w n mode depth P a b c e R S h q hw (all_frames_ih hZ w n hw) hf hn hg

theorem agreed_history_exists {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w n mode depth P a b c e R S : Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (FormulaCodeSyntax.formulaCode w n a b))
    (hf : Derives Γ (InstantiateOperationFrameSyntax.frame w mode depth P a b c e R S)) :
    Derives Γ (OriginalFormulaInductionSyntax.agreedHistory w mode depth P R S a b c e n) :=
  InstantiateUniformInductionRules.agreed_history_at_frame hZ w n mode depth P a b c e R S hw hn (all_frames_ih hZ w n hw) hf

end PPAC.Migration.Internal.InstantiateFormulaCorrectnessInduction
