import PPAC.Migration.Internal.InstantiateFrameAtomic
import PPAC.Migration.Internal.OriginalUniversalBlock

/-! mode2全内部统一归纳：十个变化frame参数及候选输出在对象ALL中，源／目标绑定界独立。 -/
namespace PPAC.Migration.Internal.InstantiateUniformInductionSyntax
open Source SourceAlgebra SourceLogic HornBinderSyntax OriginalUniversalBlock
open SyntaxRenameQuerySyntax (of_eq)

def correctAt {m} (w n mode depth P a b c e R S q : Fin m) : Formula m :=
  (InstantiateOperationFrameSyntax.frame w mode depth P a b c e R S).imp
    ((FormulaCodeSyntax.formulaCode w n a b).imp
      ((OriginalTransformRowSyntax.run 3 w mode depth P n q).iff
        (FormulaTransformExecutionSyntax.executed w R S a b c e n q)))

theorem correctAt_rename {m j} (w n mode depth P a b c e R S q : Fin m) (ρ : Fin m → Fin j) :
    (correctAt w n mode depth P a b c e R S q).rename ρ = correctAt (ρ w) (ρ n) (ρ mode) (ρ depth) (ρ P) (ρ a) (ρ b) (ρ c) (ρ e) (ρ R) (ρ S) (ρ q) := by
  simp only [correctAt, Formula.rename, Formula.iff, InstantiateOperationFrameSyntax.frame_rename, FormulaCodeSyntax.formulaCode_rename, OriginalTransformRowSyntax.run_rename, FormulaTransformExecutionSyntax.executed_rename]

def parameters {m} (mode depth P a b c e R S q : Fin m) : Fin 10 → Fin m :=
  Fin.cases mode (Fin.cases depth (Fin.cases P (Fin.cases a (Fin.cases b (Fin.cases c (Fin.cases e (Fin.cases R (Fin.cases S (Fin.cases q Fin.elim0)))))))))

def body {m} (w n : Fin m) : Formula (m+10) :=
  correctAt (old 10 w) (old 10 n) (slot 10 0) (slot 10 1) (slot 10 2) (slot 10 3) (slot 10 4) (slot 10 5) (slot 10 6) (slot 10 7) (slot 10 8) (slot 10 9)

def correct {m} (w n : Fin m) : Formula m := allMany 10 (body w n)

theorem body_lift {m j} (w n : Fin m) (ρ : Fin m → Fin j) :
    (body w n).rename (lift 10 ρ) = body (ρ w) (ρ n) := by
  simp only [body, correctAt_rename, lift_old, lift_slot]

theorem correct_rename {m j} (w n : Fin m) (ρ : Fin m → Fin j) :
    (correct w n).rename ρ = correct (ρ w) (ρ n) := by
  simp only [correct, allMany_rename, body_lift]

theorem correct_at {m} {Γ : Context m} (w n mode depth P a b c e R S q : Fin m)
    (hc : Derives Γ (correct w n))
    (hf : Derives Γ (InstantiateOperationFrameSyntax.frame w mode depth P a b c e R S))
    (hn : Derives Γ (FormulaCodeSyntax.formulaCode w n a b)) :
    Derives Γ ((OriginalTransformRowSyntax.run 3 w mode depth P n q).iff (FormulaTransformExecutionSyntax.executed w R S a b c e n q)) := by
  have hi := at_many 10 (body w n) (parameters mode depth P a b c e R S q) hc
  have he : Derives Γ (correctAt w n mode depth P a b c e R S q) := of_eq
    (by simp only [body, correctAt_rename, assign_old, assign_slot]; rfl) hi
  exact .impE (.impE he hf) hn

def allFramesIH {m} (w n : Fin m) : Formula m := .all
  ((Formula.mem (Fin.last m) n.castSucc).imp (correct w.castSucc (Fin.last m)))

theorem allFramesIH_rename {m j} (w n : Fin m) (ρ : Fin m → Fin j) :
    (allFramesIH w n).rename ρ = allFramesIH (ρ w) (ρ n) := by
  simp only [allFramesIH, Formula.rename, correct_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem allFramesIH_at {m} {Γ : Context m} (w n x : Fin m)
    (hi : Derives Γ (allFramesIH w n)) (hx : Derives Γ (.mem x n)) : Derives Γ (correct w x) := by
  have he : Derives Γ ((Formula.mem x n).imp (correct w x)) := of_eq
    (by simp only [Formula.instantiate, Formula.rename, correct_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (Derives.allE x hi)
  exact .impE he hx

end PPAC.Migration.Internal.InstantiateUniformInductionSyntax
