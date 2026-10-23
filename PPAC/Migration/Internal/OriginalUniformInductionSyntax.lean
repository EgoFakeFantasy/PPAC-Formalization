import PPAC.Migration.Internal.OriginalUniversalBlock

/-! 对全部十个变化环境参数及任意输出量化的对象正确性与严格成员归纳假设。 -/
namespace PPAC.Migration.Internal.OriginalUniformInductionSyntax
open Source SourceAlgebra SourceLogic HornBinderSyntax OriginalUniversalBlock
open SyntaxRenameQuerySyntax (of_eq)

def correctAt {m} (three : Bool) (w n mode depth P a b c I J R S q : Fin m) : Formula m :=
  (OriginalOperationFrameSyntax.frame three w mode depth P a b c I J R S).imp
    ((FormulaCodeSyntax.formulaCode w n a b).imp
      ((OriginalTransformRowSyntax.run 3 w mode depth (OriginalOperationFrameSyntax.parameter three P S) n q).iff
        (FormulaTransformExecutionSyntax.executed w R S a b a c n q)))

theorem correctAt_rename {m j} (three : Bool) (w n mode depth P a b c I J R S q : Fin m) (ρ : Fin m → Fin j) :
    (correctAt three w n mode depth P a b c I J R S q).rename ρ = correctAt three (ρ w) (ρ n) (ρ mode) (ρ depth) (ρ P) (ρ a) (ρ b) (ρ c) (ρ I) (ρ J) (ρ R) (ρ S) (ρ q) := by
  simp only [correctAt, Formula.rename, Formula.iff, OriginalOperationFrameSyntax.frame_rename, FormulaCodeSyntax.formulaCode_rename, OriginalTransformRowSyntax.run_rename, OriginalOperationFrameSyntax.parameter_map, FormulaTransformExecutionSyntax.executed_rename]

def parameters {m} (mode depth P a b c I J R S q : Fin m) : Fin 11 → Fin m := Fin.cases mode (Fin.cases depth (Fin.cases P (Fin.cases a (Fin.cases b (Fin.cases c (Fin.cases I (Fin.cases J (Fin.cases R (Fin.cases S (Fin.cases q (Fin.elim0)))))))))))

def body {m} (three : Bool) (w n : Fin m) : Formula (m+11) :=
  correctAt three (old 11 w) (old 11 n) (slot 11 0) (slot 11 1) (slot 11 2) (slot 11 3) (slot 11 4) (slot 11 5) (slot 11 6) (slot 11 7) (slot 11 8) (slot 11 9) (slot 11 10)

def correct {m} (three : Bool) (w n : Fin m) : Formula m := allMany 11 (body three w n)

theorem body_lift {m j} (three : Bool) (w n : Fin m) (ρ : Fin m → Fin j) :
    (body three w n).rename (lift 11 ρ) = body three (ρ w) (ρ n) := by
  simp only [body, correctAt_rename, lift_old, lift_slot]

theorem correct_rename {m j} (three : Bool) (w n : Fin m) (ρ : Fin m → Fin j) :
    (correct three w n).rename ρ = correct three (ρ w) (ρ n) := by
  simp only [correct, allMany_rename, body_lift]

theorem correct_at {m} {Γ : Context m} (three : Bool) (w n mode depth P a b c I J R S q : Fin m)
    (hc : Derives Γ (correct three w n))
    (hf : Derives Γ (OriginalOperationFrameSyntax.frame three w mode depth P a b c I J R S))
    (hn : Derives Γ (FormulaCodeSyntax.formulaCode w n a b)) :
    Derives Γ ((OriginalTransformRowSyntax.run 3 w mode depth (OriginalOperationFrameSyntax.parameter three P S) n q).iff
      (FormulaTransformExecutionSyntax.executed w R S a b a c n q)) := by
  have hi := at_many 11 (body three w n) (parameters mode depth P a b c I J R S q) hc
  have he : Derives Γ (correctAt three w n mode depth P a b c I J R S q) :=
    of_eq (by simp only [body, correctAt_rename, assign_old, assign_slot]; rfl) hi
  exact .impE (.impE he hf) hn

def allFramesIH {m} (three : Bool) (w n : Fin m) : Formula m := .all
  ((Formula.mem (Fin.last m) n.castSucc).imp (correct three w.castSucc (Fin.last m)))

theorem allFramesIH_rename {m j} (three : Bool) (w n : Fin m) (ρ : Fin m → Fin j) :
    (allFramesIH three w n).rename ρ = allFramesIH three (ρ w) (ρ n) := by
  simp only [allFramesIH, Formula.rename, correct_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem allFramesIH_at {m} {Γ : Context m} (three : Bool) (w n x : Fin m)
    (hi : Derives Γ (allFramesIH three w n)) (hx : Derives Γ (.mem x n)) : Derives Γ (correct three w x) := by
  have he : Derives Γ ((Formula.mem x n).imp (correct three w x)) :=
    of_eq (by simp only [Formula.instantiate, Formula.rename, correct_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (Derives.allE x hi)
  exact .impE he hx

end PPAC.Migration.Internal.OriginalUniformInductionSyntax
