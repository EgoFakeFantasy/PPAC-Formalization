import PPAC.Migration.Internal.LookupTableJudgment

/-! 无历史参数的表码递归判据；递归调用是新程序自身的真实执行。 -/
namespace PPAC.Migration.Internal.LookupTableRecursiveSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax
open LookupTableProgramSyntax (legal legal_rename zeroCase zeroCase_rename)
open LookupTableExecutionSyntax (executed executed_rename)
open SyntaxRenameQuerySyntax (of_eq)

def successorBody {m} (w n i y : Fin m) : Formula (m+2) :=
  (StructuralListProjectionSyntax.selected false w.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc).conj
    (((Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj (successor i.castSucc.castSucc (Fin.last (m+1)))).conj
      (executed w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) y.castSucc.castSucc))

def successorCase {m} (w n i y : Fin m) : Formula m := .ex (.ex (successorBody w n i y))

def step {m} (w n i y : Fin m) : Formula m := (zeroCase w n i y).disj (successorCase w n i y)

def criterion {m} (w n i y : Fin m) : Formula m :=
  (Formula.mem n w).conj ((legal w i y).conj (step w n i y))

theorem successorCase_rename {m k} (w n i y : Fin m) (ρ : Fin m → Fin k) :
    (successorCase w n i y).rename ρ = successorCase (ρ w) (ρ n) (ρ i) (ρ y) := by
  simp only [successorCase, successorBody, Formula.rename, StructuralListProjectionSyntax.selected_rename, successor_rename, executed_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem step_rename {m k} (w n i y : Fin m) (ρ : Fin m → Fin k) :
    (step w n i y).rename ρ = step (ρ w) (ρ n) (ρ i) (ρ y) := by
  simp only [step, Formula.rename, zeroCase_rename, successorCase_rename]

theorem criterion_rename {m k} (w n i y : Fin m) (ρ : Fin m → Fin k) :
    (criterion w n i y).rename ρ = criterion (ρ w) (ρ n) (ρ i) (ρ y) := by
  simp only [criterion, Formula.rename, legal_rename, step_rename]

theorem intro_successor {m} {Γ : Context m} (w n i y t j : Fin m)
    (ht : Derives Γ (StructuralListProjectionSyntax.selected false w n t)) (hj : Derives Γ (.mem j w))
    (hi : Derives Γ (successor i j)) (hr : Derives Γ (executed w t j y)) : Derives Γ (successorCase w n i y) := by
  apply Derives.exI t
  apply Derives.exI j
  exact of_eq (by simp only [successorBody, Formula.instantiate, Formula.rename, StructuralListProjectionSyntax.selected_rename, successor_rename, executed_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI ht (.conjI (.conjI hj hi) hr))

end PPAC.Migration.Internal.LookupTableRecursiveSyntax
