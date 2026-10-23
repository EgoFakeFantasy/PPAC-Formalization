import PPAC.Migration.Internal.WeakenFreeProgramCorrectness

/-! 受检程序的实际结果及比较全部内部候选的唯一纤维。 -/
namespace PPAC.Migration.Internal.WeakenFreeProgramValueSyntax
open Source SourceAlgebra SourceLogic WeakenFreeProgramSyntax

def inputGuard {m} (w a b B n : Fin m) : Formula m :=
  (FormulaCodeSyntax.formulaCode w n a b).conj (OmegaSyntax.successor B b)

theorem inputGuard_rename {m k} (w a b B n : Fin m) (ρ : Fin m → Fin k) :
    (inputGuard w a b B n).rename ρ = inputGuard (ρ w) (ρ a) (ρ b) (ρ B) (ρ n) := by
  simp only [inputGuard, Formula.rename, FormulaCodeSyntax.formulaCode_rename, OmegaSyntax.successor_rename]

def uniqueOutput {m} (w a b B n q : Fin m) : Formula m := .all
  ((executed w.castSucc a.castSucc b.castSucc B.castSucc n.castSucc (Fin.last m)).imp (.equal (Fin.last m) q.castSucc))

def value {m} (w a b B n q : Fin m) : Formula m :=
  (executed w a b B n q).conj ((FormulaCodeSyntax.formulaCode w q a B).conj
    ((Formula.mem q w).conj (uniqueOutput w a b B n q)))

def fiber {m} (w a b B n : Fin m) : Formula m := .ex
  (value w.castSucc a.castSucc b.castSucc B.castSucc n.castSucc (Fin.last m))

theorem uniqueOutput_rename {m k} (w a b B n q : Fin m) (ρ : Fin m → Fin k) :
    (uniqueOutput w a b B n q).rename ρ = uniqueOutput (ρ w) (ρ a) (ρ b) (ρ B) (ρ n) (ρ q) := by
  simp only [uniqueOutput, Formula.rename, executed_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem value_rename {m k} (w a b B n q : Fin m) (ρ : Fin m → Fin k) :
    (value w a b B n q).rename ρ = value (ρ w) (ρ a) (ρ b) (ρ B) (ρ n) (ρ q) := by
  simp only [value, Formula.rename, executed_rename, FormulaCodeSyntax.formulaCode_rename, uniqueOutput_rename]

theorem fiber_rename {m k} (w a b B n : Fin m) (ρ : Fin m → Fin k) :
    (fiber w a b B n).rename ρ = fiber (ρ w) (ρ a) (ρ b) (ρ B) (ρ n) := by
  simp only [fiber, Formula.rename, value_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_fiber {m} {Γ : Context m} (w a b B n q : Fin m) (hq : Derives Γ (value w a b B n q)) :
    Derives Γ (fiber w a b B n) := by
  apply Derives.exI q
  exact SyntaxRenameQuerySyntax.of_eq (by simp only [Formula.instantiate, value_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hq

def actualState {m} (w a b n : Fin m) : Formula m := .ex
  ((OmegaSyntax.successor (Fin.last m) b.castSucc).conj
    (fiber w.castSucc a.castSucc b.castSucc (Fin.last m) n.castSucc))

theorem actualState_rename {m k} (w a b n : Fin m) (ρ : Fin m → Fin k) :
    (actualState w a b n).rename ρ = actualState (ρ w) (ρ a) (ρ b) (ρ n) := by
  simp only [actualState, Formula.rename, OmegaSyntax.successor_rename, fiber_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

end PPAC.Migration.Internal.WeakenFreeProgramValueSyntax
