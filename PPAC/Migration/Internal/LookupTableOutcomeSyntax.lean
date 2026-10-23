import PPAC.Migration.Internal.LookupTableProgramCode

/-! Option 的对象成功图与无输出分支。未引入自造的 Option 数字封包。 -/
namespace PPAC.Migration.Internal.LookupTableOutcomeSyntax
open Source SourceAlgebra SourceLogic

def hasOutput {m} (w n i : Fin m) : Formula m := .ex
  (LookupTableExecutionSyntax.executed w.castSucc n.castSucc i.castSucc (Fin.last m))

def noOutput {m} (w n i : Fin m) : Formula m := (hasOutput w n i).neg

def uniqueOutput {m} (w n i y : Fin m) : Formula m := .all
  ((LookupTableExecutionSyntax.executed w.castSucc n.castSucc i.castSucc (Fin.last m)).imp (.equal (Fin.last m) y.castSucc))

theorem hasOutput_rename {m k} (w n i : Fin m) (ρ : Fin m → Fin k) :
    (hasOutput w n i).rename ρ = hasOutput (ρ w) (ρ n) (ρ i) := by
  simp only [hasOutput, Formula.rename, LookupTableExecutionSyntax.executed_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem noOutput_rename {m k} (w n i : Fin m) (ρ : Fin m → Fin k) :
    (noOutput w n i).rename ρ = noOutput (ρ w) (ρ n) (ρ i) := by
  simp only [noOutput, Formula.neg, Formula.rename, hasOutput_rename]

theorem uniqueOutput_rename {m k} (w n i y : Fin m) (ρ : Fin m → Fin k) :
    (uniqueOutput w n i y).rename ρ = uniqueOutput (ρ w) (ρ n) (ρ i) (ρ y) := by
  simp only [uniqueOutput, Formula.rename, LookupTableExecutionSyntax.executed_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

end PPAC.Migration.Internal.LookupTableOutcomeSyntax
