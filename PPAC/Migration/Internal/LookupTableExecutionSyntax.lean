import PPAC.Migration.Internal.LookupTableHistory
import PPAC.Migration.Internal.LookupTableOperatorMembership

/-! 独立表码递归图的真实状态执行判断；不以旧StrictLookup/Field为定义。 -/
namespace PPAC.Migration.Internal.LookupTableExecutionSyntax
open Source SourceAlgebra SourceLogic LookupTableProgramSyntax LookupTableEvaluationSyntax
open SyntaxRenameQuerySyntax (of_eq)

def body {m} (w n i y : Fin m) : Formula (m+1) :=
  (evaluation w.castSucc n.castSucc (Fin.last m)).conj (contains w.castSucc (Fin.last m) i.castSucc y.castSucc)

def executed {m} (w n i y : Fin m) : Formula m := (Formula.mem n w).conj (.ex (body w n i y))

theorem executed_rename {m k} (w n i y : Fin m) (ρ : Fin m → Fin k) :
    (executed w n i y).rename ρ = executed (ρ w) (ρ n) (ρ i) (ρ y) := by
  simp only [executed, body, Formula.rename, evaluation_rename, contains_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_executed {m} {Γ : Context m} (w n i y v : Fin m) (hn : Derives Γ (.mem n w))
    (hv : Derives Γ (evaluation w n v)) (hc : Derives Γ (contains w v i y)) : Derives Γ (executed w n i y) := by
  apply Derives.conjI hn
  apply Derives.exI v
  exact of_eq (by simp only [body, Formula.instantiate, Formula.rename, evaluation_rename, contains_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hv hc)

end PPAC.Migration.Internal.LookupTableExecutionSyntax
