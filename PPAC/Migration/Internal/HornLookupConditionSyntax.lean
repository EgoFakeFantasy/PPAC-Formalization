import PPAC.Migration.Internal.HornLookupTraceClosed

/-! 完整原规则表关系式编译的任意内部ω子集轨迹条件；不限定为宿主有限轨迹。 -/
namespace PPAC.Migration.Internal.HornLookupConditionSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax HornLookupSoundSyntax
open SyntaxRenameQuerySyntax (of_eq)

def witness {m} (w r R : Fin m) : Formula m :=
  (RestrictionSyntax.subset R w).conj ((Formula.mem r R).conj (closed w R))

def condition {m} (w r : Fin m) : Formula m := .ex (witness w.castSucc r.castSucc (Fin.last m))

theorem witness_rename {m k} (w r R : Fin m) (ρ : Fin m → Fin k) :
    (witness w r R).rename ρ = witness (ρ w) (ρ r) (ρ R) := by
  simp only [witness, Formula.rename, RestrictionSyntax.subset_rename, HornLookupSoundSyntax.closed_rename]

theorem condition_rename {m k} (w r : Fin m) (ρ : Fin m → Fin k) :
    (condition w r).rename ρ = condition (ρ w) (ρ r) := by
  simp only [condition, Formula.rename, witness_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_condition {m} {Γ : Context m} (w r R : Fin m) (hw : Derives Γ (witness w r R)) : Derives Γ (condition w r) := by
  apply Derives.exI R
  exact of_eq (by simp only [Formula.instantiate, witness_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hw

end PPAC.Migration.Internal.HornLookupConditionSyntax
