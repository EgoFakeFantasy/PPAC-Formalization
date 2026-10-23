import PPAC.Migration.Internal.StrictLookupDomainInduction

/-! 严格成功值和对全部内部候选的唯一性；没有成功时不会制造默认零结果。 -/
namespace PPAC.Migration.Internal.StrictLookupValueSyntax
open Source SourceAlgebra SourceLogic StrictLookupSyntax
open SyntaxRenameQuerySyntax (of_eq)

def uniqueOutput {m} (w n i y : Fin m) : Formula m := .all
  ((returned w.castSucc n.castSucc i.castSucc (Fin.last m)).imp (.equal (Fin.last m) y.castSucc))

def value {m} (w n i y : Fin m) : Formula m :=
  (returned w n i y).conj ((Formula.mem y w).conj (uniqueOutput w n i y))

def fiber {m} (w n i : Fin m) : Formula m := .ex
  (value w.castSucc n.castSucc i.castSucc (Fin.last m))

theorem uniqueOutput_rename {m k} (w n i y : Fin m) (ρ : Fin m → Fin k) :
    (uniqueOutput w n i y).rename ρ = uniqueOutput (ρ w) (ρ n) (ρ i) (ρ y) := by
  simp only [uniqueOutput, Formula.rename, returned_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem value_rename {m k} (w n i y : Fin m) (ρ : Fin m → Fin k) :
    (value w n i y).rename ρ = value (ρ w) (ρ n) (ρ i) (ρ y) := by
  simp only [value, Formula.rename, returned_rename, uniqueOutput_rename]

theorem fiber_rename {m k} (w n i : Fin m) (ρ : Fin m → Fin k) :
    (fiber w n i).rename ρ = fiber (ρ w) (ρ n) (ρ i) := by
  simp only [fiber, Formula.rename, value_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_fiber {m} {Γ : Context m} (w n i y : Fin m) (hy : Derives Γ (value w n i y)) :
    Derives Γ (fiber w n i) := by
  apply Derives.exI y
  exact of_eq (by simp only [Formula.instantiate, value_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hy

end PPAC.Migration.Internal.StrictLookupValueSyntax
