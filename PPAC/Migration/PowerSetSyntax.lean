import PPAC.Migration.ObjectTransfiniteRecursion

/-! 原PowerSet的纯成员/等词展开；没有新增函数符号。 -/
namespace PPAC.Migration.PowerSetSyntax
open Source SourceAlgebra SourceLogic RestrictionSyntax

def powerOf {m} (w v : Fin m) : Formula m := .all
  ((Formula.mem (Fin.last m) w.castSucc).iff (subset (Fin.last m) v.castSucc))

def powerExists {m} (v : Fin m) : Formula m := .ex (powerOf (Fin.last m) v.castSucc)

theorem powerOf_rename {m k} (w v : Fin m) (r : Fin m → Fin k) :
    (powerOf w v).rename r = powerOf (r w) (r v) := by
  simp only [powerOf, Formula.rename, Formula.iff, subset_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem powerExists_rename {m k} (v : Fin m) (r : Fin m → Fin k) :
    (powerExists v).rename r = powerExists (r v) := by
  simp only [powerExists, Formula.rename, powerOf_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem power_core : Source.SetLanguage.powerSet = (powerExists (0 : Fin 1)).close := rfl

theorem power_instance {m} {Γ : Context m} (v : Fin m)
    (hp : Derives Γ (Source.SetLanguage.powerSet.rename Fin.elim0)) : Derives Γ (powerExists v) := by
  rw [power_core] at hp
  have hi := specialize_close (powerExists (0 : Fin 1)) (fun _ => v) hp
  simpa only [powerExists_rename] using hi

theorem power_at {m} {Γ : Context m} (w v z : Fin m) (hp : Derives Γ (powerOf w v)) :
    Derives Γ ((Formula.mem z w).iff (subset z v)) := by
  have hi := Derives.allE z hp
  simpa only [Formula.instantiate, Formula.rename, subset_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi
end PPAC.Migration.PowerSetSyntax
