import PPAC.Migration.ObjectOrdinalComparison

/-! 任意内部序数集合、包含上界和最小上界的纯成员公式。 -/
namespace PPAC.Migration.OrdinalFamilySyntax
open Source SourceAlgebra OrdinalSyntax RestrictionSyntax InsertSyntax

def ordinals {m} (c : Fin m) : Formula m := .all
  ((Formula.mem (Fin.last m) c.castSucc).imp (ordinal (Fin.last m)))

def upperBound {m} (c b : Fin m) : Formula m := .all
  ((Formula.mem (Fin.last m) c.castSucc).imp (subset (Fin.last m) b.castSucc))

/-- 最小性针对全部内部集合上界，不要求上界本身是序数。 -/
def leastUpper {m} (u c : Fin m) : Formula m := (upperBound c u).conj
  (.all ((upperBound c.castSucc (Fin.last m)).imp (subset u.castSucc (Fin.last m))))

def ordinalUnionExists {m} (c : Fin m) : Formula m := .ex
  ((unionOf (Fin.last m) c.castSucc).conj ((ordinal (Fin.last m)).conj (leastUpper (Fin.last m) c.castSucc)))

theorem ordinals_rename {m k} (c : Fin m) (ρ : Fin m → Fin k) :
    (ordinals c).rename ρ = ordinals (ρ c) := by
  simp only [ordinals, Formula.rename, ordinal_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem upperBound_rename {m k} (c b : Fin m) (ρ : Fin m → Fin k) :
    (upperBound c b).rename ρ = upperBound (ρ c) (ρ b) := by
  simp only [upperBound, Formula.rename, subset_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem leastUpper_rename {m k} (u c : Fin m) (ρ : Fin m → Fin k) :
    (leastUpper u c).rename ρ = leastUpper (ρ u) (ρ c) := by
  simp only [leastUpper, Formula.rename, upperBound_rename, subset_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem ordinalUnionExists_rename {m k} (c : Fin m) (ρ : Fin m → Fin k) :
    (ordinalUnionExists c).rename ρ = ordinalUnionExists (ρ c) := by
  simp only [ordinalUnionExists, Formula.rename, unionOf_rename, ordinal_rename, leastUpper_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem ordinals_at {m} {Γ : Context m} (c a : Fin m) (hc : Derives Γ (ordinals c)) :
    Derives Γ ((Formula.mem a c).imp (ordinal a)) := by
  have hi := Derives.allE a hc
  simpa only [Formula.instantiate, Formula.rename, ordinal_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi

theorem upperBound_at {m} {Γ : Context m} (c b a : Fin m) (hc : Derives Γ (upperBound c b)) :
    Derives Γ ((Formula.mem a c).imp (subset a b)) := by
  have hi := Derives.allE a hc
  simpa only [Formula.instantiate, Formula.rename, subset_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi

theorem leastUpper_at {m} {Γ : Context m} (u c b : Fin m) (hu : Derives Γ (leastUpper u c)) :
    Derives Γ ((upperBound c b).imp (subset u b)) := by
  have hi := Derives.allE b (Derives.conjR hu)
  simpa only [Formula.instantiate, Formula.rename, subset_rename, upperBound_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi
end PPAC.Migration.OrdinalFamilySyntax
