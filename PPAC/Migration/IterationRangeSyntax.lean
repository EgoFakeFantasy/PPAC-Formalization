import PPAC.Migration.IterationValueStep

/-! 精确末值集合的种子与取并封闭条件；仍是有限纯成员公式。 -/
namespace PPAC.Migration.IterationRangeSyntax
open Source SourceAlgebra SourceLogic InsertSyntax IterationValueSyntax

def closedFiber {m} (c r : Fin m) : Formula m := .ex
  ((Formula.mem (Fin.last m) c.castSucc).conj (unionOf (Fin.last m) r.castSucc))

def closedUnion {m} (c : Fin m) : Formula m := .all
  ((Formula.mem (Fin.last m) c.castSucc).imp (closedFiber c.castSucc (Fin.last m)))

theorem closedFiber_rename {m k} (c r : Fin m) (ρ : Fin m → Fin k) :
    (closedFiber c r).rename ρ = closedFiber (ρ c) (ρ r) := by
  simp only [closedFiber, Formula.rename, unionOf_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem closedUnion_rename {m k} (c : Fin m) (ρ : Fin m → Fin k) :
    (closedUnion c).rename ρ = closedUnion (ρ c) := by
  simp only [closedUnion, Formula.rename, closedFiber_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem range_at {m} {Γ : Context m} (c w z a r : Fin m) (hc : Derives Γ (IterationValueSyntax.range c w z a)) :
    Derives Γ ((Formula.mem r c).iff (imageValue w z a r)) := by
  have hi := Derives.allE r hc
  simpa only [Formula.instantiate, Formula.rename, imageValue_rename, Formula.iff, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi

theorem image_intro {m} {Γ : Context m} (w z a n r : Fin m)
    (hn : Derives Γ (.mem n w)) (hr : Derives Γ (value n z a r)) : Derives Γ (imageValue w z a r) := by
  apply Derives.exI n
  simpa only [Formula.instantiate, Formula.rename, value_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.conjI hn hr

theorem member_from_value {m} {Γ : Context m} (c w z a n r : Fin m)
    (hc : Derives Γ (IterationValueSyntax.range c w z a)) (hn : Derives Γ (.mem n w)) (hr : Derives Γ (value n z a r)) :
    Derives Γ (.mem r c) := .impE (.conjR (range_at c w z a r hc)) (image_intro w z a n r hn hr)

theorem closed_at {m} {Γ : Context m} (c r : Fin m) (hc : Derives Γ (closedUnion c)) :
    Derives Γ ((Formula.mem r c).imp (closedFiber c r)) := by
  have hi := Derives.allE r hc
  simpa only [Formula.instantiate, Formula.rename, closedFiber_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi
end PPAC.Migration.IterationRangeSyntax
