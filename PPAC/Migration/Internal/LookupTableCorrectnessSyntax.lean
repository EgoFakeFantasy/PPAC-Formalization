import PPAC.Migration.Internal.LookupTableRecursive

/-! 按表码的对象成员归纳合同，内部全称量化全部索引和候选输出。 -/
namespace PPAC.Migration.Internal.LookupTableCorrectnessSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax
open SyntaxRenameQuerySyntax (of_eq)

def property {m} (w n : Fin m) : Formula m := .all (.all
  ((Formula.mem (Fin.last m).castSucc w.castSucc.castSucc).imp
    ((LookupTableExecutionSyntax.executed w.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).iff
      (StrictLookupSyntax.returned w.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))))))

def earlier {m} (w n : Fin m) : Formula m := .all
  (((Formula.mem (Fin.last m) w.castSucc).conj (.mem (Fin.last m) n.castSucc)).imp (property w.castSucc (Fin.last m)))

theorem property_rename {m k} (w n : Fin m) (ρ : Fin m → Fin k) :
    (property w n).rename ρ = property (ρ w) (ρ n) := by
  simp only [property, Formula.rename, Formula.iff, LookupTableExecutionSyntax.executed_rename, StrictLookupSyntax.returned_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem earlier_rename {m k} (w n : Fin m) (ρ : Fin m → Fin k) :
    (earlier w n).rename ρ = earlier (ρ w) (ρ n) := by
  simp only [earlier, Formula.rename, property_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem property_at {m} {Γ : Context m} (w n i y : Fin m) (hp : Derives Γ (property w n)) (hi : Derives Γ (.mem i w)) :
    Derives Γ ((LookupTableExecutionSyntax.executed w n i y).iff (StrictLookupSyntax.returned w n i y)) := by
  have hh : Derives Γ ((Formula.mem i w).imp ((LookupTableExecutionSyntax.executed w n i y).iff (StrictLookupSyntax.returned w n i y))) := of_eq
    (by simp only [Formula.instantiate, Formula.rename, Formula.iff, LookupTableExecutionSyntax.executed_rename, StrictLookupSyntax.returned_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
    (Derives.allE y (Derives.allE i hp))
  exact .impE hh hi

theorem earlier_at {m} {Γ : Context m} (w n t j y : Fin m) (he : Derives Γ (earlier w n))
    (ht : Derives Γ (.mem t w)) (htn : Derives Γ (.mem t n)) (hj : Derives Γ (.mem j w)) :
    Derives Γ ((LookupTableExecutionSyntax.executed w t j y).iff (StrictLookupSyntax.returned w t j y)) := by
  have hh : Derives Γ (((Formula.mem t w).conj (.mem t n)).imp (property w t)) := of_eq
    (by simp only [Formula.instantiate, Formula.rename, property_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (Derives.allE t he)
  exact property_at w t j y (.impE hh (.conjI ht htn)) hj

end PPAC.Migration.Internal.LookupTableCorrectnessSyntax
