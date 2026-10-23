import PPAC.Migration.Internal.HornLookupExecution

/-! 任意内部轨迹的原lookup可靠性成员归纳性质，量化全部索引/输出/行。 -/
namespace PPAC.Migration.Internal.HornLookupSoundSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax HornLookupRowSyntax
open SyntaxRenameQuerySyntax (of_eq)

def property {m} (w R n : Fin m) : Formula m := .all (.all (.all
  (((row w.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2))).conj
    (.mem (Fin.last (m+2)) R.castSucc.castSucc.castSucc)).imp
      (LookupTableExecutionSyntax.executed w.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc))))

def earlier {m} (w R n : Fin m) : Formula m := .all
  (((Formula.mem (Fin.last m) w.castSucc).conj (.mem (Fin.last m) n.castSucc)).imp (property w.castSucc R.castSucc (Fin.last m)))

def closed {m} (w R : Fin m) : Formula m := .all
  ((Formula.mem (Fin.last m) R.castSucc).imp (HornStepSyntax.originalStep w.castSucc (Fin.last m) R.castSucc))

theorem property_rename {m k} (w R n : Fin m) (ρ : Fin m → Fin k) :
    (property w R n).rename ρ = property (ρ w) (ρ R) (ρ n) := by
  simp only [property, Formula.rename, row_rename, LookupTableExecutionSyntax.executed_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem earlier_rename {m k} (w R n : Fin m) (ρ : Fin m → Fin k) :
    (earlier w R n).rename ρ = earlier (ρ w) (ρ R) (ρ n) := by
  simp only [earlier, Formula.rename, property_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem closed_rename {m k} (w R : Fin m) (ρ : Fin m → Fin k) :
    (closed w R).rename ρ = closed (ρ w) (ρ R) := by
  simp only [closed, Formula.rename, HornStepSyntax.originalStep_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem property_at {m} {Γ : Context m} (w R n i y r : Fin m) (hp : Derives Γ (property w R n))
    (hc : Derives Γ (row w n i y r)) (hm : Derives Γ (.mem r R)) : Derives Γ (LookupTableExecutionSyntax.executed w n i y) := by
  have hh : Derives Γ (((row w n i y r).conj (.mem r R)).imp (LookupTableExecutionSyntax.executed w n i y)) := of_eq
    (by simp only [Formula.instantiate, Formula.rename, row_rename, LookupTableExecutionSyntax.executed_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
    (Derives.allE r (Derives.allE y (Derives.allE i hp)))
  exact .impE hh (.conjI hc hm)

theorem earlier_at {m} {Γ : Context m} (w R n t i y r : Fin m) (he : Derives Γ (earlier w R n))
    (ht : Derives Γ (.mem t w)) (htn : Derives Γ (.mem t n))
    (hc : Derives Γ (row w t i y r)) (hm : Derives Γ (.mem r R)) : Derives Γ (LookupTableExecutionSyntax.executed w t i y) := by
  have hh : Derives Γ (((Formula.mem t w).conj (.mem t n)).imp (property w R t)) := of_eq
    (by simp only [Formula.instantiate, Formula.rename, property_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (Derives.allE t he)
  exact property_at w R t i y r (.impE hh (.conjI ht htn)) hc hm

theorem closed_at {m} {Γ : Context m} (w R r : Fin m) (hc : Derives Γ (closed w R)) (hm : Derives Γ (.mem r R)) :
    Derives Γ (HornStepSyntax.originalStep w r R) := by
  have hh : Derives Γ ((Formula.mem r R).imp (HornStepSyntax.originalStep w r R)) := of_eq
    (by simp only [Formula.instantiate, Formula.rename, HornStepSyntax.originalStep_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (Derives.allE r hc)
  exact .impE hh hm

end PPAC.Migration.Internal.HornLookupSoundSyntax
