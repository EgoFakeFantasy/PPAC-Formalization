import PPAC.Migration.Internal.HornApplicationRange

/-! Exact all-candidate original application laws, with the literal radix internally existentially bound. -/
namespace PPAC.Migration.Internal.PacketAffineApplicationLawSyntax
open Source SourceAlgebra SourceLogic HornBinderSyntax PacketAffineApplicationSyntax
open PacketAffineRuleData (baseRule stepRule)

def baseAt {m} (wide : Bool) (w B r V : Fin m) : Formula m :=
  (HornApplicationSyntax.application (baseRule wide) w r V).iff (baseOutcome wide w B r)

def stepAt {m} (wide : Bool) (w B r V : Fin m) : Formula m :=
  (HornApplicationSyntax.application (stepRule wide) w r V).iff (stepOutcome wide w B V r)

def lawBody {m} (wide : Bool) (w B : Fin m) : Formula (m+2) :=
  (baseAt wide (old 2 w) (old 2 B) (slot 2 0) (slot 2 1)).conj
    (stepAt wide (old 2 w) (old 2 B) (slot 2 0) (slot 2 1))

def allLaw {m} (wide : Bool) (w B : Fin m) : Formula m := OriginalUniversalBlock.allMany 2 (lawBody wide w B)

def system {m} (wide : Bool) (w B : Fin m) : Formula m :=
  (PacketAffineLiteralSyntax.frame wide w B).conj (allLaw wide w B)

def existsSystem {m} (wide : Bool) (w : Fin m) : Formula m := .ex (system wide w.castSucc (Fin.last m))

theorem baseAt_rename {m j} (wide : Bool) (w B r V : Fin m) (ρ : Fin m → Fin j) :
    (baseAt wide w B r V).rename ρ = baseAt wide (ρ w) (ρ B) (ρ r) (ρ V) := by
  simp only [baseAt, Formula.iff, Formula.rename, HornApplicationSyntax.application_rename, baseOutcome_rename]

theorem stepAt_rename {m j} (wide : Bool) (w B r V : Fin m) (ρ : Fin m → Fin j) :
    (stepAt wide w B r V).rename ρ = stepAt wide (ρ w) (ρ B) (ρ r) (ρ V) := by
  simp only [stepAt, Formula.iff, Formula.rename, HornApplicationSyntax.application_rename, stepOutcome_rename]

theorem lawBody_lift {m j} (wide : Bool) (w B : Fin m) (ρ : Fin m → Fin j) :
    (lawBody wide w B).rename (lift 2 ρ) = lawBody wide (ρ w) (ρ B) := by
  simp only [lawBody, Formula.rename, baseAt_rename, stepAt_rename, lift_old, lift_slot]

theorem allLaw_rename {m j} (wide : Bool) (w B : Fin m) (ρ : Fin m → Fin j) :
    (allLaw wide w B).rename ρ = allLaw wide (ρ w) (ρ B) := by
  simp only [allLaw, OriginalUniversalBlock.allMany_rename, lawBody_lift]

theorem system_rename {m j} (wide : Bool) (w B : Fin m) (ρ : Fin m → Fin j) :
    (system wide w B).rename ρ = system wide (ρ w) (ρ B) := by
  simp only [system, Formula.rename, PacketAffineLiteralSyntax.frame_rename, allLaw_rename]

theorem existsSystem_rename {m j} (wide : Bool) (w : Fin m) (ρ : Fin m → Fin j) :
    (existsSystem wide w).rename ρ = existsSystem wide (ρ w) := by
  simp only [existsSystem, Formula.rename, system_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

end PPAC.Migration.Internal.PacketAffineApplicationLawSyntax
