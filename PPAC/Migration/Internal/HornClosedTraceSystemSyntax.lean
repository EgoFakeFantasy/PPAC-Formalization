import PPAC.Migration.Internal.PacketAffineDispatch

/-! One actual internal trace gives closure and unfolding for every internal root candidate. -/
namespace PPAC.Migration.Internal.HornClosedTraceSystemSyntax
open Source SourceAlgebra SourceLogic
open YesMetaZFC.Automation.ObjectHorn (Rule)

def lawBody {m} (rules : List Rule) (w V : Fin m) : Formula (m+1) :=
  (HornClosedTraceSyntax.condition rules w.castSucc (Fin.last m)).iff
    (HornStepSyntax.step rules w.castSucc (Fin.last m) V.castSucc)

def allLaw {m} (rules : List Rule) (w V : Fin m) : Formula m := .all (lawBody rules w V)

def system {m} (rules : List Rule) (w V : Fin m) : Formula m :=
  (HornClosedTraceValueSyntax.value rules w V).conj
    ((HornClosedTraceSyntax.closed rules w V).conj (allLaw rules w V))

def existsSystem {m} (rules : List Rule) (w : Fin m) : Formula m := .ex (system rules w.castSucc (Fin.last m))

theorem lawBody_lift {m j} (rules : List Rule) (w V : Fin m) (ρ : Fin m → Fin j) :
    (lawBody rules w V).rename (Formula.liftRen ρ) = lawBody rules (ρ w) (ρ V) := by
  simp only [lawBody, Formula.iff, Formula.rename, HornClosedTraceSyntax.condition_rename, HornStepSyntax.step_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem allLaw_rename {m j} (rules : List Rule) (w V : Fin m) (ρ : Fin m → Fin j) :
    (allLaw rules w V).rename ρ = allLaw rules (ρ w) (ρ V) := by
  simp only [allLaw, Formula.rename, lawBody_lift]

theorem system_rename {m j} (rules : List Rule) (w V : Fin m) (ρ : Fin m → Fin j) :
    (system rules w V).rename ρ = system rules (ρ w) (ρ V) := by
  simp only [system, Formula.rename, HornClosedTraceValueSyntax.value_rename, HornClosedTraceSyntax.closed_rename, allLaw_rename]

theorem existsSystem_rename {m j} (rules : List Rule) (w : Fin m) (ρ : Fin m → Fin j) :
    (existsSystem rules w).rename ρ = existsSystem rules (ρ w) := by
  simp only [existsSystem, Formula.rename, system_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

end PPAC.Migration.Internal.HornClosedTraceSystemSyntax
