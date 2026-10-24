import PPAC.Migration.Internal.PacketStructureAcceptedForward

/-! Every actual internal field candidate remains quantified, with the original acceptance on the implication left side. -/
namespace PPAC.Migration.Internal.PacketStructureRootLawSyntax
open Source SourceAlgebra SourceLogic HornBinderSyntax PacketStructureSyntax PacketStructureAcceptedSyntax PacketStructureDispatchData

def rootLawBody {m} (f : Family) (w V : Fin m) : Formula (m+(width f+1)) :=
  (row (width f) (tag f) (old (width f+1) w) (fun i => slot (width f+1) i.castSucc) (slot (width f+1) (Fin.last (width f)))).imp
    ((PacketStructureDispatch.results false f (old (width f+1) w) (old (width f+1) V) (slot (width f+1) (Fin.last (width f)))).iff
      (PacketStructureRootSyntax.criterion f (old (width f+1) w) (old (width f+1) V) (fun i => slot (width f+1) i.castSucc)))

def allRootLaw {m} (f : Family) (w V : Fin m) : Formula m := OriginalUniversalBlock.allMany (width f+1) (rootLawBody f w V)

def acceptedLawBody {m} (f : Family) (w : Fin m) : Formula (m+width f) :=
  (accepted (width f) (tag f) (old (width f) w) (slot (width f))).imp (criterion f (old (width f) w) (slot (width f)))

def allAcceptedLaw {m} (f : Family) (w : Fin m) : Formula m := OriginalUniversalBlock.allMany (width f) (acceptedLawBody f w)

def allSystem {m} (w : Fin m) : Formula m := (allAcceptedLaw .tree w).conj ((allAcceptedLaw .forest w).conj (allAcceptedLaw .packet w))

theorem rootLawBody_lift {m j} (f : Family) (w V : Fin m) (ρ : Fin m → Fin j) :
    (rootLawBody f w V).rename (lift (width f+1) ρ) = rootLawBody f (ρ w) (ρ V) := by
  simp only [rootLawBody,Formula.iff,Formula.rename,row_rename,PacketStructureDispatch.results_rename,PacketStructureRootSyntax.criterion_rename,lift_old,lift_slot]

theorem allRootLaw_rename {m j} (f : Family) (w V : Fin m) (ρ : Fin m → Fin j) :
    (allRootLaw f w V).rename ρ = allRootLaw f (ρ w) (ρ V) := by
  simp only [allRootLaw,OriginalUniversalBlock.allMany_rename,rootLawBody_lift]

theorem acceptedLawBody_lift {m j} (f : Family) (w : Fin m) (ρ : Fin m → Fin j) :
    (acceptedLawBody f w).rename (lift (width f) ρ) = acceptedLawBody f (ρ w) := by
  simp only [acceptedLawBody,Formula.rename,accepted_rename,criterion_rename,lift_old,lift_slot]

theorem allAcceptedLaw_rename {m j} (f : Family) (w : Fin m) (ρ : Fin m → Fin j) :
    (allAcceptedLaw f w).rename ρ = allAcceptedLaw f (ρ w) := by
  simp only [allAcceptedLaw,OriginalUniversalBlock.allMany_rename,acceptedLawBody_lift]

theorem allSystem_rename {m j} (w : Fin m) (ρ : Fin m → Fin j) :
    (allSystem w).rename ρ = allSystem (ρ w) := by
  simp only [allSystem,Formula.rename,allAcceptedLaw_rename]

end PPAC.Migration.Internal.PacketStructureRootLawSyntax
