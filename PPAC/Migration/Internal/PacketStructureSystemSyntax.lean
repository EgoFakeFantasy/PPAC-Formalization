import PPAC.Migration.Internal.PacketStructureDispatch

/-! All internal root candidates remain under ALL4/ALL5/ALL3 in one canonical Packet structure system. -/
namespace PPAC.Migration.Internal.PacketStructureSystemSyntax
open Source SourceAlgebra SourceLogic HornBinderSyntax PacketStructureSyntax PacketStructureDispatchData PacketStructureDispatch
open SyntaxRenameQuerySyntax (of_eq)

def rootLaw {m} (f : Family) (w V r : Fin m) : Formula m :=
  ((PacketTraceSyntax.condition w r).iff (results true f w V r)).conj
    ((PacketTraceSyntax.condition w r).imp (results false f w V r))

def lawBody {m} (f : Family) (w V : Fin m) : Formula (m+(width f+1)) :=
  (row (width f) (tag f) (old (width f+1) w) (fun i => slot (width f+1) i.castSucc) (slot (width f+1) (Fin.last (width f)))).imp
    (rootLaw f (old (width f+1) w) (old (width f+1) V) (slot (width f+1) (Fin.last (width f))))

def allLaw {m} (f : Family) (w V : Fin m) : Formula m := OriginalUniversalBlock.allMany (width f+1) (lawBody f w V)

def system {m} (w V : Fin m) : Formula m := (PacketTraceCore.value w V).conj
  ((allLaw .tree w V).conj ((allLaw .forest w V).conj (allLaw .packet w V)))

def existsSystem {m} (w : Fin m) : Formula m := .ex (system w.castSucc (Fin.last m))

theorem rootLaw_rename {m j} (f : Family) (w V r : Fin m) (ρ : Fin m → Fin j) :
    (rootLaw f w V r).rename ρ = rootLaw f (ρ w) (ρ V) (ρ r) := by
  simp only [rootLaw,Formula.iff,Formula.rename,PacketTraceSyntax.condition_rename,results_rename]

theorem lawBody_lift {m j} (f : Family) (w V : Fin m) (ρ : Fin m → Fin j) :
    (lawBody f w V).rename (lift (width f+1) ρ) = lawBody f (ρ w) (ρ V) := by
  simp only [lawBody,Formula.rename,row_rename,rootLaw_rename,lift_old,lift_slot]

theorem allLaw_rename {m j} (f : Family) (w V : Fin m) (ρ : Fin m → Fin j) :
    (allLaw f w V).rename ρ = allLaw f (ρ w) (ρ V) := by
  simp only [allLaw,OriginalUniversalBlock.allMany_rename,lawBody_lift]

theorem system_rename {m j} (w V : Fin m) (ρ : Fin m → Fin j) :
    (system w V).rename ρ = system (ρ w) (ρ V) := by
  simp only [system,Formula.rename,PacketTraceCore.value_rename,allLaw_rename]

theorem existsSystem_rename {m j} (w : Fin m) (ρ : Fin m → Fin j) :
    (existsSystem w).rename ρ = existsSystem (ρ w) := by
  simp only [existsSystem,Formula.rename,system_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem intro_system {m} {Γ : Context m} (w V : Fin m) (hs : Derives Γ (system w V)) : Derives Γ (existsSystem w) := by
  apply Derives.exI V
  exact of_eq (by simp only [Formula.instantiate,system_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) hs

end PPAC.Migration.Internal.PacketStructureSystemSyntax
