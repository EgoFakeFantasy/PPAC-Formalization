import PPAC.Migration.Internal.PacketStructureSearchAccepted

/-! Exact structural recursion quantifies every internal candidate and retains all original naturality guards. -/
namespace PPAC.Migration.Internal.PacketStructureSearchLawSyntax
open Source SourceAlgebra SourceLogic HornBinderSyntax HornExprSyntax PacketStructureSyntax PacketStructureAcceptedSyntax PacketStructureDispatchData
open SyntaxRenameQuerySyntax (of_eq)

def rootBody {m} (f : Family) (w V : Fin m) : Formula (m+(width f+1)) :=
  (row (width f) (tag f) (old (width f+1) w) (fun i => slot (width f+1) i.castSucc) (slot (width f+1) (Fin.last (width f)))).imp
    ((PacketTraceSyntax.condition (old (width f+1) w) (slot (width f+1) (Fin.last (width f)))).iff
      (PacketStructureRootSyntax.criterion f (old (width f+1) w) (old (width f+1) V) (fun i => slot (width f+1) i.castSucc)))

def allRoot {m} (f : Family) (w V : Fin m) : Formula m := OriginalUniversalBlock.allMany (width f+1) (rootBody f w V)

def actualBody {m} (f : Family) (w : Fin m) : Formula (m+width f) :=
  (accepted (width f) (tag f) (old (width f) w) (slot (width f))).iff
    ((environmentNat (width f) (old (width f) w) (slot (width f))).conj (criterion f (old (width f) w) (slot (width f))))

def allActual {m} (f : Family) (w : Fin m) : Formula m := OriginalUniversalBlock.allMany (width f) (actualBody f w)

def allSystem {m} (w : Fin m) : Formula m := (allActual .tree w).conj ((allActual .forest w).conj (allActual .packet w))

def canonicalSystem {m} (w V : Fin m) : Formula m := (PacketTraceCore.value w V).conj
  ((allRoot .tree w V).conj ((allRoot .forest w V).conj (allRoot .packet w V)))

def existsCanonical {m} (w : Fin m) : Formula m := .ex (canonicalSystem w.castSucc (Fin.last m))

theorem rootBody_lift {m j} (f : Family) (w V : Fin m) (ρ : Fin m → Fin j) :
    (rootBody f w V).rename (lift (width f+1) ρ) = rootBody f (ρ w) (ρ V) := by
  simp only [rootBody,Formula.iff,Formula.rename,row_rename,PacketTraceSyntax.condition_rename,PacketStructureRootSyntax.criterion_rename,lift_old,lift_slot]

theorem allRoot_rename {m j} (f : Family) (w V : Fin m) (ρ : Fin m → Fin j) :
    (allRoot f w V).rename ρ = allRoot f (ρ w) (ρ V) := by
  simp only [allRoot,OriginalUniversalBlock.allMany_rename,rootBody_lift]

theorem actualBody_lift {m j} (f : Family) (w : Fin m) (ρ : Fin m → Fin j) :
    (actualBody f w).rename (lift (width f) ρ) = actualBody f (ρ w) := by
  simp only [actualBody,Formula.iff,Formula.rename,accepted_rename,environmentNat_rename,criterion_rename,lift_old,lift_slot]

theorem allActual_rename {m j} (f : Family) (w : Fin m) (ρ : Fin m → Fin j) :
    (allActual f w).rename ρ = allActual f (ρ w) := by
  simp only [allActual,OriginalUniversalBlock.allMany_rename,actualBody_lift]

theorem allSystem_rename {m j} (w : Fin m) (ρ : Fin m → Fin j) :
    (allSystem w).rename ρ = allSystem (ρ w) := by
  simp only [allSystem,Formula.rename,allActual_rename]

theorem canonicalSystem_rename {m j} (w V : Fin m) (ρ : Fin m → Fin j) :
    (canonicalSystem w V).rename ρ = canonicalSystem (ρ w) (ρ V) := by
  simp only [canonicalSystem,Formula.rename,PacketTraceCore.value_rename,allRoot_rename]

theorem existsCanonical_rename {m j} (w : Fin m) (ρ : Fin m → Fin j) :
    (existsCanonical w).rename ρ = existsCanonical (ρ w) := by
  simp only [existsCanonical,Formula.rename,canonicalSystem_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem intro_canonical {m} {Γ : Context m} (w V : Fin m) (hs : Derives Γ (canonicalSystem w V)) : Derives Γ (existsCanonical w) := by
  apply Derives.exI V
  exact of_eq (by simp only [Formula.instantiate,canonicalSystem_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) hs

end PPAC.Migration.Internal.PacketStructureSearchLawSyntax
