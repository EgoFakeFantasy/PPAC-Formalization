import PPAC.Migration.Internal.PacketTokenDispatch

/-! A single actual two-radix canonical system covers every internal token root candidate. -/
namespace PPAC.Migration.Internal.PacketTokenSystemSyntax
open Source SourceAlgebra SourceLogic HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)

def lawBody {m} (w B _C V : Fin m) : Formula (m+4) :=
  (PacketTokenSyntax.row (old 4 w) (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3)).imp
    ((PacketTraceSyntax.condition (old 4 w) (slot 4 3)).iff
      ((PacketTokenApplicationSyntax.smallOutcome (old 4 w) (old 4 B) (old 4 V) (slot 4 3)).disj
        (PacketTokenApplicationSyntax.largeOutcome (old 4 w) (old 4 B) (old 4 V) (slot 4 3))))

def allLaw {m} (w B C V : Fin m) : Formula m := OriginalUniversalBlock.allMany 4 (lawBody w B C V)

def system {m} (w B C V : Fin m) : Formula m := (PacketAffineLiteralSyntax.frame false w B).conj
  ((PacketAffineLiteralSyntax.frame true w C).conj ((PacketTraceCore.value w V).conj (allLaw w B C V)))

def systemBody {m} (w : Fin m) : Formula (m+3) := system (old 3 w) (slot 3 0) (slot 3 1) (slot 3 2)

def existsSystem {m} (w : Fin m) : Formula m := existsMany 3 (systemBody w)

theorem lawBody_lift {m j} (w B C V : Fin m) (ρ : Fin m → Fin j) :
    (lawBody w B C V).rename (lift 4 ρ) = lawBody (ρ w) (ρ B) (ρ C) (ρ V) := by
  simp only [lawBody, Formula.iff, Formula.rename, PacketTokenSyntax.row_rename, PacketTraceSyntax.condition_rename,
    PacketTokenApplicationSyntax.smallOutcome_rename, PacketTokenApplicationSyntax.largeOutcome_rename, lift_old, lift_slot]

theorem allLaw_rename {m j} (w B C V : Fin m) (ρ : Fin m → Fin j) :
    (allLaw w B C V).rename ρ = allLaw (ρ w) (ρ B) (ρ C) (ρ V) := by
  simp only [allLaw, OriginalUniversalBlock.allMany_rename, lawBody_lift]

theorem system_rename {m j} (w B C V : Fin m) (ρ : Fin m → Fin j) :
    (system w B C V).rename ρ = system (ρ w) (ρ B) (ρ C) (ρ V) := by
  simp only [system, Formula.rename, PacketAffineLiteralSyntax.frame_rename, PacketTraceCore.value_rename, allLaw_rename]

theorem systemBody_lift {m j} (w : Fin m) (ρ : Fin m → Fin j) :
    (systemBody w).rename (lift 3 ρ) = systemBody (ρ w) := by
  simp only [systemBody, system_rename, lift_old, lift_slot]

theorem existsSystem_rename {m j} (w : Fin m) (ρ : Fin m → Fin j) :
    (existsSystem w).rename ρ = existsSystem (ρ w) := by
  simp only [existsSystem, existsMany_rename, systemBody_lift]

theorem intro_system {m} {Γ : Context m} (w B C V : Fin m) (hs : Derives Γ (system w B C V)) :
    Derives Γ (existsSystem w) := by
  apply HornBinderRules.intro_many 3 (systemBody w) (SyntaxAtomSyntax.three B C V)
  exact of_eq (by simp only [systemBody, system_rename, assign_old, assign_slot]; rfl) hs

end PPAC.Migration.Internal.PacketTokenSystemSyntax
