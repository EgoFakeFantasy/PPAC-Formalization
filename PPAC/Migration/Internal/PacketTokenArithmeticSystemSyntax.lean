import PPAC.Migration.Internal.PacketTokenArithmeticProperties

/-! All-data arithmetic recursion laws and literal systems bind no external canonical value. -/
namespace PPAC.Migration.Internal.PacketTokenArithmeticSystemSyntax
open Source SourceAlgebra SourceLogic HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)

def lawBody {m} (w B C : Fin m) : Formula (m+3) :=
  (PacketTokenAcceptedSyntax.accepted (old 3 w) (slot 3 0) (slot 3 1) (slot 3 2)).iff
    (PacketTokenArithmeticSyntax.criterion (old 3 w) (old 3 B) (old 3 C) (slot 3 0) (slot 3 1) (slot 3 2))

def allLaw {m} (w B C : Fin m) : Formula m := OriginalUniversalBlock.allMany 3 (lawBody w B C)

def rootLawBody {m} (w B C : Fin m) : Formula (m+4) :=
  (PacketTokenSyntax.row (old 4 w) (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3)).imp
    ((PacketTraceSyntax.condition (old 4 w) (slot 4 3)).iff
      (PacketTokenArithmeticSyntax.criterion (old 4 w) (old 4 B) (old 4 C) (slot 4 0) (slot 4 1) (slot 4 2)))

def allRootLaw {m} (w B C : Fin m) : Formula m := OriginalUniversalBlock.allMany 4 (rootLawBody w B C)

def system {m} (w B C : Fin m) : Formula m := (PacketAffineLiteralSyntax.frame false w B).conj
  ((PacketAffineLiteralSyntax.frame true w C).conj ((allLaw w B C).conj (allRootLaw w B C)))

def systemBody {m} (w : Fin m) : Formula (m+2) := system (old 2 w) (slot 2 0) (slot 2 1)

def existsSystem {m} (w : Fin m) : Formula m := existsMany 2 (systemBody w)

theorem lawBody_lift {m j} (w B C : Fin m) (ρ : Fin m → Fin j) :
    (lawBody w B C).rename (lift 3 ρ) = lawBody (ρ w) (ρ B) (ρ C) := by
  simp only [lawBody,Formula.iff,Formula.rename,PacketTokenAcceptedSyntax.accepted_rename,
    PacketTokenArithmeticSyntax.criterion_rename,lift_old,lift_slot]

theorem allLaw_rename {m j} (w B C : Fin m) (ρ : Fin m → Fin j) :
    (allLaw w B C).rename ρ = allLaw (ρ w) (ρ B) (ρ C) := by
  simp only [allLaw,OriginalUniversalBlock.allMany_rename,lawBody_lift]

theorem rootLawBody_lift {m j} (w B C : Fin m) (ρ : Fin m → Fin j) :
    (rootLawBody w B C).rename (lift 4 ρ) = rootLawBody (ρ w) (ρ B) (ρ C) := by
  simp only [rootLawBody,Formula.iff,Formula.rename,PacketTokenSyntax.row_rename,PacketTraceSyntax.condition_rename,
    PacketTokenArithmeticSyntax.criterion_rename,lift_old,lift_slot]

theorem allRootLaw_rename {m j} (w B C : Fin m) (ρ : Fin m → Fin j) :
    (allRootLaw w B C).rename ρ = allRootLaw (ρ w) (ρ B) (ρ C) := by
  simp only [allRootLaw,OriginalUniversalBlock.allMany_rename,rootLawBody_lift]

theorem system_rename {m j} (w B C : Fin m) (ρ : Fin m → Fin j) :
    (system w B C).rename ρ = system (ρ w) (ρ B) (ρ C) := by
  simp only [system,Formula.rename,PacketAffineLiteralSyntax.frame_rename,allLaw_rename,allRootLaw_rename]

theorem systemBody_lift {m j} (w : Fin m) (ρ : Fin m → Fin j) :
    (systemBody w).rename (lift 2 ρ) = systemBody (ρ w) := by
  simp only [systemBody,system_rename,lift_old,lift_slot]

theorem existsSystem_rename {m j} (w : Fin m) (ρ : Fin m → Fin j) :
    (existsSystem w).rename ρ = existsSystem (ρ w) := by
  simp only [existsSystem,existsMany_rename,systemBody_lift]

theorem intro_system {m} {Γ : Context m} (w B C : Fin m) (hs : Derives Γ (system w B C)) : Derives Γ (existsSystem w) := by
  apply HornBinderRules.intro_many 2 (systemBody w) (SyntaxAtomSyntax.two B C)
  exact of_eq (by simp only [systemBody,system_rename,assign_old,assign_slot]; rfl) hs

end PPAC.Migration.Internal.PacketTokenArithmeticSystemSyntax
