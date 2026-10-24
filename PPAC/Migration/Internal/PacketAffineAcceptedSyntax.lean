import PPAC.Migration.Internal.PacketAffineInduction

/-! All-data acceptance existentially binds an actual Packet root; invalid data are kept in the domain. -/
namespace PPAC.Migration.Internal.PacketAffineAcceptedSyntax
open Source SourceAlgebra SourceLogic HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)

def accepted {m} (wide : Bool) (w d t n : Fin m) : Formula m := .ex
  ((PacketHornAffineSyntax.row wide w.castSucc d.castSucc t.castSucc n.castSucc (Fin.last m)).conj
    (PacketTraceSyntax.condition w.castSucc (Fin.last m)))

def lawBody {m} (wide : Bool) (w B : Fin m) : Formula (m+3) :=
  (accepted wide (old 3 w) (slot 3 0) (slot 3 1) (slot 3 2)).iff
    (PacketAffineSyntax.affine (old 3 w) (old 3 B) (slot 3 0) (slot 3 1) (slot 3 2))

def allLaw {m} (wide : Bool) (w B : Fin m) : Formula m := OriginalUniversalBlock.allMany 3 (lawBody wide w B)

def rootLawBody {m} (wide : Bool) (w B : Fin m) : Formula (m+4) :=
  (PacketHornAffineSyntax.row wide (old 4 w) (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3)).imp
    ((PacketTraceSyntax.condition (old 4 w) (slot 4 3)).iff
      (PacketAffineSyntax.affine (old 4 w) (old 4 B) (slot 4 0) (slot 4 1) (slot 4 2)))

def allRootLaw {m} (wide : Bool) (w B : Fin m) : Formula m := OriginalUniversalBlock.allMany 4 (rootLawBody wide w B)

def system {m} (wide : Bool) (w B : Fin m) : Formula m :=
  (PacketAffineLiteralSyntax.frame wide w B).conj ((allLaw wide w B).conj (allRootLaw wide w B))

def existsSystem {m} (wide : Bool) (w : Fin m) : Formula m := .ex (system wide w.castSucc (Fin.last m))

theorem accepted_rename {m j} (wide : Bool) (w d t n : Fin m) (ρ : Fin m → Fin j) :
    (accepted wide w d t n).rename ρ = accepted wide (ρ w) (ρ d) (ρ t) (ρ n) := by
  simp only [accepted, Formula.rename, PacketHornAffineSyntax.row_rename, PacketTraceSyntax.condition_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem lawBody_lift {m j} (wide : Bool) (w B : Fin m) (ρ : Fin m → Fin j) :
    (lawBody wide w B).rename (lift 3 ρ) = lawBody wide (ρ w) (ρ B) := by
  simp only [lawBody, Formula.iff, Formula.rename, accepted_rename, PacketAffineSyntax.affine_rename, lift_old, lift_slot]

theorem allLaw_rename {m j} (wide : Bool) (w B : Fin m) (ρ : Fin m → Fin j) :
    (allLaw wide w B).rename ρ = allLaw wide (ρ w) (ρ B) := by
  simp only [allLaw, OriginalUniversalBlock.allMany_rename, lawBody_lift]

theorem rootLawBody_lift {m j} (wide : Bool) (w B : Fin m) (ρ : Fin m → Fin j) :
    (rootLawBody wide w B).rename (lift 4 ρ) = rootLawBody wide (ρ w) (ρ B) := by
  simp only [rootLawBody, Formula.iff, Formula.rename, PacketHornAffineSyntax.row_rename, PacketTraceSyntax.condition_rename,
    PacketAffineSyntax.affine_rename, lift_old, lift_slot]

theorem allRootLaw_rename {m j} (wide : Bool) (w B : Fin m) (ρ : Fin m → Fin j) :
    (allRootLaw wide w B).rename ρ = allRootLaw wide (ρ w) (ρ B) := by
  simp only [allRootLaw, OriginalUniversalBlock.allMany_rename, rootLawBody_lift]

theorem system_rename {m j} (wide : Bool) (w B : Fin m) (ρ : Fin m → Fin j) :
    (system wide w B).rename ρ = system wide (ρ w) (ρ B) := by
  simp only [system, Formula.rename, PacketAffineLiteralSyntax.frame_rename, allLaw_rename, allRootLaw_rename]

theorem existsSystem_rename {m j} (wide : Bool) (w : Fin m) (ρ : Fin m → Fin j) :
    (existsSystem wide w).rename ρ = existsSystem wide (ρ w) := by
  simp only [existsSystem, Formula.rename, system_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_accepted {m} {Γ : Context m} (wide : Bool) (w d t n r : Fin m)
    (hr : Derives Γ (PacketHornAffineSyntax.row wide w d t n r)) (hc : Derives Γ (PacketTraceSyntax.condition w r)) :
    Derives Γ (accepted wide w d t n) := by
  apply Derives.exI r
  exact of_eq (by simp only [Formula.instantiate, Formula.rename, PacketHornAffineSyntax.row_rename,
    PacketTraceSyntax.condition_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hr hc)

end PPAC.Migration.Internal.PacketAffineAcceptedSyntax
