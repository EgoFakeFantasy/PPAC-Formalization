import PPAC.Migration.Internal.PacketQuotientInduction

/-! Complete descent contracts quantify arbitrary internal accepted candidates. -/
namespace PPAC.Migration.Internal.PacketDivisionDescentSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax

def properties {m} (_w B d q n : Fin m) : Formula m :=
  (NaturalAdditionBounds.below q n).conj (((empty n).neg.imp (.mem q n)).conj
    (((empty q).iff (.mem n B)).conj ((empty n).iff ((empty d).conj (empty q)))))

def branch {m} (B d q n : Fin m) : Formula m :=
  ((empty q).conj ((Formula.mem n B).conj (.equal n d))).disj
    ((Formula.mem q n).conj ((empty q).neg.conj (Formula.mem n B).neg))

def lawBody {m} (wide : Bool) (w B : Fin m) : Formula (m+3) :=
  (PacketAffineAcceptedSyntax.accepted wide (old 3 w) (slot 3 0) (slot 3 1) (slot 3 2)).imp
    ((properties (old 3 w) (old 3 B) (slot 3 0) (slot 3 1) (slot 3 2)).conj
      (branch (old 3 B) (slot 3 0) (slot 3 1) (slot 3 2)))

def allLaw {m} (wide : Bool) (w B : Fin m) : Formula m := OriginalUniversalBlock.allMany 3 (lawBody wide w B)

def system {m} (wide : Bool) (w B : Fin m) : Formula m :=
  (PacketDivisionValueSyntax.system wide w B).conj (allLaw wide w B)

def existsSystem {m} (wide : Bool) (w : Fin m) : Formula m := .ex (system wide w.castSucc (Fin.last m))

theorem properties_rename {m j} (w B d q n : Fin m) (ρ : Fin m → Fin j) :
    (properties w B d q n).rename ρ = properties (ρ w) (ρ B) (ρ d) (ρ q) (ρ n) := by
  simp only [properties, Formula.iff, Formula.rename, NaturalAdditionBounds.below_rename, empty_rename]

theorem branch_rename {m j} (B d q n : Fin m) (ρ : Fin m → Fin j) :
    (branch B d q n).rename ρ = branch (ρ B) (ρ d) (ρ q) (ρ n) := by
  simp only [branch, Formula.rename, empty_rename]

theorem lawBody_lift {m j} (wide : Bool) (w B : Fin m) (ρ : Fin m → Fin j) :
    (lawBody wide w B).rename (lift 3 ρ) = lawBody wide (ρ w) (ρ B) := by
  simp only [lawBody, Formula.rename, PacketAffineAcceptedSyntax.accepted_rename, properties_rename, branch_rename, lift_old, lift_slot]

theorem allLaw_rename {m j} (wide : Bool) (w B : Fin m) (ρ : Fin m → Fin j) :
    (allLaw wide w B).rename ρ = allLaw wide (ρ w) (ρ B) := by
  simp only [allLaw, OriginalUniversalBlock.allMany_rename, lawBody_lift]

theorem system_rename {m j} (wide : Bool) (w B : Fin m) (ρ : Fin m → Fin j) :
    (system wide w B).rename ρ = system wide (ρ w) (ρ B) := by
  simp only [system, Formula.rename, PacketDivisionValueSyntax.system_rename, allLaw_rename]

theorem existsSystem_rename {m j} (wide : Bool) (w : Fin m) (ρ : Fin m → Fin j) :
    (existsSystem wide w).rename ρ = existsSystem wide (ρ w) := by
  simp only [existsSystem, Formula.rename, system_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

end PPAC.Migration.Internal.PacketDivisionDescentSyntax
