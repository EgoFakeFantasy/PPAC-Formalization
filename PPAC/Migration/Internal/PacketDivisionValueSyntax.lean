import PPAC.Migration.Internal.PacketDivisionUnique

/-! The inverse fiber quantifies all internal candidate digits and quotients. -/
namespace PPAC.Migration.Internal.PacketDivisionValueSyntax
open Source SourceAlgebra SourceLogic HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)

def uniquePair {m} (w B n d q : Fin m) : Formula m := OriginalUniversalBlock.allMany 2
  ((PacketAffineSyntax.affine (old 2 w) (old 2 B) (slot 2 0) (slot 2 1) (old 2 n)).imp
    ((Formula.equal (slot 2 0) (old 2 d)).conj (.equal (slot 2 1) (old 2 q))))

theorem uniquePair_rename {m j} (w B n d q : Fin m) (ρ : Fin m → Fin j) :
    (uniquePair w B n d q).rename ρ = uniquePair (ρ w) (ρ B) (ρ n) (ρ d) (ρ q) := by
  simp only [uniquePair, OriginalUniversalBlock.allMany_rename, Formula.rename,
    PacketAffineSyntax.affine_rename, lift_old, lift_slot]

def fiberBody {m} (w B n : Fin m) : Formula (m+2) :=
  (PacketAffineSyntax.affine (old 2 w) (old 2 B) (slot 2 0) (slot 2 1) (old 2 n)).conj
    (uniquePair (old 2 w) (old 2 B) (old 2 n) (slot 2 0) (slot 2 1))

def fiber {m} (w B n : Fin m) : Formula m := existsMany 2 (fiberBody w B n)

theorem fiberBody_lift {m j} (w B n : Fin m) (ρ : Fin m → Fin j) :
    (fiberBody w B n).rename (lift 2 ρ) = fiberBody (ρ w) (ρ B) (ρ n) := by
  simp only [fiberBody, Formula.rename, PacketAffineSyntax.affine_rename, uniquePair_rename, lift_old, lift_slot]

theorem fiber_rename {m j} (w B n : Fin m) (ρ : Fin m → Fin j) :
    (fiber w B n).rename ρ = fiber (ρ w) (ρ B) (ρ n) := by
  simp only [fiber, existsMany_rename, fiberBody_lift]

def acceptedBody {m} (wide : Bool) (w n : Fin m) : Formula (m+2) :=
  PacketAffineAcceptedSyntax.accepted wide (old 2 w) (slot 2 0) (slot 2 1) (old 2 n)

def acceptedDecomposition {m} (wide : Bool) (w n : Fin m) : Formula m := existsMany 2 (acceptedBody wide w n)

theorem acceptedBody_lift {m j} (wide : Bool) (w n : Fin m) (ρ : Fin m → Fin j) :
    (acceptedBody wide w n).rename (lift 2 ρ) = acceptedBody wide (ρ w) (ρ n) := by
  simp only [acceptedBody, PacketAffineAcceptedSyntax.accepted_rename, lift_old, lift_slot]

theorem acceptedDecomposition_rename {m j} (wide : Bool) (w n : Fin m) (ρ : Fin m → Fin j) :
    (acceptedDecomposition wide w n).rename ρ = acceptedDecomposition wide (ρ w) (ρ n) := by
  simp only [acceptedDecomposition, existsMany_rename, acceptedBody_lift]

def allLaw {m} (w B : Fin m) : Formula m := .all
  ((fiber w.castSucc B.castSucc (Fin.last m)).iff (.mem (Fin.last m) w.castSucc))

def allAcceptedLaw {m} (wide : Bool) (w : Fin m) : Formula m := .all
  ((acceptedDecomposition wide w.castSucc (Fin.last m)).iff (.mem (Fin.last m) w.castSucc))

def system {m} (wide : Bool) (w B : Fin m) : Formula m :=
  (PacketAffineLiteralSyntax.frame wide w B).conj ((allLaw w B).conj (allAcceptedLaw wide w))

def existsSystem {m} (wide : Bool) (w : Fin m) : Formula m := .ex (system wide w.castSucc (Fin.last m))

theorem allLaw_rename {m j} (w B : Fin m) (ρ : Fin m → Fin j) :
    (allLaw w B).rename ρ = allLaw (ρ w) (ρ B) := by
  simp only [allLaw, Formula.iff, Formula.rename, fiber_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem allAcceptedLaw_rename {m j} (wide : Bool) (w : Fin m) (ρ : Fin m → Fin j) :
    (allAcceptedLaw wide w).rename ρ = allAcceptedLaw wide (ρ w) := by
  simp only [allAcceptedLaw, Formula.iff, Formula.rename, acceptedDecomposition_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem system_rename {m j} (wide : Bool) (w B : Fin m) (ρ : Fin m → Fin j) :
    (system wide w B).rename ρ = system wide (ρ w) (ρ B) := by
  simp only [system, Formula.rename, PacketAffineLiteralSyntax.frame_rename, allLaw_rename, allAcceptedLaw_rename]

theorem existsSystem_rename {m j} (wide : Bool) (w : Fin m) (ρ : Fin m → Fin j) :
    (existsSystem wide w).rename ρ = existsSystem wide (ρ w) := by
  simp only [existsSystem, Formula.rename, system_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_fiber {m} {Γ : Context m} (w B n d q : Fin m)
    (ha : Derives Γ (PacketAffineSyntax.affine w B d q n)) (hu : Derives Γ (uniquePair w B n d q)) :
    Derives Γ (fiber w B n) := by
  apply HornBinderRules.intro_many 2 (fiberBody w B n) (SyntaxAtomSyntax.two d q)
  exact of_eq (by simp only [fiberBody, Formula.rename, PacketAffineSyntax.affine_rename, uniquePair_rename, assign_old, assign_slot]; rfl) (.conjI ha hu)

theorem intro_accepted {m} {Γ : Context m} (wide : Bool) (w n d q : Fin m)
    (ha : Derives Γ (PacketAffineAcceptedSyntax.accepted wide w d q n)) :
    Derives Γ (acceptedDecomposition wide w n) := by
  apply HornBinderRules.intro_many 2 (acceptedBody wide w n) (SyntaxAtomSyntax.two d q)
  exact of_eq (by simp only [acceptedBody, PacketAffineAcceptedSyntax.accepted_rename, assign_old, assign_slot]; rfl) ha

end PPAC.Migration.Internal.PacketDivisionValueSyntax
