import PPAC.Migration.Internal.PacketAffineRuleData

/-! Literal radix frames and complete internal affine systems for the two actual Packet arithmetic relations. -/
namespace PPAC.Migration.Internal.PacketAffineLiteralSyntax
open Source SourceAlgebra SourceLogic HornBinderSyntax PacketAffineSyntax

def frame {m} (wide : Bool) (w B : Fin m) : Formula m :=
  (Formula.mem B w).conj (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B)

def totalBody {m} (w B : Fin m) : Formula (m+2) :=
  ((Formula.mem (slot 2 0) (old 2 B)).conj (.mem (slot 2 1) (old 2 w))).imp
    (fiber (old 2 w) (old 2 B) (slot 2 0) (slot 2 1))

def totalLaw {m} (w B : Fin m) : Formula m := OriginalUniversalBlock.allMany 2 (totalBody w B)

def system {m} (wide : Bool) (w B : Fin m) : Formula m :=
  (frame wide w B).conj ((totalLaw w B).conj (PacketAffineRecursive.universalLaw w B))

def existsSystem {m} (wide : Bool) (w : Fin m) : Formula m := .ex (system wide w.castSucc (Fin.last m))

theorem frame_rename {m j} (wide : Bool) (w B : Fin m) (σ : Fin m → Fin j) :
    (frame wide w B).rename σ = frame wide (σ w) (σ B) := by
  simp only [frame, Formula.rename, SyntaxNumeralSyntax.numeral_rename]

theorem totalBody_lift {m j} (w B : Fin m) (σ : Fin m → Fin j) :
    (totalBody w B).rename (lift 2 σ) = totalBody (σ w) (σ B) := by
  simp only [totalBody, Formula.rename, fiber_rename, lift_old, lift_slot]

theorem totalLaw_rename {m j} (w B : Fin m) (σ : Fin m → Fin j) :
    (totalLaw w B).rename σ = totalLaw (σ w) (σ B) := by
  simp only [totalLaw, OriginalUniversalBlock.allMany_rename, totalBody_lift]

theorem system_rename {m j} (wide : Bool) (w B : Fin m) (σ : Fin m → Fin j) :
    (system wide w B).rename σ = system wide (σ w) (σ B) := by
  simp only [system, Formula.rename, frame_rename, totalLaw_rename, PacketAffineRecursive.universalLaw_rename]

theorem existsSystem_rename {m j} (wide : Bool) (w : Fin m) (σ : Fin m → Fin j) :
    (existsSystem wide w).rename σ = existsSystem wide (σ w) := by
  simp only [existsSystem, Formula.rename, system_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

end PPAC.Migration.Internal.PacketAffineLiteralSyntax
