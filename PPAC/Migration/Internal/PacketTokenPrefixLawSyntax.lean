import PPAC.Migration.Internal.PacketTokenPrefixSyntax

/-! All candidate numeric inputs and tails stay internally quantified. -/
namespace PPAC.Migration.Internal.PacketTokenPrefixLawSyntax
open Source SourceAlgebra SourceLogic HornBinderSyntax PacketTokenAcceptedSyntax

def five {m} (n t a k s : Fin m) : Fin 5 → Fin m := Fin.cases n (Fin.cases t (Fin.cases a (Fin.cases k (Fin.cases s Fin.elim0))))

def lawBody {m} (w : Fin m) : Formula (m+5) :=
  (accepted (old 5 w) (slot 5 0) (slot 5 1) (slot 5 2)).imp
    ((accepted (old 5 w) (slot 5 3) (slot 5 4) (slot 5 2)).imp
      ((Formula.equal (slot 5 0) (slot 5 3)).conj (.equal (slot 5 1) (slot 5 4))))

def allLaw {m} (w : Fin m) : Formula m := OriginalUniversalBlock.allMany 5 (lawBody w)

theorem lawBody_lift {m j} (w : Fin m) (ρ : Fin m → Fin j) :
    (lawBody w).rename (lift 5 ρ) = lawBody (ρ w) := by
  simp only [lawBody,Formula.rename,accepted_rename,lift_old,lift_slot]

theorem allLaw_rename {m j} (w : Fin m) (ρ : Fin m → Fin j) :
    (allLaw w).rename ρ = allLaw (ρ w) := by
  simp only [allLaw,OriginalUniversalBlock.allMany_rename,lawBody_lift]

end PPAC.Migration.Internal.PacketTokenPrefixLawSyntax
