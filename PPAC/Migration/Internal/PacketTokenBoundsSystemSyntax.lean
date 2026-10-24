import PPAC.Migration.Internal.PacketTokenBoundsInduction

/-! Quantitative law for the independently defined real token acceptance relation. -/
namespace PPAC.Migration.Internal.PacketTokenBoundsSystemSyntax
open Source SourceAlgebra SourceLogic HornBinderSyntax PacketTokenAcceptedSyntax PacketTokenBoundsSyntax

def lawBody {m} (w : Fin m) : Formula (m+3) :=
  (accepted (old 3 w) (slot 3 0) (slot 3 1) (slot 3 2)).imp (bounds (slot 3 0) (slot 3 1) (slot 3 2))

def allLaw {m} (w : Fin m) : Formula m := OriginalUniversalBlock.allMany 3 (lawBody w)

theorem lawBody_lift {m j} (w : Fin m) (ρ : Fin m → Fin j) :
    (lawBody w).rename (lift 3 ρ) = lawBody (ρ w) := by
  simp only [lawBody,Formula.rename,accepted_rename,bounds_rename,lift_old,lift_slot]

theorem allLaw_rename {m j} (w : Fin m) (ρ : Fin m → Fin j) :
    (allLaw w).rename ρ = allLaw (ρ w) := by
  simp only [allLaw,OriginalUniversalBlock.allMany_rename,lawBody_lift]

end PPAC.Migration.Internal.PacketTokenBoundsSystemSyntax
