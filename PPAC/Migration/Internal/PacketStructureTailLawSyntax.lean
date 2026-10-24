import PPAC.Migration.Internal.PacketStructureTailBounds

/-! Final tail bounds quantify every actual internal tree and forest field candidate. -/
namespace PPAC.Migration.Internal.PacketStructureTailLawSyntax
open Source SourceAlgebra SourceLogic HornBinderSyntax PacketStructureAcceptedSyntax
open NaturalAdditionBounds (below below_rename)

def treeBody {m} (w : Fin m) : Formula (m+3) :=
  (tree (old 3 w) (slot 3 0) (slot 3 1) (slot 3 2)).imp (below (slot 3 1) (slot 3 2))

def allTree {m} (w : Fin m) : Formula m := OriginalUniversalBlock.allMany 3 (treeBody w)

def forestBody {m} (w : Fin m) : Formula (m+4) :=
  (forest (old 4 w) (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3)).imp (below (slot 4 2) (slot 4 3))

def allForest {m} (w : Fin m) : Formula m := OriginalUniversalBlock.allMany 4 (forestBody w)

def allLaw {m} (w : Fin m) : Formula m := (allTree w).conj (allForest w)

theorem treeBody_lift {m j} (w : Fin m) (ρ : Fin m → Fin j) :
    (treeBody w).rename (lift 3 ρ) = treeBody (ρ w) := by
  simp only [treeBody,Formula.rename,tree_rename,below_rename,lift_old,lift_slot]

theorem forestBody_lift {m j} (w : Fin m) (ρ : Fin m → Fin j) :
    (forestBody w).rename (lift 4 ρ) = forestBody (ρ w) := by
  simp only [forestBody,Formula.rename,forest_rename,below_rename,lift_old,lift_slot]

theorem allTree_rename {m j} (w : Fin m) (ρ : Fin m → Fin j) :
    (allTree w).rename ρ = allTree (ρ w) := by
  simp only [allTree,OriginalUniversalBlock.allMany_rename,treeBody_lift]

theorem allForest_rename {m j} (w : Fin m) (ρ : Fin m → Fin j) :
    (allForest w).rename ρ = allForest (ρ w) := by
  simp only [allForest,OriginalUniversalBlock.allMany_rename,forestBody_lift]

theorem allLaw_rename {m j} (w : Fin m) (ρ : Fin m → Fin j) :
    (allLaw w).rename ρ = allLaw (ρ w) := by
  simp only [allLaw,Formula.rename,allTree_rename,allForest_rename]

end PPAC.Migration.Internal.PacketStructureTailLawSyntax
