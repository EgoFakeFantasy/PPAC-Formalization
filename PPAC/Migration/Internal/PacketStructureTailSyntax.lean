import PPAC.Migration.Internal.ObjectPacketStructureRoot

/-! One fixed object matrix couples both kinds of actual accepted tail bounds. -/
namespace PPAC.Migration.Internal.PacketStructureTailSyntax
open Source SourceAlgebra SourceLogic HornBinderSyntax PacketStructureAcceptedSyntax
open NaturalAdditionBounds (below below_rename)
open SyntaxRenameQuerySyntax (of_eq)

def treeProperty {m} (w n : Fin m) : Formula m := OriginalUniversalBlock.allMany 2
  ((tree (old 2 w) (old 2 n) (slot 2 0) (slot 2 1)).imp (below (slot 2 0) (slot 2 1)))

def forestProperty {m} (w n : Fin m) : Formula m := OriginalUniversalBlock.allMany 3
  ((forest (old 3 w) (old 3 n) (slot 3 0) (slot 3 1) (slot 3 2)).imp (below (slot 3 1) (slot 3 2)))

def property {m} (w n : Fin m) : Formula m := (treeProperty w n).conj (forestProperty w n)

def matrix : Formula 2 := property 0 1

def hypothesis {m} (w n : Fin m) : Formula m := BoundedInduction.below matrix (fun _ : Fin 1 => w) w n

theorem treeProperty_rename {m j} (w n : Fin m) (ρ : Fin m → Fin j) :
    (treeProperty w n).rename ρ = treeProperty (ρ w) (ρ n) := by
  simp only [treeProperty,OriginalUniversalBlock.allMany_rename,Formula.rename,tree_rename,below_rename,lift_old,lift_slot]

theorem forestProperty_rename {m j} (w n : Fin m) (ρ : Fin m → Fin j) :
    (forestProperty w n).rename ρ = forestProperty (ρ w) (ρ n) := by
  simp only [forestProperty,OriginalUniversalBlock.allMany_rename,Formula.rename,forest_rename,below_rename,lift_old,lift_slot]

theorem property_rename {m j} (w n : Fin m) (ρ : Fin m → Fin j) :
    (property w n).rename ρ = property (ρ w) (ρ n) := by
  simp only [property,Formula.rename,treeProperty_rename,forestProperty_rename]

theorem matrix_pred {m} (ρ : Fin 1 → Fin m) (n : Fin m) : MinimalPredicates.pred matrix ρ n = property (ρ 0) n := by
  have h0 : Fin.lastCases n ρ (0 : Fin 2) = ρ 0 := by
    change Fin.lastCases n ρ (0 : Fin 1).castSucc = ρ 0
    exact Fin.lastCases_castSucc _
  have h1 : Fin.lastCases n ρ (1 : Fin 2) = n := by
    change Fin.lastCases n ρ (Fin.last 1) = n
    exact Fin.lastCases_last
  simp only [matrix,MinimalPredicates.pred,property_rename,h0,h1]

theorem hypothesis_rename {m j} (w n : Fin m) (ρ : Fin m → Fin j) :
    (hypothesis w n).rename ρ = hypothesis (ρ w) (ρ n) := BoundedInduction.below_rename matrix (fun _ => w) w n ρ

theorem tree_at {m} {Γ : Context m} (w n t a : Fin m) (hp : Derives Γ (treeProperty w n))
    (ha : Derives Γ (tree w n t a)) : Derives Γ (below t a) := by
  have hi := OriginalUniversalBlock.at_many 2 _ (SyntaxAtomSyntax.two t a) hp
  have he : Derives Γ ((tree w n t a).imp (below t a)) :=
    of_eq (by simp only [Formula.rename,tree_rename,below_rename,assign_old,assign_slot]; rfl) hi
  exact .impE he ha

theorem forest_at {m} {Γ : Context m} (w n l t a : Fin m) (hp : Derives Γ (forestProperty w n))
    (ha : Derives Γ (forest w n l t a)) : Derives Γ (below t a) := by
  have hi := OriginalUniversalBlock.at_many 3 _ (SyntaxAtomSyntax.three l t a) hp
  have he : Derives Γ ((forest w n l t a).imp (below t a)) :=
    of_eq (by simp only [Formula.rename,forest_rename,below_rename,assign_old,assign_slot]; rfl) hi
  exact .impE he ha

theorem ih_at {m} {Γ : Context m} (w n q : Fin m) (hi : Derives Γ (hypothesis w n))
    (hq : Derives Γ (.mem q w)) (hqn : Derives Γ (.mem q n)) : Derives Γ (property w q) :=
  of_eq (matrix_pred (fun _ : Fin 1 => w) q) (PacketQuotientInductionSyntax.below_at matrix (fun _ : Fin 1 => w) w n q hi hq hqn)

end PPAC.Migration.Internal.PacketStructureTailSyntax
