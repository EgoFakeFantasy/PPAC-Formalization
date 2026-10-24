import PPAC.Migration.Internal.PacketVarintCell
import PPAC.Migration.Internal.StructuralListTraceAppend

/-! One actual independent varint fold step shares its indices with the original ordered list construction. -/
namespace PPAC.Migration.Internal.PacketVarintRowSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax GraphSyntax
open SyntaxRenameQuerySyntax (of_eq)

def six {m} (j h x y u v : Fin m) : Fin 6 → Fin m := Fin.cases j (Fin.cases h (Fin.cases x (Fin.cases y (Fin.cases u (Fin.cases v Fin.elim0)))))

def rowAt {m} (w C f g i j h x y u v : Fin m) : Formula m :=
  (successor j i).conj ((edge f i x).conj ((edge f j y).conj
    ((StructuralListSyntax.consCode w h x y).conj ((edge g i u).conj
      ((edge g j v).conj (PacketVarintCellSyntax.cell w C x h u v))))))

def rowBody {m} (w C f g i : Fin m) : Formula (m+6) :=
  rowAt (old 6 w) (old 6 C) (old 6 f) (old 6 g) (old 6 i)
    (slot 6 0) (slot 6 1) (slot 6 2) (slot 6 3) (slot 6 4) (slot 6 5)

def row {m} (w C f g i : Fin m) : Formula m := existsMany 6 (rowBody w C f g i)

def links {m} (w C l f g : Fin m) : Formula m := .all
  ((Formula.mem (Fin.last m) l.castSucc).imp (row w.castSucc C.castSucc f.castSucc g.castSucc (Fin.last m)))

theorem rowAt_rename {m k} (w C f g i j h x y u v : Fin m) (ρ : Fin m → Fin k) :
    (rowAt w C f g i j h x y u v).rename ρ = rowAt (ρ w) (ρ C) (ρ f) (ρ g) (ρ i) (ρ j) (ρ h) (ρ x) (ρ y) (ρ u) (ρ v) := by
  simp only [rowAt,Formula.rename,successor_rename,edge_rename,StructuralListSyntax.consCode_rename,PacketVarintCellSyntax.cell_rename]

theorem rowBody_lift {m k} (w C f g i : Fin m) (ρ : Fin m → Fin k) :
    (rowBody w C f g i).rename (lift 6 ρ) = rowBody (ρ w) (ρ C) (ρ f) (ρ g) (ρ i) := by
  simp only [rowBody,rowAt_rename,lift_old,lift_slot]

theorem row_rename {m k} (w C f g i : Fin m) (ρ : Fin m → Fin k) :
    (row w C f g i).rename ρ = row (ρ w) (ρ C) (ρ f) (ρ g) (ρ i) := by
  simp only [row,existsMany_rename,rowBody_lift]

theorem links_rename {m k} (w C l f g : Fin m) (ρ : Fin m → Fin k) :
    (links w C l f g).rename ρ = links (ρ w) (ρ C) (ρ l) (ρ f) (ρ g) := by
  simp only [links,Formula.rename,row_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem intro_row {m} {Γ : Context m} (w C f g i j h x y u v : Fin m)
    (hs : Derives Γ (successor j i)) (hx : Derives Γ (edge f i x)) (hy : Derives Γ (edge f j y))
    (hc : Derives Γ (StructuralListSyntax.consCode w h x y)) (hu : Derives Γ (edge g i u)) (hv : Derives Γ (edge g j v))
    (ha : Derives Γ (PacketVarintCellSyntax.cell w C x h u v)) : Derives Γ (row w C f g i) := by
  apply HornBinderRules.intro_many 6 (rowBody w C f g i) (six j h x y u v)
  exact of_eq (by simp only [rowBody,rowAt_rename,assign_old,assign_slot]; rfl)
    (.conjI hs (.conjI hx (.conjI hy (.conjI hc (.conjI hu (.conjI hv ha))))))

theorem links_at {m} {Γ : Context m} (w C l f g i : Fin m) (hl : Derives Γ (links w C l f g))
    (hi : Derives Γ (.mem i l)) : Derives Γ (row w C f g i) := by
  have h : Derives Γ ((Formula.mem i l).imp (row w C f g i)) :=
    of_eq (by simp only [Formula.instantiate,Formula.rename,row_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (Derives.allE i hl)
  exact .impE h hi

theorem empty_links {m} {Γ : Context m} (w C z f g : Fin m) (hz : Derives Γ (empty z)) : Derives Γ (links w C z f g) := by
  apply Derives.allI
  apply Derives.impI
  have hz1 := of_eq (empty_rename z Fin.castSucc) (under hz (Formula.mem (Fin.last m) z.castSucc))
  exact .botE (.impE (empty_at z.castSucc (Fin.last m) hz1) (.hyp (Or.inl rfl)))

end PPAC.Migration.Internal.PacketVarintRowSyntax
