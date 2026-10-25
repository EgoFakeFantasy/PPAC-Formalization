import PPAC.Migration.Internal.ObjectPacketReaderRecursion
import PPAC.Migration.Internal.StructuralListTraceAppend

/-! One actual coupled-splice step shares its indices with the original ordered list construction. -/
namespace PPAC.Migration.Internal.StructuralListSpliceRowSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax GraphSyntax
open SyntaxRenameQuerySyntax (of_eq)

def push {m} (w h u v : Fin m) : Formula m :=
  (Formula.mem h w).conj (StructuralListSyntax.consCode w h u v)

theorem push_rename {m k} (w h u v : Fin m) (ρ : Fin m → Fin k) :
    (push w h u v).rename ρ = push (ρ w) (ρ h) (ρ u) (ρ v) := by
  simp only [push,Formula.rename,StructuralListSyntax.consCode_rename]

def six {m} (j h x y u v : Fin m) : Fin 6 → Fin m := Fin.cases j (Fin.cases h (Fin.cases x (Fin.cases y (Fin.cases u (Fin.cases v Fin.elim0)))))

def rowAt {m} (w f g i j h x y u v : Fin m) : Formula m :=
  (successor j i).conj ((edge f i x).conj ((edge f j y).conj
    ((StructuralListSyntax.consCode w h x y).conj ((edge g i u).conj
      ((edge g j v).conj (StructuralListSpliceRowSyntax.push w h u v))))))

def rowBody {m} (w f g i : Fin m) : Formula (m+6) :=
  rowAt (old 6 w) (old 6 f) (old 6 g) (old 6 i)
    (slot 6 0) (slot 6 1) (slot 6 2) (slot 6 3) (slot 6 4) (slot 6 5)

def row {m} (w f g i : Fin m) : Formula m := existsMany 6 (rowBody w f g i)

def links {m} (w l f g : Fin m) : Formula m := .all
  ((Formula.mem (Fin.last m) l.castSucc).imp (row w.castSucc f.castSucc g.castSucc (Fin.last m)))

theorem rowAt_rename {m k} (w f g i j h x y u v : Fin m) (ρ : Fin m → Fin k) :
    (rowAt w f g i j h x y u v).rename ρ = rowAt (ρ w) (ρ f) (ρ g) (ρ i) (ρ j) (ρ h) (ρ x) (ρ y) (ρ u) (ρ v) := by
  simp only [rowAt,Formula.rename,successor_rename,edge_rename,StructuralListSyntax.consCode_rename,StructuralListSpliceRowSyntax.push_rename]

theorem rowBody_lift {m k} (w f g i : Fin m) (ρ : Fin m → Fin k) :
    (rowBody w f g i).rename (lift 6 ρ) = rowBody (ρ w) (ρ f) (ρ g) (ρ i) := by
  simp only [rowBody,rowAt_rename,lift_old,lift_slot]

theorem row_rename {m k} (w f g i : Fin m) (ρ : Fin m → Fin k) :
    (row w f g i).rename ρ = row (ρ w) (ρ f) (ρ g) (ρ i) := by
  simp only [row,existsMany_rename,rowBody_lift]

theorem links_rename {m k} (w l f g : Fin m) (ρ : Fin m → Fin k) :
    (links w l f g).rename ρ = links (ρ w) (ρ l) (ρ f) (ρ g) := by
  simp only [links,Formula.rename,row_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem intro_row {m} {Γ : Context m} (w f g i j h x y u v : Fin m)
    (hs : Derives Γ (successor j i)) (hx : Derives Γ (edge f i x)) (hy : Derives Γ (edge f j y))
    (hc : Derives Γ (StructuralListSyntax.consCode w h x y)) (hu : Derives Γ (edge g i u)) (hv : Derives Γ (edge g j v))
    (ha : Derives Γ (StructuralListSpliceRowSyntax.push w h u v)) : Derives Γ (row w f g i) := by
  apply HornBinderRules.intro_many 6 (rowBody w f g i) (six j h x y u v)
  exact of_eq (by simp only [rowBody,rowAt_rename,assign_old,assign_slot]; rfl)
    (.conjI hs (.conjI hx (.conjI hy (.conjI hc (.conjI hu (.conjI hv ha))))))

theorem links_at {m} {Γ : Context m} (w l f g i : Fin m) (hl : Derives Γ (links w l f g))
    (hi : Derives Γ (.mem i l)) : Derives Γ (row w f g i) := by
  have h : Derives Γ ((Formula.mem i l).imp (row w f g i)) :=
    of_eq (by simp only [Formula.instantiate,Formula.rename,row_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (Derives.allE i hl)
  exact .impE h hi

theorem empty_links {m} {Γ : Context m} (w z f g : Fin m) (hz : Derives Γ (empty z)) : Derives Γ (links w z f g) := by
  apply Derives.allI
  apply Derives.impI
  have hz1 := of_eq (empty_rename z Fin.castSucc) (under hz (Formula.mem (Fin.last m) z.castSucc))
  exact .botE (.impE (empty_at z.castSucc (Fin.last m) hz1) (.hyp (Or.inl rfl)))

end PPAC.Migration.Internal.StructuralListSpliceRowSyntax
