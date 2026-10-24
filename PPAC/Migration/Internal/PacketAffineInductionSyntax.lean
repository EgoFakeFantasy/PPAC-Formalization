import PPAC.Migration.Internal.PacketAffineRootEquation

/-! The induction predicate quantifies every digit, output, and actual row internally. -/
namespace PPAC.Migration.Internal.PacketAffineInductionSyntax
open Source SourceAlgebra SourceLogic HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)

def propertyBody {m} (wide : Bool) (w B V t : Fin m) : Formula (m+3) :=
  (PacketHornAffineSyntax.row wide (old 3 w) (slot 3 0) (old 3 t) (slot 3 1) (slot 3 2)).imp
    ((Formula.mem (slot 3 2) (old 3 V)).iff (PacketAffineSyntax.affine (old 3 w) (old 3 B) (slot 3 0) (old 3 t) (slot 3 1)))

def correct {m} (wide : Bool) (w B V t : Fin m) : Formula m := OriginalUniversalBlock.allMany 3 (propertyBody wide w B V t)

def matrix (wide : Bool) : Formula 4 := correct wide 0 1 2 3

theorem propertyBody_lift {m j} (wide : Bool) (w B V t : Fin m) (ρ : Fin m → Fin j) :
    (propertyBody wide w B V t).rename (lift 3 ρ) = propertyBody wide (ρ w) (ρ B) (ρ V) (ρ t) := by
  simp only [propertyBody, Formula.iff, Formula.rename, PacketHornAffineSyntax.row_rename, PacketAffineSyntax.affine_rename, lift_old, lift_slot]

theorem correct_rename {m j} (wide : Bool) (w B V t : Fin m) (ρ : Fin m → Fin j) :
    (correct wide w B V t).rename ρ = correct wide (ρ w) (ρ B) (ρ V) (ρ t) := by
  simp only [correct, OriginalUniversalBlock.allMany_rename, propertyBody_lift]

theorem matrix_pred {m} (wide : Bool) (ρ : Fin 3 → Fin m) (t : Fin m) :
    MinimalPredicates.pred (matrix wide) ρ t = correct wide (ρ 0) (ρ 1) (ρ 2) t := by
  have h0 : Fin.lastCases t ρ (0 : Fin 4) = ρ 0 := by
    change Fin.lastCases t ρ (0 : Fin 3).castSucc = ρ 0
    exact Fin.lastCases_castSucc _
  have h1 : Fin.lastCases t ρ (1 : Fin 4) = ρ 1 := by
    change Fin.lastCases t ρ (1 : Fin 3).castSucc = ρ 1
    exact Fin.lastCases_castSucc _
  have h2 : Fin.lastCases t ρ (2 : Fin 4) = ρ 2 := by
    change Fin.lastCases t ρ (2 : Fin 3).castSucc = ρ 2
    exact Fin.lastCases_castSucc _
  have h3 : Fin.lastCases t ρ (3 : Fin 4) = t := by
    change Fin.lastCases t ρ (Fin.last 3) = t
    exact Fin.lastCases_last
  simp only [matrix, MinimalPredicates.pred, correct_rename, h0, h1, h2, h3]

theorem at_correct {m} {Γ : Context m} (wide : Bool) (w B V t d n r : Fin m)
    (hI : Derives Γ (correct wide w B V t)) (hr : Derives Γ (PacketHornAffineSyntax.row wide w d t n r)) :
    Derives Γ ((Formula.mem r V).iff (PacketAffineSyntax.affine w B d t n)) := by
  have ha := OriginalUniversalBlock.at_many 3 (propertyBody wide w B V t) (SyntaxAtomSyntax.three d n r) hI
  have hh : Derives Γ ((PacketHornAffineSyntax.row wide w d t n r).imp
      ((Formula.mem r V).iff (PacketAffineSyntax.affine w B d t n))) :=
    of_eq (by simp only [propertyBody, Formula.iff, Formula.rename, PacketHornAffineSyntax.row_rename,
      PacketAffineSyntax.affine_rename, assign_old, assign_slot]; rfl) ha
  exact .impE hh hr

end PPAC.Migration.Internal.PacketAffineInductionSyntax
