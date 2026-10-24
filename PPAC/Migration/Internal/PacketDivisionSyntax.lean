import PPAC.Migration.Internal.ObjectPacketAffineArithmetic

/-! Internal quotient/remainder witnesses for the exact guarded affine relation. -/
namespace PPAC.Migration.Internal.PacketDivisionSyntax
open Source SourceAlgebra SourceLogic HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)

def decompositionBody {m} (w B n : Fin m) : Formula (m+2) :=
  PacketAffineSyntax.affine (old 2 w) (old 2 B) (slot 2 0) (slot 2 1) (old 2 n)

def decomposes {m} (w B n : Fin m) : Formula m := existsMany 2 (decompositionBody w B n)

def matrix : Formula 3 := decomposes 0 1 2

theorem decompositionBody_lift {m j} (w B n : Fin m) (ρ : Fin m → Fin j) :
    (decompositionBody w B n).rename (lift 2 ρ) = decompositionBody (ρ w) (ρ B) (ρ n) := by
  simp only [decompositionBody, PacketAffineSyntax.affine_rename, lift_old, lift_slot]

theorem decomposes_rename {m j} (w B n : Fin m) (ρ : Fin m → Fin j) :
    (decomposes w B n).rename ρ = decomposes (ρ w) (ρ B) (ρ n) := by
  simp only [decomposes, existsMany_rename, decompositionBody_lift]

theorem matrix_pred {m} (ρ : Fin 2 → Fin m) (n : Fin m) :
    MinimalPredicates.pred matrix ρ n = decomposes (ρ 0) (ρ 1) n := by
  have h0 : Fin.lastCases n ρ (0 : Fin 3) = ρ 0 := by
    change Fin.lastCases n ρ (0 : Fin 2).castSucc = ρ 0
    exact Fin.lastCases_castSucc _
  have h1 : Fin.lastCases n ρ (1 : Fin 3) = ρ 1 := by
    change Fin.lastCases n ρ (1 : Fin 2).castSucc = ρ 1
    exact Fin.lastCases_castSucc _
  have h2 : Fin.lastCases n ρ (2 : Fin 3) = n := by
    change Fin.lastCases n ρ (Fin.last 2) = n
    exact Fin.lastCases_last
  simp only [matrix, MinimalPredicates.pred, decomposes_rename, h0, h1, h2]

theorem intro_decomposes {m} {Γ : Context m} (w B n d q : Fin m)
    (ha : Derives Γ (PacketAffineSyntax.affine w B d q n)) : Derives Γ (decomposes w B n) := by
  apply HornBinderRules.intro_many 2 (decompositionBody w B n) (SyntaxAtomSyntax.two d q)
  exact of_eq (by simp only [decompositionBody, PacketAffineSyntax.affine_rename, assign_old, assign_slot]; rfl) ha

end PPAC.Migration.Internal.PacketDivisionSyntax
