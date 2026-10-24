import PPAC.Migration.Internal.PacketDivisionDescentCore

/-! Arbitrary finite object matrices index a quotient-recursion induction schema. -/
namespace PPAC.Migration.Internal.PacketQuotientInductionSyntax
open Source SourceAlgebra SourceLogic HornBinderSyntax MinimalPredicates
open ReplacementPredicates (paramsUp)
open SyntaxRenameQuerySyntax (of_eq)

def base {k m} (p : Formula (k+1)) (ρ : Fin k → Fin m) (w B : Fin m) : Formula m := .all
  ((Formula.mem (Fin.last m) w.castSucc).imp ((Formula.mem (Fin.last m) B.castSucc).imp
    (pred p (paramsUp ρ) (Fin.last m))))

def stepBody {k m} (p : Formula (k+1)) (ρ : Fin k → Fin m) (w B : Fin m) : Formula (m+3) :=
  (Formula.mem (slot 3 0) (old 3 w)).imp (((Formula.mem (slot 3 0) (old 3 B)).neg).imp
    ((PacketAffineSyntax.affine (old 3 w) (old 3 B) (slot 3 1) (slot 3 2) (slot 3 0)).imp
      ((pred p (fun i => old 3 (ρ i)) (slot 3 2)).imp (pred p (fun i => old 3 (ρ i)) (slot 3 0)))))

def step {k m} (p : Formula (k+1)) (ρ : Fin k → Fin m) (w B : Fin m) : Formula m :=
  OriginalUniversalBlock.allMany 3 (stepBody p ρ w B)

theorem base_rename {k m j} (p : Formula (k+1)) (ρ : Fin k → Fin m) (w B : Fin m) (σ : Fin m → Fin j) :
    (base p ρ w B).rename σ = base p (fun i => σ (ρ i)) (σ w) (σ B) := by
  simp only [base, Formula.rename, pred_rename, paramsUp, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem stepBody_lift {k m j} (p : Formula (k+1)) (ρ : Fin k → Fin m) (w B : Fin m) (σ : Fin m → Fin j) :
    (stepBody p ρ w B).rename (lift 3 σ) = stepBody p (fun i => σ (ρ i)) (σ w) (σ B) := by
  simp only [stepBody, Formula.rename, PacketAffineSyntax.affine_rename, pred_rename, lift_old, lift_slot]

theorem step_rename {k m j} (p : Formula (k+1)) (ρ : Fin k → Fin m) (w B : Fin m) (σ : Fin m → Fin j) :
    (step p ρ w B).rename σ = step p (fun i => σ (ρ i)) (σ w) (σ B) := by
  simp only [step, OriginalUniversalBlock.allMany_rename, stepBody_lift]

theorem base_at {k m} {Γ : Context m} (p : Formula (k+1)) (ρ : Fin k → Fin m) (w B n : Fin m)
    (hb : Derives Γ (base p ρ w B)) : Derives Γ ((Formula.mem n w).imp ((Formula.mem n B).imp (pred p ρ n))) := by
  exact of_eq (by simp only [Formula.instantiate, Formula.rename, pred_rename, paramsUp,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (Derives.allE n hb)

theorem step_at {k m} {Γ : Context m} (p : Formula (k+1)) (ρ : Fin k → Fin m) (w B n d q : Fin m)
    (hs : Derives Γ (step p ρ w B)) : Derives Γ ((Formula.mem n w).imp (((Formula.mem n B).neg).imp
      ((PacketAffineSyntax.affine w B d q n).imp ((pred p ρ q).imp (pred p ρ n))))) := by
  have ht := OriginalUniversalBlock.at_many 3 (stepBody p ρ w B) (SyntaxAtomSyntax.three n d q) hs
  exact of_eq (by simp only [stepBody, Formula.rename, PacketAffineSyntax.affine_rename, pred_rename, assign_old, assign_slot]; rfl) ht

theorem below_at {k m} {Γ : Context m} (p : Formula (k+1)) (ρ : Fin k → Fin m) (w n q : Fin m)
    (hi : Derives Γ (BoundedInduction.below p ρ w n)) (hq : Derives Γ (.mem q w)) (hqn : Derives Γ (.mem q n)) :
    Derives Γ (pred p ρ q) := by
  have ht : Derives Γ ((Formula.mem q w).imp ((Formula.mem q n).imp (pred p ρ q))) :=
    of_eq (by simp only [Formula.instantiate, Formula.rename, pred_rename, paramsUp,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (Derives.allE q hi)
  exact .impE (.impE ht hq) hqn

end PPAC.Migration.Internal.PacketQuotientInductionSyntax
