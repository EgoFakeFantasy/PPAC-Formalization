import PPAC.Migration.Internal.ObjectProjectCompiler

/-! Object ALL3 equivalence for guarded recursive queries; no correctness oracle is introduced. -/
namespace PPAC.Migration.Internal.ProjectCompilerQuerySyntax
open Source SourceAlgebra SourceLogic HornBinderSyntax ProjectCompilerCaseSyntax
open SyntaxRenameQuerySyntax (of_eq)

def body {k l m} (P : Formula (k+3)) (ρ : Fin k → Fin m) (Q : Formula (l+3)) (σ : Fin l → Fin m) (n : Fin m) : Formula (m+3) :=
  (queried P (fun i => old 3 (ρ i)) (old 3 n) (slot 3 0) (slot 3 1) (slot 3 2)).iff
    (queried Q (fun i => old 3 (σ i)) (old 3 n) (slot 3 0) (slot 3 1) (slot 3 2))

def equivalent {k l m} (P : Formula (k+3)) (ρ : Fin k → Fin m) (Q : Formula (l+3)) (σ : Fin l → Fin m) (n : Fin m) : Formula m :=
  OriginalUniversalBlock.allMany 3 (body P ρ Q σ n)

theorem body_lift {k l m j} (P : Formula (k+3)) (ρ : Fin k → Fin m) (Q : Formula (l+3)) (σ : Fin l → Fin m)
    (n : Fin m) (τ : Fin m → Fin j) :
    (body P ρ Q σ n).rename (lift 3 τ) = body P (fun i => τ (ρ i)) Q (fun i => τ (σ i)) (τ n) := by
  simp only [body, Formula.iff, Formula.rename, queried_rename, lift_old, lift_slot]

theorem equivalent_rename {k l m j} (P : Formula (k+3)) (ρ : Fin k → Fin m) (Q : Formula (l+3)) (σ : Fin l → Fin m)
    (n : Fin m) (τ : Fin m → Fin j) :
    (equivalent P ρ Q σ n).rename τ = equivalent P (fun i => τ (ρ i)) Q (fun i => τ (σ i)) (τ n) := by
  simp only [equivalent, OriginalUniversalBlock.allMany_rename, body_lift]

theorem at_queries {k l m} {Γ : Context m} (P : Formula (k+3)) (ρ : Fin k → Fin m) (Q : Formula (l+3)) (σ : Fin l → Fin m)
    (n x b q : Fin m) (he : Derives Γ (equivalent P ρ Q σ n)) :
    Derives Γ ((queried P ρ n x b q).iff (queried Q σ n x b q)) := by
  have hi := OriginalUniversalBlock.at_many 3 (body P ρ Q σ n) (SyntaxAtomSyntax.three x b q) he
  exact of_eq (by simp only [body, Formula.iff, Formula.rename, queried_rename, assign_old, assign_slot]; rfl) hi

end PPAC.Migration.Internal.ProjectCompilerQuerySyntax
