import PPAC.Migration.Internal.ProjectCompilerIndependent

/-! Original-rule introduction of actual twelve-case program branches. -/
namespace PPAC.Migration.Internal.ProjectCompilerCaseIntro
open Source SourceAlgebra SourceLogic HornBinderSyntax ProjectCompilerCaseSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem atomic_case {m} {Γ : Context m} (kind : Fin 3) (w b z x y n q : Fin m)
    (hc : Derives Γ (ProjectAtomicSyntax.compiled kind w b z x y n q)) : Derives Γ (atomicCase kind w b z n q) := by
  apply HornBinderRules.intro_many 2 (atomicBody kind w b z n q) (SyntaxAtomSyntax.two x y)
  exact of_eq (by simp only [atomicBody, ProjectAtomicSyntax.compiled_rename, assign_old, assign_slot]; rfl) hc

theorem single_case {k m} {Γ : Context m} (tag : Nat) (advance : Bool) (P : Formula (k+3)) (ρ : Fin k → Fin m)
    (w b n q x y : Fin m) (hc : Derives Γ (singleMatrix tag advance P ρ w b n q x y)) :
    Derives Γ (singleCase tag advance P ρ w b n q) := by
  apply HornBinderRules.intro_many 2 (singleBody tag advance P ρ w b n q) (SyntaxAtomSyntax.two x y)
  exact of_eq (by simp only [singleBody, singleMatrix_rename, assign_old, assign_slot]; rfl) hc

def four {m} (x y X Y : Fin m) (i : Fin 4) : Fin m := match i.val with | 0 => x | 1 => y | 2 => X | _ => Y

theorem binary_case {k m} {Γ : Context m} (kind : Fin 4) (P : Formula (k+3)) (ρ : Fin k → Fin m)
    (w b n q x y X Y : Fin m) (hc : Derives Γ (binaryMatrix kind P ρ w b n q x y X Y)) :
    Derives Γ (binaryCase kind P ρ w b n q) := by
  apply HornBinderRules.intro_many 4 (binaryBody kind P ρ w b n q) (four x y X Y)
  exact of_eq (by simp only [binaryBody, binaryMatrix_rename, assign_old, assign_slot]; rfl) hc

theorem constant_cases {k m} {Γ : Context m} (truth : Bool) (P : Formula (k+3)) (ρ : Fin k → Fin m)
    (w b z n q : Fin m) (hc : Derives Γ (constant truth w n q)) : Derives Γ (cases P ρ w b z n q) := by
  cases truth
  · exact .disjL hc
  · exact .disjR (.disjL hc)

theorem atomic_cases {k m} {Γ : Context m} (kind : Fin 3) (P : Formula (k+3)) (ρ : Fin k → Fin m)
    (w b z n q : Fin m) (hc : Derives Γ (atomicCase kind w b z n q)) : Derives Γ (cases P ρ w b z n q) := by
  rcases kind with ⟨j,hj⟩
  have h : j=0 ∨ j=1 ∨ j=2 := by omega
  rcases h with rfl | rfl | rfl
  · exact .disjR (.disjR (.disjL hc))
  · exact .disjR (.disjR (.disjR (.disjL hc)))
  · exact .disjR (.disjR (.disjR (.disjR (.disjL hc))))

end PPAC.Migration.Internal.ProjectCompilerCaseIntro
