import PPAC.Migration.Internal.ProjectCompilerQueryTransport

/-! All twelve actual compiler cases preserve object query equivalence, including every witness. -/
namespace PPAC.Migration.Internal.ProjectCompilerCaseTransport
open Source SourceAlgebra SourceLogic HornBinderSyntax ProjectCompilerCaseSyntax ProjectCompilerQuerySyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem single_matrix {k l m} {Γ : Context m} (tag : Nat) (advance : Bool)
    (P : Formula (k+3)) (ρ : Fin k → Fin m) (Q : Formula (l+3)) (σ : Fin l → Fin m)
    (w b n q x y : Fin m) (he : Derives Γ (equivalent P ρ Q σ n)) :
    Derives Γ ((singleMatrix tag advance P ρ w b n q x y).iff (singleMatrix tag advance Q σ w b n q x y)) :=
  ProjectSourceCodeCongruence.conj_congr (ProjectSourceTypeLocalTransfer.iff_refl _)
    (ProjectSourceCodeCongruence.conj_congr (ProjectCompilerQueryTransport.check_iff advance P ρ Q σ n x b y he)
      (ProjectSourceTypeLocalTransfer.iff_refl _))

theorem single_case {k l m} {Γ : Context m} (tag : Nat) (advance : Bool)
    (P : Formula (k+3)) (ρ : Fin k → Fin m) (Q : Formula (l+3)) (σ : Fin l → Fin m)
    (w b n q : Fin m) (he : Derives Γ (equivalent P ρ Q σ n)) :
    Derives Γ ((singleCase tag advance P ρ w b n q).iff (singleCase tag advance Q σ w b n q)) := by
  apply ProjectSourceCodeCongruence.ex_congr
  apply ProjectSourceCodeCongruence.ex_congr
  have he2 := of_eq (equivalent_rename P ρ Q σ n (old 2)) (HornBinderRules.under_many 2 he)
  exact single_matrix tag advance P (fun i => old 2 (ρ i)) Q (fun i => old 2 (σ i))
    (old 2 w) (old 2 b) (old 2 n) (old 2 q) (slot 2 0) (slot 2 1) he2

theorem binary_matrix {k l m} {Γ : Context m} (kind : Fin 4)
    (P : Formula (k+3)) (ρ : Fin k → Fin m) (Q : Formula (l+3)) (σ : Fin l → Fin m)
    (w b n q x y X Y : Fin m) (he : Derives Γ (equivalent P ρ Q σ n)) :
    Derives Γ ((binaryMatrix kind P ρ w b n q x y X Y).iff (binaryMatrix kind Q σ w b n q x y X Y)) :=
  ProjectSourceCodeCongruence.conj_congr (ProjectSourceTypeLocalTransfer.iff_refl _)
    (ProjectSourceCodeCongruence.conj_congr (at_queries P ρ Q σ n x b X he)
      (ProjectSourceCodeCongruence.conj_congr (at_queries P ρ Q σ n y b Y he) (ProjectSourceTypeLocalTransfer.iff_refl _)))

theorem binary_case {k l m} {Γ : Context m} (kind : Fin 4)
    (P : Formula (k+3)) (ρ : Fin k → Fin m) (Q : Formula (l+3)) (σ : Fin l → Fin m)
    (w b n q : Fin m) (he : Derives Γ (equivalent P ρ Q σ n)) :
    Derives Γ ((binaryCase kind P ρ w b n q).iff (binaryCase kind Q σ w b n q)) := by
  apply ProjectSourceCodeCongruence.ex_congr
  apply ProjectSourceCodeCongruence.ex_congr
  apply ProjectSourceCodeCongruence.ex_congr
  apply ProjectSourceCodeCongruence.ex_congr
  have he4 := of_eq (equivalent_rename P ρ Q σ n (old 4)) (HornBinderRules.under_many 4 he)
  exact binary_matrix kind P (fun i => old 4 (ρ i)) Q (fun i => old 4 (σ i))
    (old 4 w) (old 4 b) (old 4 n) (old 4 q) (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3) he4

theorem all_cases {k l m} {Γ : Context m}
    (P : Formula (k+3)) (ρ : Fin k → Fin m) (Q : Formula (l+3)) (σ : Fin l → Fin m)
    (w b z n q : Fin m) (he : Derives Γ (equivalent P ρ Q σ n)) :
    Derives Γ ((cases P ρ w b z n q).iff (cases Q σ w b z n q)) := by
  exact ProjectSourceTypeLocalTransfer.disj_congr (ProjectSourceTypeLocalTransfer.iff_refl (constant false w n q)) (ProjectSourceTypeLocalTransfer.disj_congr (ProjectSourceTypeLocalTransfer.iff_refl (constant true w n q)) (ProjectSourceTypeLocalTransfer.disj_congr (ProjectSourceTypeLocalTransfer.iff_refl (atomicCase 0 w b z n q)) (ProjectSourceTypeLocalTransfer.disj_congr (ProjectSourceTypeLocalTransfer.iff_refl (atomicCase 1 w b z n q)) (ProjectSourceTypeLocalTransfer.disj_congr (ProjectSourceTypeLocalTransfer.iff_refl (atomicCase 2 w b z n q)) (ProjectSourceTypeLocalTransfer.disj_congr (single_case 4 false P ρ Q σ w b n q he) (ProjectSourceTypeLocalTransfer.disj_congr (binary_case 0 P ρ Q σ w b n q he) (ProjectSourceTypeLocalTransfer.disj_congr (binary_case 1 P ρ Q σ w b n q he) (ProjectSourceTypeLocalTransfer.disj_congr (binary_case 2 P ρ Q σ w b n q he) (ProjectSourceTypeLocalTransfer.disj_congr (binary_case 3 P ρ Q σ w b n q he) (ProjectSourceTypeLocalTransfer.disj_congr (single_case 9 true P ρ Q σ w b n q he) (single_case 10 true P ρ Q σ w b n q he)))))))))))

end PPAC.Migration.Internal.ProjectCompilerCaseTransport
