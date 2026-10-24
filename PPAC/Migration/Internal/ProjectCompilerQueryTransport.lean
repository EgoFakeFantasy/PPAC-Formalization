import PPAC.Migration.Internal.ProjectCompilerRecursiveSyntax

/-! Logical transport of object guarded-query equivalence through real successor queries. -/
namespace PPAC.Migration.Internal.ProjectCompilerQueryTransport
open Source SourceAlgebra SourceLogic ProjectCompilerCaseSyntax ProjectCompilerQuerySyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem advanced_iff {k l m} {Γ : Context m} (P : Formula (k+3)) (ρ : Fin k → Fin m) (Q : Formula (l+3)) (σ : Fin l → Fin m)
    (n x b q : Fin m) (he : Derives Γ (equivalent P ρ Q σ n)) :
    Derives Γ ((advanced P ρ n x b q).iff (advanced Q σ n x b q)) := by
  apply ProjectSourceCodeCongruence.ex_congr
  have he1 := of_eq (equivalent_rename P ρ Q σ n Fin.castSucc) (Derives.rename Fin.castSucc he)
  exact ProjectSourceCodeCongruence.conj_congr (ProjectSourceTypeLocalTransfer.iff_refl _)
    (at_queries P (fun i => (ρ i).castSucc) Q (fun i => (σ i).castSucc) n.castSucc x.castSucc (Fin.last m) q.castSucc he1)

theorem check_iff {k l m} {Γ : Context m} (advance : Bool) (P : Formula (k+3)) (ρ : Fin k → Fin m) (Q : Formula (l+3)) (σ : Fin l → Fin m)
    (n x b q : Fin m) (he : Derives Γ (equivalent P ρ Q σ n)) :
    Derives Γ ((check advance P ρ n x b q).iff (check advance Q σ n x b q)) := by
  cases advance
  · exact at_queries P ρ Q σ n x b q he
  · exact advanced_iff P ρ Q σ n x b q he

end PPAC.Migration.Internal.ProjectCompilerQueryTransport
