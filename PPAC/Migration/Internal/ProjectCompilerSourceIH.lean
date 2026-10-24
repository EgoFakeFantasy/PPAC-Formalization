import PPAC.Migration.Internal.ProjectCompilerSourceCases

/-! The object member IH supplies actual child source-validity judgments at every internal scope. -/
namespace PPAC.Migration.Internal.ProjectCompilerSourceIH
open Source SourceAlgebra SourceLogic HornBinderSyntax ProjectCompilerSourceSyntax ProjectCompilerRecursiveSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem supply_queries {m} {Γ : Context m} (w n f : Fin m) (hf : Derives Γ (.mem f w)) (hI : Derives Γ (allIH w n)) :
    Derives Γ (goodQueries codeMatrix (parameters w) w n f) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let K := ProjectCompilerCaseSyntax.queried codeMatrix (parameters (old 3 w)) (old 3 n) (slot 3 0) (slot 3 1) (slot 3 2)
  let Δ := Context.add K (raisedContext 3 Γ)
  have hK : Derives Δ K := .hyp (Or.inl rfl)
  have hf3 : Derives Δ (.mem (old 3 f) (old 3 w)) := HornBinderRules.under_body 3 hf K
  have hI3 := of_eq (allIH_rename w n (old 3)) (HornBinderRules.under_body 3 hI K)
  have hc := of_eq (codeMatrix_at (parameters (old 3 w)) (slot 3 0) (slot 3 1) (slot 3 2)) (.conjR hK)
  have hs := below_correct (old 3 w) (old 3 n) (slot 3 0) hI3 (.conjL hK)
  exact at_correct (old 3 w) (slot 3 0) (slot 3 1) (slot 3 2) (old 3 f) hs hf3 hc

end PPAC.Migration.Internal.ProjectCompilerSourceIH
