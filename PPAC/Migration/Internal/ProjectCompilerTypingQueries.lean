import PPAC.Migration.Internal.ProjectCompilerAllTyping

/-! The actual compiler child-typing condition is derived from the object member induction hypothesis. -/
namespace PPAC.Migration.Internal.ProjectCompilerTypingQueries
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax ProjectCompilerTypingSyntax ProjectCompilerRecursiveSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem from_induction {m} {Γ : Context m} (w n z : Fin m)
    (hz : Derives Γ (empty z)) (hI : Derives Γ (allIH w n)) :
    Derives Γ (goodQueries codeMatrix (parameters w) w n z) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let K := ProjectCompilerCaseSyntax.queried codeMatrix (parameters (old 3 w)) (old 3 n) (slot 3 0) (slot 3 1) (slot 3 2)
  let Δ := Context.add K (raisedContext 3 Γ)
  have hK : Derives Δ K := .hyp (Or.inl rfl)
  have hz3 := of_eq (empty_rename z (old 3)) (HornBinderRules.under_body 3 hz K)
  have hI3 := of_eq (allIH_rename w n (old 3)) (HornBinderRules.under_body 3 hI K)
  have hx := below_correct (old 3 w) (old 3 n) (slot 3 0) hI3 (.conjL hK)
  have hc := of_eq (codeMatrix_at (parameters (old 3 w)) (slot 3 0) (slot 3 1) (slot 3 2)) (.conjR hK)
  exact at_correct (old 3 w) (slot 3 0) (slot 3 1) (slot 3 2) (old 3 z) hx hz3 hc

end PPAC.Migration.Internal.ProjectCompilerTypingQueries
