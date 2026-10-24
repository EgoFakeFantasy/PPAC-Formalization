import PPAC.Migration.Internal.ProjectCompilerCompleteCases

/-! Actual source-code completeness for one object member-induction step. -/
namespace PPAC.Migration.Internal.ProjectCompilerCompleteStep
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax ProjectCompilerCompleteSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem output_from_induction {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n b f z : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hI : Derives Γ (allIH w n))
    (hc : Derives Γ (ProjectSourceCodeSyntax.sourceCode w n b f)) : Derives Γ (existsOutput w n b) := by
  have hr := Derives.impE (.conjL (ProjectSourceCodeRecursive.recursive_iff hZ w n b f hw)) hc
  exact ProjectCompilerCompleteCases.all_cases hZ w n b f z hw hz hI (.conjR hr)

theorem from_induction {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m)
    (hw : Derives Γ (omega w)) (hI : Derives Γ (allIH w n)) : Derives Γ (correct w n) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  apply Derives.impI
  let E := empty (slot 3 2 : Fin (m+3))
  let C := ProjectSourceCodeSyntax.sourceCode (old 3 w) (old 3 n) (slot 3 0) (slot 3 1)
  let Δ := Context.add C (Context.add E (raisedContext 3 Γ))
  have hz : Derives Δ E := .hyp (Or.inr (Or.inl rfl))
  have hc : Derives Δ C := .hyp (Or.inl rfl)
  have hw3 := of_eq (omega_rename w (old 3)) (add (HornBinderRules.under_body 3 hw E) C)
  have hI3 := of_eq (allIH_rename w n (old 3)) (add (HornBinderRules.under_body 3 hI E) C)
  exact output_from_induction (ZFContext.add (HornBinderRules.zf_body 3 hZ E) C)
    (old 3 w) (old 3 n) (slot 3 0) (slot 3 1) (slot 3 2) hw3 hz hI3 hc

end PPAC.Migration.Internal.ProjectCompilerCompleteStep
