import PPAC.Migration.Internal.ProjectCompilerUniqueFiberSyntax

/-! Every internal legal source has an actual target-typed output unique among all compiler outputs. -/
namespace PPAC.Migration.Internal.ProjectCompilerUniqueFiber
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax ProjectCompilerUniqueFiberSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem unique_output {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n b q : Fin m)
    (hw : Derives Γ (omega w)) (hq : Derives Γ (ProjectCompilerCodeSyntax.compiled w n b q)) :
    Derives Γ (uniqueOutput w n b q) := by
  apply Derives.allI
  apply Derives.impI
  let R := ProjectCompilerCodeSyntax.compiled w.castSucc n.castSucc b.castSucc (Fin.last m)
  have hr : Derives (Context.add R (Context.image Formula.raise Γ)) R := .hyp (Or.inl rfl)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hq1 := of_eq (ProjectCompilerCodeSyntax.compiled_rename w n b q Fin.castSucc) (under hq R)
  exact ProjectCompilerUnique.unique_outputs (ZFContext.under hZ R) w.castSucc n.castSucc b.castSucc (Fin.last m) q.castSucc hw1 hr hq1

theorem typed_unique_exists {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n b f z : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hc : Derives Γ (ProjectSourceCodeSyntax.sourceCode w n b f)) :
    Derives Γ (typedFiber w n b z) := by
  let B := (ProjectCompilerCodeSyntax.compiled w.castSucc n.castSucc b.castSucc (Fin.last m)).conj
    (FormulaCodeSyntax.formulaCode w.castSucc (Fin.last m) b.castSucc z.castSucc)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) (ProjectCompilerComplete.typed_output_exists hZ w n b f z hw hz hc)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hu := unique_output (ZFContext.under hZ B) w.castSucc n.castSucc b.castSucc (Fin.last m) hw1 (.conjL hB)
  have ho : Derives Δ (typedFiber w.castSucc n.castSucc b.castSucc z.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [B, Formula.instantiate, Formula.rename, ProjectCompilerCodeSyntax.compiled_rename,
      FormulaCodeSyntax.formulaCode_rename, uniqueOutput_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hB hu)
  exact of_eq (typedFiber_rename w n b z Fin.castSucc).symm ho

theorem all_source_typed_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) (hw : Derives Γ (omega w)) :
    Derives Γ (allSourceTypedUniqueLaw w) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  apply Derives.impI
  let E := empty (slot 4 3 : Fin (m+4))
  let S := ProjectSourceCodeSyntax.sourceCode (old 4 w) (slot 4 0) (slot 4 1) (slot 4 2)
  let Δ := Context.add S (Context.add E (raisedContext 4 Γ))
  have hz : Derives Δ E := .hyp (Or.inr (Or.inl rfl))
  have hs : Derives Δ S := .hyp (Or.inl rfl)
  have hw4 := of_eq (omega_rename w (old 4)) (add (HornBinderRules.under_body 4 hw E) S)
  exact typed_unique_exists (ZFContext.add (HornBinderRules.zf_body 4 hZ E) S)
    (old 4 w) (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3) hw4 hz hs

end PPAC.Migration.Internal.ProjectCompilerUniqueFiber
