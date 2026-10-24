import PPAC.Migration.Internal.ProjectCompilerCompleteStep

/-! Original Foundation proves actual output existence for every internal legal Project source code. -/
namespace PPAC.Migration.Internal.ProjectCompilerComplete
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax ProjectCompilerCompleteSyntax
open SyntaxRenameQuerySyntax (of_eq)
open ReplacementPredicates (paramsUp)

def inductionMatrix : Formula 2 := correct (0 : Fin 1).castSucc (Fin.last 1)

theorem matrix_pred {m} (ρ : Fin 1 → Fin m) (x : Fin m) :
    MinimalPredicates.pred inductionMatrix ρ x = correct (ρ 0) x := by
  simp only [inductionMatrix, MinimalPredicates.pred, correct_rename, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem progressive {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) (hw : Derives Γ (omega w)) :
    Derives Γ (SetInductionSyntax.progressive inductionMatrix (fun _ : Fin 1 => w)) := by
  simp only [SetInductionSyntax.progressive, SetInductionSyntax.below, matrix_pred, paramsUp]
  apply Derives.allI
  apply Derives.impI
  let I := allIH w.castSucc (Fin.last m)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw I)
  exact ProjectCompilerCompleteStep.from_induction (ZFContext.under hZ I) w.castSucc (Fin.last m) hw1 (.hyp (Or.inl rfl))

theorem all_correct {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) (hw : Derives Γ (omega w)) :
    Derives Γ (.all (correct w.castSucc (Fin.last m))) := by
  have hh := SetInduction.all_holds inductionMatrix (fun _ : Fin 1 => w)
    (ZFContext.separation hZ inductionMatrix.neg) (ZFContext.arithmetic hZ).base.foundation
    (ZFContext.closed hZ ObjectTransitiveCover.source_cover) (progressive hZ w hw)
  exact of_eq (by simp only [SetInductionSyntax.holds, matrix_pred, paramsUp]) hh

theorem at_input {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m) (hw : Derives Γ (omega w)) :
    Derives Γ (correct w n) := of_eq
  (by simp only [Formula.instantiate, correct_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
  (Derives.allE n (all_correct hZ w hw))

theorem output_exists {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n b f z : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hc : Derives Γ (ProjectSourceCodeSyntax.sourceCode w n b f)) : Derives Γ (existsOutput w n b) :=
  at_correct w n b f z (at_input hZ w n hw) hz hc

theorem output_exists_without_zero {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n b f : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (ProjectSourceCodeSyntax.sourceCode w n b f)) :
    Derives Γ (existsOutput w n b) := by
  let Z := (Formula.mem (Fin.last m) w.castSucc).conj (empty (Fin.last m))
  let Δ := Context.add Z (Context.image Formula.raise Γ)
  apply Derives.exE (p := Z) (.conjL (.conjL hw))
  have hZ0 : Derives Δ Z := .hyp (Or.inl rfl)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw Z)
  have hc1 := of_eq (ProjectSourceCodeSyntax.sourceCode_rename w n b f Fin.castSucc) (under hc Z)
  exact of_eq (existsOutput_rename w n b Fin.castSucc).symm
    (output_exists (ZFContext.under hZ Z) w.castSucc n.castSucc b.castSucc f.castSucc (Fin.last m) hw1 (.conjR hZ0) hc1)

def sourceLawBody {m} (w : Fin m) : Formula (m+3) :=
  (ProjectSourceCodeSyntax.sourceCode (old 3 w) (slot 3 0) (slot 3 1) (slot 3 2)).imp
    (existsOutput (old 3 w) (slot 3 0) (slot 3 1))

def allSourceLaw {m} (w : Fin m) : Formula m := OriginalUniversalBlock.allMany 3 (sourceLawBody w)

theorem sourceLawBody_lift {m j} (w : Fin m) (σ : Fin m → Fin j) :
    (sourceLawBody w).rename (lift 3 σ) = sourceLawBody (σ w) := by
  simp only [sourceLawBody, Formula.rename, ProjectSourceCodeSyntax.sourceCode_rename, existsOutput_rename, lift_old, lift_slot]

theorem allSourceLaw_rename {m j} (w : Fin m) (σ : Fin m → Fin j) :
    (allSourceLaw w).rename σ = allSourceLaw (σ w) := by
  simp only [allSourceLaw, OriginalUniversalBlock.allMany_rename, sourceLawBody_lift]

theorem all_source_outputs {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) (hw : Derives Γ (omega w)) :
    Derives Γ (allSourceLaw w) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let S := ProjectSourceCodeSyntax.sourceCode (old 3 w) (slot 3 0) (slot 3 1) (slot 3 2)
  have hw3 := of_eq (omega_rename w (old 3)) (HornBinderRules.under_body 3 hw S)
  exact output_exists_without_zero (HornBinderRules.zf_body 3 hZ S) (old 3 w) (slot 3 0) (slot 3 1) (slot 3 2) hw3 (.hyp (Or.inl rfl))

theorem typed_output_exists {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n b f z : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hc : Derives Γ (ProjectSourceCodeSyntax.sourceCode w n b f)) :
    Derives Γ (ProjectCompilerBase.existsTyped w n b z) := by
  let C := ProjectCompilerCodeSyntax.compiled w.castSucc n.castSucc b.castSucc (Fin.last m)
  let Δ := Context.add C (Context.image Formula.raise Γ)
  apply Derives.exE (p := C) (output_exists_without_zero hZ w n b f hw hc)
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw C)
  have hz1 := of_eq (empty_rename z Fin.castSucc) (under hz C)
  have ht := ProjectCompilerTyping.output_type (ZFContext.under hZ C) w.castSucc n.castSucc b.castSucc (Fin.last m) z.castSucc hw1 hz1 hC
  have ho : Derives Δ (ProjectCompilerBase.existsTyped w.castSucc n.castSucc b.castSucc z.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [C, Formula.instantiate, Formula.rename, ProjectCompilerCodeSyntax.compiled_rename,
      FormulaCodeSyntax.formulaCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hC ht)
  exact of_eq (ProjectCompilerBase.existsTyped_rename w n b z Fin.castSucc).symm ho

end PPAC.Migration.Internal.ProjectCompilerComplete
