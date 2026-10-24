import PPAC.Migration.Internal.ProjectCompilerTypingQueries

/-! Full actual compiler type preservation for one object member-induction step. -/
namespace PPAC.Migration.Internal.ProjectCompilerTypingStep
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax ProjectCompilerTypingSyntax
open FormulaCodeSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem output_from_induction {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n b q z : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hI : Derives Γ (allIH w n))
    (hc : Derives Γ (ProjectCompilerCodeSyntax.compiled w n b q)) : Derives Γ (formulaCode w q b z) := by
  have hr := Derives.impE (.conjL (ProjectCompilerRecursive.recursive_iff hZ w n b q hw)) hc
  have hb := Derives.conjL (Derives.conjL (Derives.conjR hr))
  let B := ProjectCompilerRecursiveSyntax.body w n b q
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) (.conjR (.conjR hr))
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ B
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hz1 := of_eq (empty_rename z Fin.castSucc) (under hz B)
  have hI1 := of_eq (allIH_rename w n Fin.castSucc) (under hI B)
  have hb1 : Derives Δ (.mem b.castSucc w.castSucc) := under hb B
  have hg := ProjectCompilerTypingQueries.from_induction w.castSucc n.castSucc (Fin.last m) (.conjL hB) hI1
  have ht := ProjectCompilerAllTyping.all_cases hZ1 ProjectCompilerRecursiveSyntax.codeMatrix
    (ProjectCompilerRecursiveSyntax.parameters w.castSucc) w.castSucc b.castSucc (Fin.last m) n.castSucc q.castSucc
    hw1 hb1 (.conjL hB) hg (.conjR hB)
  have he := OmegaUniversal.empty_unique (Fin.last m) z.castSucc (ZFContext.arithmetic hZ1).base.extensionality (.conjL hB) hz1
  have hout := FormulaCodeTransport.code_free w.castSucc q.castSucc b.castSucc (Fin.last m) z.castSucc he ht
  exact of_eq (formulaCode_rename w q b z Fin.castSucc).symm hout

theorem from_induction {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m)
    (hw : Derives Γ (omega w)) (hI : Derives Γ (allIH w n)) : Derives Γ (correct w n) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  apply Derives.impI
  let E := empty (slot 3 2 : Fin (m+3))
  let C := ProjectCompilerCodeSyntax.compiled (old 3 w) (old 3 n) (slot 3 0) (slot 3 1)
  let Δ := Context.add C (Context.add E (raisedContext 3 Γ))
  have hz : Derives Δ E := .hyp (Or.inr (Or.inl rfl))
  have hc : Derives Δ C := .hyp (Or.inl rfl)
  have hw3 := of_eq (omega_rename w (old 3)) (add (HornBinderRules.under_body 3 hw E) C)
  have hI3 := of_eq (allIH_rename w n (old 3)) (add (HornBinderRules.under_body 3 hI E) C)
  exact output_from_induction (ZFContext.add (HornBinderRules.zf_body 3 hZ E) C)
    (old 3 w) (old 3 n) (slot 3 0) (slot 3 1) (slot 3 2) hw3 hz hI3 hc

end PPAC.Migration.Internal.ProjectCompilerTypingStep
