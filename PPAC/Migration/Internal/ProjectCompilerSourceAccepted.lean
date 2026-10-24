import PPAC.Migration.Internal.ProjectCompilerSourceAcceptedSyntax

/-! Exact acceptance of all internal source candidates and actual target-typed unique compiler fibers. -/
namespace PPAC.Migration.Internal.ProjectCompilerSourceAccepted
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax ProjectCompilerSourceAcceptedSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem source_iff_exists {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n b f : Fin m) (hw : Derives Γ (omega w)) :
    Derives Γ ((ProjectSourceCodeSyntax.sourceCode w n b f).iff (accepted w n b f)) := by
  apply Derives.conjI
  · apply Derives.impI
    let S := ProjectSourceCodeSyntax.sourceCode w n b f
    have hs : Derives (Context.add S Γ) S := .hyp (Or.inl rfl)
    have hf := Derives.conjR (Derives.conjR (ProjectSourceCodeProperties.guards w n b f hs))
    exact .conjI hf (ProjectCompilerComplete.output_exists_without_zero (ZFContext.add hZ S) w n b f (add hw S) hs)
  · apply Derives.impI
    let A := accepted w n b f
    let Ξ := Context.add A Γ
    have hA : Derives Ξ A := .hyp (Or.inl rfl)
    let C := ProjectCompilerCodeSyntax.compiled w.castSucc n.castSucc b.castSucc (Fin.last m)
    let Δ := Context.add C (Context.image Formula.raise Ξ)
    apply Derives.exE (p := C) (.conjR hA)
    have hC : Derives Δ C := .hyp (Or.inl rfl)
    have hw1 := of_eq (omega_rename w Fin.castSucc) (under (add hw A) C)
    have hf1 : Derives Δ (.mem f.castSucc w.castSucc) := under (Derives.conjL hA) C
    have hs := ProjectCompilerSourceValid.valid_input (ZFContext.under (ZFContext.add hZ A) C) w.castSucc n.castSucc b.castSucc (Fin.last m) f.castSucc hw1 hf1 hC
    exact of_eq (ProjectSourceCodeSyntax.sourceCode_rename w n b f Fin.castSucc).symm hs

theorem source_iff_typed_fiber {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n b f z : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) :
    Derives Γ ((ProjectSourceCodeSyntax.sourceCode w n b f).iff (typedAccepted w n b f z)) := by
  apply Derives.conjI
  · apply Derives.impI
    let S := ProjectSourceCodeSyntax.sourceCode w n b f
    have hs : Derives (Context.add S Γ) S := .hyp (Or.inl rfl)
    have hf := Derives.conjR (Derives.conjR (ProjectSourceCodeProperties.guards w n b f hs))
    exact .conjI hf (ProjectCompilerUniqueFiber.typed_unique_exists (ZFContext.add hZ S) w n b f z (add hw S) (add hz S) hs)
  · apply Derives.impI
    let A := typedAccepted w n b f z
    let Ξ := Context.add A Γ
    have hA : Derives Ξ A := .hyp (Or.inl rfl)
    let C := ((ProjectCompilerCodeSyntax.compiled w.castSucc n.castSucc b.castSucc (Fin.last m)).conj
      (FormulaCodeSyntax.formulaCode w.castSucc (Fin.last m) b.castSucc z.castSucc)).conj
        (ProjectCompilerUniqueFiberSyntax.uniqueOutput w.castSucc n.castSucc b.castSucc (Fin.last m))
    let Δ := Context.add C (Context.image Formula.raise Ξ)
    apply Derives.exE (p := C) (.conjR hA)
    have hC : Derives Δ C := .hyp (Or.inl rfl)
    have hw1 := of_eq (omega_rename w Fin.castSucc) (under (add hw A) C)
    have hf1 : Derives Δ (.mem f.castSucc w.castSucc) := under (Derives.conjL hA) C
    have hs := ProjectCompilerSourceValid.valid_input (ZFContext.under (ZFContext.add hZ A) C)
      w.castSucc n.castSucc b.castSucc (Fin.last m) f.castSucc hw1 hf1 (.conjL (.conjL hC))
    exact of_eq (ProjectSourceCodeSyntax.sourceCode_rename w n b f Fin.castSucc).symm hs

theorem all_source_iff_exists {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) (hw : Derives Γ (omega w)) :
    Derives Γ (allAcceptanceLaw w) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  have hw3 := of_eq (omega_rename w (old 3)) (HornBinderRules.under_many 3 hw)
  exact source_iff_exists (HornBinderRules.zf_many 3 hZ) (old 3 w) (slot 3 0) (slot 3 1) (slot 3 2) hw3

theorem all_source_iff_typed_fiber {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) (hw : Derives Γ (omega w)) :
    Derives Γ (allTypedAcceptanceLaw w) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let E := empty (slot 4 3 : Fin (m+4))
  have hz : Derives (Context.add E (raisedContext 4 Γ)) E := .hyp (Or.inl rfl)
  have hw4 := of_eq (omega_rename w (old 4)) (HornBinderRules.under_body 4 hw E)
  exact source_iff_typed_fiber (HornBinderRules.zf_body 4 hZ E) (old 4 w) (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3) hw4 hz

theorem closed_source_iff_typed_fiber {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n b z : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) :
    Derives Γ ((ProjectSourceCodeSyntax.sourceCode w n b z).iff (ProjectCompilerUniqueFiberSyntax.typedFiber w n b z)) := by
  have hi := source_iff_typed_fiber hZ w n b z z hw hz
  have hzN := OmegaStructureAlgebra.zero_member w z (ZFContext.arithmetic hZ).base.extensionality hw hz
  apply Derives.conjI
  · apply Derives.impI
    exact .conjR (.impE (add (.conjL hi) _) (.hyp (Or.inl rfl)))
  · apply Derives.impI
    exact .impE (add (.conjR hi) _) (.conjI (add hzN _) (.hyp (Or.inl rfl)))

theorem reject_invalid_source {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n b q f : Fin m)
    (hw : Derives Γ (omega w)) (hf : Derives Γ (.mem f w))
    (hs : Derives Γ (ProjectSourceCodeSyntax.sourceCode w n b f).neg) :
    Derives Γ (ProjectCompilerCodeSyntax.compiled w n b q).neg := by
  apply Derives.impI
  exact .impE (add hs _) (ProjectCompilerSourceValid.valid_input (ZFContext.add hZ _) w n b q f (add hw _) (add hf _) (.hyp (Or.inl rfl)))

end PPAC.Migration.Internal.ProjectCompilerSourceAccepted
