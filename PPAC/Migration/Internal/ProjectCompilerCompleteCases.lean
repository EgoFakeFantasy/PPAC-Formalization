import PPAC.Migration.Internal.ProjectCompilerCompleteAtoms

/-! Internal source logical witnesses are eliminated while obtaining actual compiler outputs. -/
namespace PPAC.Migration.Internal.ProjectCompilerCompleteCases
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax ProjectCompilerCompleteSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem single_case {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (advance : Bool)
    (hs : (tag = 4 ∧ advance = false) ∨ (tag = 9 ∧ advance = true) ∨ (tag = 10 ∧ advance = true))
    (w n b f z : Fin m) (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hI : Derives Γ (allIH w n))
    (hc : Derives Γ (ProjectSourceCodeRecursiveSyntax.singleCase tag advance w b f n)) :
    Derives Γ (existsOutput w n b) := by
  let B := ProjectSourceCodeRecursiveSyntax.singleCaseBody tag advance w b f n
  let Δ := Context.add B (raisedContext 1 Γ)
  apply HornBinderRules.eliminate_many 1 B _ (.conjR hc)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hw1 := of_eq (omega_rename w (old 1)) (HornBinderRules.under_body 1 hw B)
  have hz1 := of_eq (empty_rename z (old 1)) (HornBinderRules.under_body 1 hz B)
  have hI1 := of_eq (allIH_rename w n (old 1)) (HornBinderRules.under_body 1 hI B)
  have hb1 : Derives Δ (.mem (old 1 b) (old 1 w)) := HornBinderRules.under_body 1 (Derives.conjL (Derives.conjL hc)) B
  have ho := ProjectCompilerCompleteFields.single_fields (HornBinderRules.zf_body 1 hZ B) tag advance hs
    (old 1 w) (old 1 n) (old 1 b) (old 1 f) (old 1 z) (slot 1 0) hw1 hb1 hz1 hI1 hB
  exact of_eq (existsOutput_rename w n b (old 1)).symm ho

theorem binary_case {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4)
    (w n b f z : Fin m) (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hI : Derives Γ (allIH w n))
    (hc : Derives Γ (ProjectSourceCodeRecursiveSyntax.binaryCase kind w b f n)) :
    Derives Γ (existsOutput w n b) := by
  let B := ProjectSourceCodeRecursiveSyntax.binaryCaseBody kind w b f n
  let Δ := Context.add B (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 B _ (.conjR hc)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hw2 := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw B)
  have hz2 := of_eq (empty_rename z (old 2)) (HornBinderRules.under_body 2 hz B)
  have hI2 := of_eq (allIH_rename w n (old 2)) (HornBinderRules.under_body 2 hI B)
  have hb2 : Derives Δ (.mem (old 2 b) (old 2 w)) := HornBinderRules.under_body 2 (Derives.conjL (Derives.conjL hc)) B
  have ho := ProjectCompilerCompleteFields.binary_fields (HornBinderRules.zf_body 2 hZ B) kind
    (old 2 w) (old 2 n) (old 2 b) (old 2 f) (old 2 z) (slot 2 0) (slot 2 1) hw2 hb2 hz2 hI2 hB
  exact of_eq (existsOutput_rename w n b (old 2)).symm ho

theorem all_cases {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n b f z : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hI : Derives Γ (allIH w n))
    (hc : Derives Γ (ProjectSourceCodeRecursiveSyntax.allCases w n b f)) : Derives Γ (existsOutput w n b) := by
  have h0 : Derives Γ ((ProjectSourceAtomSyntax.atomic w b f n).imp (existsOutput w n b)) := by
    apply Derives.impI
    exact ProjectCompilerCompleteAtoms.all_atoms (ZFContext.add hZ _) w n b f z (add hw _) (add hz _) (.hyp (Or.inl rfl))
  have h1 : Derives Γ ((ProjectSourceCodeRecursiveSyntax.singleCase 4 false w b f n).imp (existsOutput w n b)) := by
    apply Derives.impI
    exact single_case (ZFContext.add hZ _) 4 false (Or.inl ⟨rfl,rfl⟩) w n b f z (add hw _) (add hz _) (add hI _) (.hyp (Or.inl rfl))
  have h2 : Derives Γ ((ProjectSourceCodeRecursiveSyntax.binaryCase 0 w b f n).imp (existsOutput w n b)) := by
    apply Derives.impI
    exact binary_case (ZFContext.add hZ _) 0 w n b f z (add hw _) (add hz _) (add hI _) (.hyp (Or.inl rfl))
  have h3 : Derives Γ ((ProjectSourceCodeRecursiveSyntax.binaryCase 1 w b f n).imp (existsOutput w n b)) := by
    apply Derives.impI
    exact binary_case (ZFContext.add hZ _) 1 w n b f z (add hw _) (add hz _) (add hI _) (.hyp (Or.inl rfl))
  have h4 : Derives Γ ((ProjectSourceCodeRecursiveSyntax.binaryCase 2 w b f n).imp (existsOutput w n b)) := by
    apply Derives.impI
    exact binary_case (ZFContext.add hZ _) 2 w n b f z (add hw _) (add hz _) (add hI _) (.hyp (Or.inl rfl))
  have h5 : Derives Γ ((ProjectSourceCodeRecursiveSyntax.binaryCase 3 w b f n).imp (existsOutput w n b)) := by
    apply Derives.impI
    exact binary_case (ZFContext.add hZ _) 3 w n b f z (add hw _) (add hz _) (add hI _) (.hyp (Or.inl rfl))
  have h6 : Derives Γ ((ProjectSourceCodeRecursiveSyntax.singleCase 9 true w b f n).imp (existsOutput w n b)) := by
    apply Derives.impI
    exact single_case (ZFContext.add hZ _) 9 true (Or.inr (Or.inl ⟨rfl,rfl⟩)) w n b f z (add hw _) (add hz _) (add hI _) (.hyp (Or.inl rfl))
  have h7 : Derives Γ ((ProjectSourceCodeRecursiveSyntax.singleCase 10 true w b f n).imp (existsOutput w n b)) := by
    apply Derives.impI
    exact single_case (ZFContext.add hZ _) 10 true (Or.inr (Or.inr ⟨rfl,rfl⟩)) w n b f z (add hw _) (add hz _) (add hI _) (.hyp (Or.inl rfl))
  exact .impE (FormulaCodeCaseLogic.disj_imp h0 (FormulaCodeCaseLogic.disj_imp h1 (FormulaCodeCaseLogic.disj_imp h2 (FormulaCodeCaseLogic.disj_imp h3 (FormulaCodeCaseLogic.disj_imp h4 (FormulaCodeCaseLogic.disj_imp h5 (FormulaCodeCaseLogic.disj_imp h6 h7))))))) hc

end PPAC.Migration.Internal.ProjectCompilerCompleteCases
