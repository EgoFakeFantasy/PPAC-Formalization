import PPAC.Migration.Internal.ProjectCompilerCaseTyping

/-! All twelve actual case templates produce target FormulaCode under the explicit object child condition. -/
namespace PPAC.Migration.Internal.ProjectCompilerAllTyping
open Source SourceAlgebra SourceLogic OmegaSyntax ProjectCompilerCaseSyntax ProjectCompilerTypingSyntax FormulaCodeSyntax

theorem all_cases {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (P : Formula (k+3)) (ρ : Fin k → Fin m)
    (w b z n q : Fin m) (hw : Derives Γ (omega w)) (hb : Derives Γ (.mem b w)) (hz : Derives Γ (empty z))
    (hg : Derives Γ (goodQueries P ρ w n z)) (hc : Derives Γ (cases P ρ w b z n q)) :
    Derives Γ (formulaCode w q b z) := by
  have hzW := OmegaStructureAlgebra.zero_member w z (ZFContext.arithmetic hZ).base.extensionality hw hz
  have hctx : Derives Γ (SyntaxTermSyntax.contexts w b z) := .conjI hb hzW
  have h0 : Derives Γ ((constant false w n q).imp (formulaCode w q b z)) := by
    apply Derives.impI
    exact ProjectCompilerMatrixTyping.constant_type (ZFContext.add hZ _) false w n b z q (add hw _) (add hb _) (add hz _) (.hyp (Or.inl rfl))
  have h1 : Derives Γ ((constant true w n q).imp (formulaCode w q b z)) := by
    apply Derives.impI
    exact ProjectCompilerMatrixTyping.constant_type (ZFContext.add hZ _) true w n b z q (add hw _) (add hb _) (add hz _) (.hyp (Or.inl rfl))
  have h2 : Derives Γ ((atomicCase 0 w b z n q).imp (formulaCode w q b z)) := by
    apply Derives.impI
    exact ProjectCompilerCaseTyping.atomic_case (ZFContext.add hZ _) 0 w b z n q (add hw _) (add hz _) (.hyp (Or.inl rfl))
  have h3 : Derives Γ ((atomicCase 1 w b z n q).imp (formulaCode w q b z)) := by
    apply Derives.impI
    exact ProjectCompilerCaseTyping.atomic_case (ZFContext.add hZ _) 1 w b z n q (add hw _) (add hz _) (.hyp (Or.inl rfl))
  have h4 : Derives Γ ((atomicCase 2 w b z n q).imp (formulaCode w q b z)) := by
    apply Derives.impI
    exact ProjectCompilerCaseTyping.atomic_case (ZFContext.add hZ _) 2 w b z n q (add hw _) (add hz _) (.hyp (Or.inl rfl))
  have h5 : Derives Γ ((singleCase 4 false P ρ w b n q).imp (formulaCode w q b z)) := by
    apply Derives.impI
    exact ProjectCompilerCaseTyping.single_case (ZFContext.add hZ _) 4 false (Or.inl ⟨rfl,rfl⟩) P ρ w b z n q (add hw _) (add hctx _) (add hg _) (.hyp (Or.inl rfl))
  have h6 : Derives Γ ((binaryCase 0 P ρ w b n q).imp (formulaCode w q b z)) := by
    apply Derives.impI
    exact ProjectCompilerCaseTyping.binary_case (ZFContext.add hZ _) 0 P ρ w b z n q (add hw _) (add hctx _) (add hg _) (.hyp (Or.inl rfl))
  have h7 : Derives Γ ((binaryCase 1 P ρ w b n q).imp (formulaCode w q b z)) := by
    apply Derives.impI
    exact ProjectCompilerCaseTyping.binary_case (ZFContext.add hZ _) 1 P ρ w b z n q (add hw _) (add hctx _) (add hg _) (.hyp (Or.inl rfl))
  have h8 : Derives Γ ((binaryCase 2 P ρ w b n q).imp (formulaCode w q b z)) := by
    apply Derives.impI
    exact ProjectCompilerCaseTyping.binary_case (ZFContext.add hZ _) 2 P ρ w b z n q (add hw _) (add hctx _) (add hg _) (.hyp (Or.inl rfl))
  have h9 : Derives Γ ((binaryCase 3 P ρ w b n q).imp (formulaCode w q b z)) := by
    apply Derives.impI
    exact ProjectCompilerCaseTyping.binary_case (ZFContext.add hZ _) 3 P ρ w b z n q (add hw _) (add hctx _) (add hg _) (.hyp (Or.inl rfl))
  have h10 : Derives Γ ((singleCase 9 true P ρ w b n q).imp (formulaCode w q b z)) := by
    apply Derives.impI
    exact ProjectCompilerCaseTyping.single_case (ZFContext.add hZ _) 9 true (Or.inr (Or.inl ⟨rfl,rfl⟩)) P ρ w b z n q (add hw _) (add hctx _) (add hg _) (.hyp (Or.inl rfl))
  have h11 : Derives Γ ((singleCase 10 true P ρ w b n q).imp (formulaCode w q b z)) := by
    apply Derives.impI
    exact ProjectCompilerCaseTyping.single_case (ZFContext.add hZ _) 10 true (Or.inr (Or.inr ⟨rfl,rfl⟩)) P ρ w b z n q (add hw _) (add hctx _) (add hg _) (.hyp (Or.inl rfl))
  exact .impE (FormulaCodeCaseLogic.disj_imp h0 (FormulaCodeCaseLogic.disj_imp h1 (FormulaCodeCaseLogic.disj_imp h2 (FormulaCodeCaseLogic.disj_imp h3 (FormulaCodeCaseLogic.disj_imp h4 (FormulaCodeCaseLogic.disj_imp h5 (FormulaCodeCaseLogic.disj_imp h6 (FormulaCodeCaseLogic.disj_imp h7 (FormulaCodeCaseLogic.disj_imp h8 (FormulaCodeCaseLogic.disj_imp h9 (FormulaCodeCaseLogic.disj_imp h10 h11))))))))))) hc

end PPAC.Migration.Internal.ProjectCompilerAllTyping
