import PPAC.Migration.Internal.ProjectCompilerMatrixTyping

/-! Actual EX2/EX4 case witnesses are eliminated in the original object derivation. -/
namespace PPAC.Migration.Internal.ProjectCompilerCaseTyping
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax ProjectCompilerCaseSyntax ProjectCompilerTypingSyntax
open FormulaCodeSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem atomic_case {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 3) (w b z n q : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hc : Derives Γ (atomicCase kind w b z n q)) :
    Derives Γ (formulaCode w q b z) := by
  let B := atomicBody kind w b z n q
  let Δ := Context.add B (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 B _ hc
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hw2 := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw B)
  have hz2 := of_eq (empty_rename z (old 2)) (HornBinderRules.under_body 2 hz B)
  have ht := ProjectAtomicLaws.compiled_type (HornBinderRules.zf_body 2 hZ B) kind
    (old 2 w) (old 2 b) (old 2 z) (slot 2 0) (slot 2 1) (old 2 n) (old 2 q) hw2 hz2 hB
  exact of_eq (formulaCode_rename w q b z (old 2)).symm ht

theorem single_case {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (advance : Bool)
    (hs : (tag = 4 ∧ advance = false) ∨ (tag = 9 ∧ advance = true) ∨ (tag = 10 ∧ advance = true))
    (P : Formula (k+3)) (ρ : Fin k → Fin m) (w b z n q : Fin m)
    (hw : Derives Γ (omega w)) (hctx : Derives Γ (SyntaxTermSyntax.contexts w b z))
    (hg : Derives Γ (goodQueries P ρ w n z)) (hc : Derives Γ (singleCase tag advance P ρ w b n q)) :
    Derives Γ (formulaCode w q b z) := by
  let B := singleBody tag advance P ρ w b n q
  let Δ := Context.add B (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 B _ hc
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hw2 := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw B)
  have hctx2 := of_eq (SyntaxTermSyntax.contexts_rename w b z (old 2)) (HornBinderRules.under_body 2 hctx B)
  have hg2 := of_eq (goodQueries_rename P ρ w n z (old 2)) (HornBinderRules.under_body 2 hg B)
  have ht := ProjectCompilerMatrixTyping.single_matrix (HornBinderRules.zf_body 2 hZ B) tag advance hs P (fun i => old 2 (ρ i))
    (old 2 w) (old 2 b) (old 2 z) (old 2 n) (old 2 q) (slot 2 0) (slot 2 1) hw2 hctx2 hg2 hB
  exact of_eq (formulaCode_rename w q b z (old 2)).symm ht

theorem binary_case {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4)
    (P : Formula (k+3)) (ρ : Fin k → Fin m) (w b z n q : Fin m)
    (hw : Derives Γ (omega w)) (hctx : Derives Γ (SyntaxTermSyntax.contexts w b z))
    (hg : Derives Γ (goodQueries P ρ w n z)) (hc : Derives Γ (binaryCase kind P ρ w b n q)) :
    Derives Γ (formulaCode w q b z) := by
  let B := binaryBody kind P ρ w b n q
  let Δ := Context.add B (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 B _ hc
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hw4 := of_eq (omega_rename w (old 4)) (HornBinderRules.under_body 4 hw B)
  have hctx4 := of_eq (SyntaxTermSyntax.contexts_rename w b z (old 4)) (HornBinderRules.under_body 4 hctx B)
  have hg4 := of_eq (goodQueries_rename P ρ w n z (old 4)) (HornBinderRules.under_body 4 hg B)
  have ht := ProjectCompilerMatrixTyping.binary_matrix (HornBinderRules.zf_body 4 hZ B) kind P (fun i => old 4 (ρ i))
    (old 4 w) (old 4 b) (old 4 z) (old 4 n) (old 4 q) (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3) hw4 hctx4 hg4 hB
  exact of_eq (formulaCode_rename w q b z (old 4)).symm ht

end PPAC.Migration.Internal.ProjectCompilerCaseTyping
