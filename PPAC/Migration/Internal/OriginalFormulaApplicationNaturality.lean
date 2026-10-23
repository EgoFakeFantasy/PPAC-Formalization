import PPAC.Migration.Internal.ObjectOriginalFormulaMatrix

/-! 原关系应用实际结构的输出自然性和内部符号索引自然性。 -/
namespace PPAC.Migration.Internal.OriginalFormulaApplicationNaturality
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open OriginalFormulaApplicationSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem scalar_index_natural {m} {Γ : Context m} (w symbol s : Fin m)
    (hs : Derives Γ (SyntaxNodeSyntax.scalar w symbol s)) : Derives Γ (.mem symbol w) := by
  let B := SyntaxNodeSyntax.nodeBody 0 w symbol Fin.elim0 s
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hs
  exact .conjL (.hyp (Or.inl rfl))

theorem symbol_natural {m} {Γ : Context m} (w symbol args n : Fin m)
    (ha : Derives Γ (application w symbol args n)) : Derives Γ (.mem symbol w) := by
  let B := body w symbol args n
  let Δ := Context.add B (raisedContext 3 Γ)
  apply HornBinderRules.eliminate_many 3 B _ ha
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  exact scalar_index_natural (old 3 w) (old 3 symbol) (slot 3 0) (.conjL hB)

theorem output_natural {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w symbol args n : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (application w symbol args n)) : Derives Γ (.mem n w) := by
  let B := body w symbol args n
  let Δ := Context.add B (raisedContext 3 Γ)
  apply HornBinderRules.eliminate_many 3 B _ ha
  have hw3 : Derives Δ (omega (old 3 w)) := of_eq (omega_rename w (old 3)) (HornBinderRules.under_body 3 hw B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  exact StructuralNodeProperties.range (HornBinderRules.zf_body 3 hZ B) (old 3 w) (slot 3 2) (slot 3 1) (old 3 n) hw3 (.conjR (.conjR (.conjR hB)))

end PPAC.Migration.Internal.OriginalFormulaApplicationNaturality
