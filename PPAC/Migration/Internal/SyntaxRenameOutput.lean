import PPAC.Migration.Internal.SyntaxRenameOutputSyntax

/-! 实际RenameFormula输出纤维的原核类型/存在消去接口；不把合同当总性结论。 -/
namespace PPAC.Migration.Internal.SyntaxRenameOutput
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax SyntaxRenameJudgmentSyntax SyntaxRenameOutputSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem input_of_renamed {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s a b c d n q : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (renamed w r s a b c d n q)) : Derives Γ (input w r s a b c d n) := by
  have hl := SyntaxRenameJudgment.legal w r s a b c d n q hr
  exact .conjI (SyntaxRenameRecursive.source_type hZ w r s a b c d n q hw hr) (.conjI (.conjL hl) (.conjL (.conjR hl)))

theorem output_natural {m} {Γ : Context m} (w r s a b c d n q : Fin m)
    (hr : Derives Γ (renamed w r s a b c d n q)) : Derives Γ (.mem q w) :=
  .conjL (FormulaCodeProperties.guards w q c d (SyntaxRenameJudgment.target_type w r s a b c d n q hr))

theorem input_natural {m} {Γ : Context m} (w r s a b c d n : Fin m)
    (hi : Derives Γ (input w r s a b c d n)) : Derives Γ (.mem n w) :=
  .conjL (FormulaCodeProperties.guards w n a b (.conjL hi))

theorem exists_of_fiber {m} {Γ : Context m} (w r s a b c d n : Fin m)
    (hf : Derives Γ (fiber w r s a b c d n)) : Derives Γ (existsOutput w r s a b c d n) := by
  let B := (renamed w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m)).conj
    (uniqueOutput w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hf
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := intro_exists _ _ _ _ _ _ _ _ (Fin.last m) (.conjL hB)
  exact of_eq (existsOutput_rename w r s a b c d n Fin.castSucc).symm ho
end PPAC.Migration.Internal.SyntaxRenameOutput
