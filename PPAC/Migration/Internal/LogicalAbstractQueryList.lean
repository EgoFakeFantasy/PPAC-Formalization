import PPAC.Migration.Internal.LogicalAbstractSyntax

/-! 实际原有序Bool表解释与无多余末truth的bundle对象等价。 -/
namespace PPAC.Migration.Internal.LogicalAbstractQueryList
open Source SourceAlgebra SourceLogic LogicalAbstractSyntax

theorem trailing_truth {m} {Γ : Context m} (p : Formula m) :
    Derives Γ ((p.conj HornRuleSyntax.truth).iff p) := by
  apply Derives.conjI
  · exact .impI (.conjL (.hyp (Or.inl rfl)))
  · exact .impI (.conjI (.hyp (Or.inl rfl)) HornRuleSyntax.truth_proved)

theorem original_bundle21_iff {m} {Γ : Context m} (w : Fin m) (env : Fin 5 → Fin m) :
    Derives Γ ((LogicalStaticQueryList.listBundle YesMetaZFC.Automation.ObjectLogicalAxiom.rule21.queries w env).iff (bundle21 w env)) := by
  change Derives Γ (((PureSyntaxExprQuery.query leftFormula21 w env).conj
    ((PureSyntaxExprQuery.query rightFormula21 w env).conj
      ((OriginalTransformExprQuery.query leftTransform21 w env).conj
        ((OriginalTransformExprQuery.query rightTransform21 w env).conj HornRuleSyntax.truth)))).iff (bundle21 w env))
  exact FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
    (FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
      (FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _) (trailing_truth _)))

theorem original_bundle24_iff {m} {Γ : Context m} (w : Fin m) (env : Fin 4 → Fin m) :
    Derives Γ ((LogicalStaticQueryList.listBundle YesMetaZFC.Automation.ObjectLogicalAxiom.rule24.queries w env).iff (bundle24 w env)) := by
  change Derives Γ (((PureSyntaxExprQuery.query leftFormula24 w env).conj
    ((PureSyntaxExprQuery.query rightFormula24 w env).conj
      ((OriginalTransformExprQuery.query leftTransform24 w env).conj HornRuleSyntax.truth))).iff (bundle24 w env))
  exact FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
    (FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _) (trailing_truth _))

end PPAC.Migration.Internal.LogicalAbstractQueryList
