import PPAC.Migration.Internal.LogicalAbstractQueryList
import PPAC.Migration.Internal.LogicalInstantiateSyntax

/-! 原20／23／25有序Bool列表与已验收查询bundle的对象对应。 -/
namespace PPAC.Migration.Internal.LogicalOriginalQueryBundles
open Source SourceAlgebra SourceLogic LogicalInstantiateSyntax

theorem original_bundle20_iff {m} {Γ : Context m} (w : Fin m) (env : Fin 4 → Fin m) :
    Derives Γ ((LogicalStaticQueryList.listBundle YesMetaZFC.Automation.ObjectLogicalAxiom.rule20.queries w env).iff (bundle4 w env)) := by
  change Derives Γ (((PureSyntaxExprQuery.query formula4 w env).conj ((PureSyntaxExprQuery.query term4 w env).conj ((OriginalTransformExprQuery.query transform4 w env).conj (HornRuleSyntax.truth)))).iff (bundle4 w env))
  exact (FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _) (FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _) (LogicalAbstractQueryList.trailing_truth _)))

theorem original_bundle23_iff {m} {Γ : Context m} (w : Fin m) (env : Fin 4 → Fin m) :
    Derives Γ ((LogicalStaticQueryList.listBundle YesMetaZFC.Automation.ObjectLogicalAxiom.rule23.queries w env).iff (bundle4 w env)) := by
  change Derives Γ (((PureSyntaxExprQuery.query formula4 w env).conj ((PureSyntaxExprQuery.query term4 w env).conj ((OriginalTransformExprQuery.query transform4 w env).conj (HornRuleSyntax.truth)))).iff (bundle4 w env))
  exact (FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _) (FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _) (LogicalAbstractQueryList.trailing_truth _)))

theorem original_bundle25_iff {m} {Γ : Context m} (w : Fin m) (env : Fin 6 → Fin m) :
    Derives Γ ((LogicalStaticQueryList.listBundle YesMetaZFC.Automation.ObjectLogicalAxiom.rule25.queries w env).iff (bundle6 w env)) := by
  change Derives Γ (((PureSyntaxExprQuery.query leftTerm6 w env).conj ((PureSyntaxExprQuery.query rightTerm6 w env).conj ((PureSyntaxExprQuery.query formula6 w env).conj ((OriginalTransformExprQuery.query leftTransform6 w env).conj ((OriginalTransformExprQuery.query rightTransform6 w env).conj (HornRuleSyntax.truth)))))).iff (bundle6 w env))
  exact (FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _) (FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _) (FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _) (FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _) (LogicalAbstractQueryList.trailing_truth _)))))

end PPAC.Migration.Internal.LogicalOriginalQueryBundles
