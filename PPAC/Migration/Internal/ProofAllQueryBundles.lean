import PPAC.Migration.Internal.ProofAllQuerySyntax

/-! 原每个Kind有序查询列表与既有六个接受bundle双条件。 -/
namespace PPAC.Migration.Internal.ProofAllQueryBundles
open Source SourceAlgebra SourceLogic
open YesMetaZFC.Automation

theorem logical_bundle_iff {m} {Γ : Context m} (test : Formula 1) (w : Fin m) (env : Fin 3 → Fin m) :
    Derives Γ ((ProofAllQuerySyntax.listBundle test ObjectProofNode.logicalShape.queries w env).iff (ProofLogicalSyntax.bundle w env)) := by
  change Derives Γ (((ProofAllQuerySyntax.query test (ObjectProofNode.logicalShape.queries[0]).1 (ObjectProofNode.logicalShape.queries[0]).2 w env).conj (HornRuleSyntax.truth)).iff (ProofLogicalSyntax.bundle w env))
  exact (LogicalAbstractQueryList.trailing_truth _)

theorem theory_bundle_iff {m} {Γ : Context m} (test : Formula 1) (w : Fin m) (env : Fin 3 → Fin m) :
    Derives Γ ((ProofAllQuerySyntax.listBundle test ObjectProofNode.theoryShape.queries w env).iff (ProofTheorySyntax.bundle test w env)) := by
  change Derives Γ (((ProofAllQuerySyntax.query test (ObjectProofNode.theoryShape.queries[0]).1 (ObjectProofNode.theoryShape.queries[0]).2 w env).conj ((ProofAllQuerySyntax.query test (ObjectProofNode.theoryShape.queries[1]).1 (ObjectProofNode.theoryShape.queries[1]).2 w env).conj (HornRuleSyntax.truth))).iff (ProofTheorySyntax.bundle test w env))
  exact (FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _) (LogicalAbstractQueryList.trailing_truth _))

theorem mp_bundle_iff {m} {Γ : Context m} (test : Formula 1) (w : Fin m) (env : Fin 5 → Fin m) :
    Derives Γ ((ProofAllQuerySyntax.listBundle test ObjectProofNode.mpShape.queries w env).iff (ProofMPAllQueries.bundle w env)) := by
  change Derives Γ (((ProofAllQuerySyntax.query test (ObjectProofNode.mpShape.queries[0]).1 (ObjectProofNode.mpShape.queries[0]).2 w env).conj ((ProofAllQuerySyntax.query test (ObjectProofNode.mpShape.queries[1]).1 (ObjectProofNode.mpShape.queries[1]).2 w env).conj ((ProofAllQuerySyntax.query test (ObjectProofNode.mpShape.queries[2]).1 (ObjectProofNode.mpShape.queries[2]).2 w env).conj ((ProofAllQuerySyntax.query test (ObjectProofNode.mpShape.queries[3]).1 (ObjectProofNode.mpShape.queries[3]).2 w env).conj ((ProofAllQuerySyntax.query test (ObjectProofNode.mpShape.queries[4]).1 (ObjectProofNode.mpShape.queries[4]).2 w env).conj ((ProofAllQuerySyntax.query test (ObjectProofNode.mpShape.queries[5]).1 (ObjectProofNode.mpShape.queries[5]).2 w env).conj (HornRuleSyntax.truth))))))).iff (ProofMPAllQueries.bundle w env))
  exact (FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _) (FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _) (FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _) (FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _) (FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _) (LogicalAbstractQueryList.trailing_truth _))))))

theorem forall_bundle_iff {m} {Γ : Context m} (test : Formula 1) (w : Fin m) (env : Fin 4 → Fin m) :
    Derives Γ ((ProofAllQuerySyntax.listBundle test ObjectProofNode.forallShape.queries w env).iff (ProofForallSyntax.bundle w env)) := by
  change Derives Γ (((ProofAllQuerySyntax.query test (ObjectProofNode.forallShape.queries[0]).1 (ObjectProofNode.forallShape.queries[0]).2 w env).conj ((ProofAllQuerySyntax.query test (ObjectProofNode.forallShape.queries[1]).1 (ObjectProofNode.forallShape.queries[1]).2 w env).conj ((ProofAllQuerySyntax.query test (ObjectProofNode.forallShape.queries[2]).1 (ObjectProofNode.forallShape.queries[2]).2 w env).conj ((ProofAllQuerySyntax.query test (ObjectProofNode.forallShape.queries[3]).1 (ObjectProofNode.forallShape.queries[3]).2 w env).conj (HornRuleSyntax.truth))))).iff (ProofForallSyntax.bundle w env))
  exact (FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _) (FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _) (FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _) (LogicalAbstractQueryList.trailing_truth _))))

theorem strengthening_bundle_iff {m} {Γ : Context m} (test : Formula 1) (w : Fin m) (env : Fin 4 → Fin m) :
    Derives Γ ((ProofAllQuerySyntax.listBundle test ObjectProofNode.strengtheningShape.queries w env).iff (ProofStrengtheningSyntax.bundle w env)) := by
  change Derives Γ (((ProofAllQuerySyntax.query test (ObjectProofNode.strengtheningShape.queries[0]).1 (ObjectProofNode.strengtheningShape.queries[0]).2 w env).conj ((ProofAllQuerySyntax.query test (ObjectProofNode.strengtheningShape.queries[1]).1 (ObjectProofNode.strengtheningShape.queries[1]).2 w env).conj ((ProofAllQuerySyntax.query test (ObjectProofNode.strengtheningShape.queries[2]).1 (ObjectProofNode.strengtheningShape.queries[2]).2 w env).conj ((ProofAllQuerySyntax.query test (ObjectProofNode.strengtheningShape.queries[3]).1 (ObjectProofNode.strengtheningShape.queries[3]).2 w env).conj (HornRuleSyntax.truth))))).iff (ProofStrengtheningSyntax.bundle w env))
  exact (FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _) (FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _) (FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _) (LogicalAbstractQueryList.trailing_truth _))))

theorem substitution_bundle_iff {m} {Γ : Context m} (test : Formula 1) (w : Fin m) (env : Fin 6 → Fin m) :
    Derives Γ ((ProofAllQuerySyntax.listBundle test ObjectProofNode.substitutionShape.queries w env).iff (ProofSubstitutionAllQueries.bundle w env)) := by
  change Derives Γ (((ProofAllQuerySyntax.query test (ObjectProofNode.substitutionShape.queries[0]).1 (ObjectProofNode.substitutionShape.queries[0]).2 w env).conj ((ProofAllQuerySyntax.query test (ObjectProofNode.substitutionShape.queries[1]).1 (ObjectProofNode.substitutionShape.queries[1]).2 w env).conj ((ProofAllQuerySyntax.query test (ObjectProofNode.substitutionShape.queries[2]).1 (ObjectProofNode.substitutionShape.queries[2]).2 w env).conj ((ProofAllQuerySyntax.query test (ObjectProofNode.substitutionShape.queries[3]).1 (ObjectProofNode.substitutionShape.queries[3]).2 w env).conj ((ProofAllQuerySyntax.query test (ObjectProofNode.substitutionShape.queries[4]).1 (ObjectProofNode.substitutionShape.queries[4]).2 w env).conj (HornRuleSyntax.truth)))))).iff (ProofSubstitutionAllQueries.bundle w env))
  exact (FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _) (FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _) (FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _) (FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _) (LogicalAbstractQueryList.trailing_truth _)))))

end PPAC.Migration.Internal.ProofAllQueryBundles
