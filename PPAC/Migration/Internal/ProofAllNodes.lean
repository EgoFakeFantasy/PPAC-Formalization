import PPAC.Migration.Internal.ProofAllNodeSyntax

/-! 六Shape全部赋值块逐项传输；对象公理测试参数保留，未实例化专用ZF/U测试。 -/
namespace PPAC.Migration.Internal.ProofAllNodes
open Source SourceAlgebra SourceLogic OmegaSyntax
open YesMetaZFC.Automation

theorem logical_node_iff {m} {Γ : Context m} (test : Formula 1) (w row : Fin m) :
    Derives Γ ((ProofAllNodeSyntax.node test ObjectProofNode.logicalShape w row).iff (ProofLogicalNodeSyntax.node w row)) := by
  apply HornApplicationBounds.existsMany_congr 3
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  exact ProofAllQueryBundles.logical_bundle_iff test _ _

theorem theory_node_iff {m} {Γ : Context m} (test : Formula 1) (w row : Fin m) :
    Derives Γ ((ProofAllNodeSyntax.node test ObjectProofNode.theoryShape w row).iff (ProofTheoryNodeSyntax.node test w row)) := by
  apply HornApplicationBounds.existsMany_congr 3
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  exact ProofAllQueryBundles.theory_bundle_iff test _ _

theorem mp_node_iff {m} {Γ : Context m} (test : Formula 1) (w row : Fin m) :
    Derives Γ ((ProofAllNodeSyntax.node test ObjectProofNode.mpShape w row).iff (ProofMPNodeSyntax.node w row)) := by
  apply HornApplicationBounds.existsMany_congr 5
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  exact ProofAllQueryBundles.mp_bundle_iff test _ _

theorem forall_node_iff {m} {Γ : Context m} (test : Formula 1) (w row : Fin m) :
    Derives Γ ((ProofAllNodeSyntax.node test ObjectProofNode.forallShape w row).iff (ProofForallNodeSyntax.node w row)) := by
  apply HornApplicationBounds.existsMany_congr 4
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  exact ProofAllQueryBundles.forall_bundle_iff test _ _

theorem strengthening_node_iff {m} {Γ : Context m} (test : Formula 1) (w row : Fin m) :
    Derives Γ ((ProofAllNodeSyntax.node test ObjectProofNode.strengtheningShape w row).iff (ProofStrengtheningNodeSyntax.node w row)) := by
  apply HornApplicationBounds.existsMany_congr 4
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  exact ProofAllQueryBundles.strengthening_bundle_iff test _ _

theorem substitution_node_iff {m} {Γ : Context m} (test : Formula 1) (w row : Fin m) :
    Derives Γ ((ProofAllNodeSyntax.node test ObjectProofNode.substitutionShape w row).iff (ProofSubstitutionNodeSyntax.node w row)) := by
  apply HornApplicationBounds.existsMany_congr 6
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  exact ProofAllQueryBundles.substitution_bundle_iff test _ _

theorem raw_table_iff {m} {Γ : Context m} (test : Formula 1) (w row : Fin m) :
    Derives Γ ((ProofAllNodeSyntax.table test w row).iff (ProofAllNodeSyntax.selected test w row)) := by
  exact (SyntaxTypeLocalTransfer.disj_congr (logical_node_iff test w row) (SyntaxTypeLocalTransfer.disj_congr (theory_node_iff test w row) (SyntaxTypeLocalTransfer.disj_congr (mp_node_iff test w row) (SyntaxTypeLocalTransfer.disj_congr (forall_node_iff test w row) (SyntaxTypeLocalTransfer.disj_congr (strengthening_node_iff test w row) (SyntaxTypeLocalTransfer.disj_congr (substitution_node_iff test w row) (SyntaxTypeLocalTransfer.iff_refl Formula.bot)))))))

theorem selected_iff {m} {Γ : Context m} (test : Formula 1) (hZ : ZFContext.Evidence Γ) (w z row : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) :
    Derives Γ ((ProofAllNodeSyntax.selected test w row).iff (ProofAllNodeSyntax.specification test w z row)) := by
  exact (SyntaxTypeLocalTransfer.disj_congr (ProofLogicalNode.normalized_node_iff hZ w z row hw hz) (SyntaxTypeLocalTransfer.disj_congr (ProofTheoryNode.normalized_node_iff test hZ w z row hw hz) (SyntaxTypeLocalTransfer.disj_congr (ProofMPNode.node_iff hZ w z row hw hz) (SyntaxTypeLocalTransfer.disj_congr (ProofForallNode.normalized_node_iff hZ w z row hw hz) (SyntaxTypeLocalTransfer.disj_congr (ProofStrengtheningNode.node_iff hZ w z row hw hz) (SyntaxTypeLocalTransfer.disj_congr (ProofSubstitutionNode.node_iff hZ w z row hw hz) (SyntaxTypeLocalTransfer.iff_refl Formula.bot)))))))

theorem table_iff {m} {Γ : Context m} (test : Formula 1) (hZ : ZFContext.Evidence Γ) (w z row : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) :
    Derives Γ ((ProofAllNodeSyntax.table test w row).iff (ProofAllNodeSyntax.specification test w z row)) :=
  SyntaxTypeLocalTransfer.iff_trans (raw_table_iff test w row) (selected_iff test hZ w z row hw hz)

end PPAC.Migration.Internal.ProofAllNodes
