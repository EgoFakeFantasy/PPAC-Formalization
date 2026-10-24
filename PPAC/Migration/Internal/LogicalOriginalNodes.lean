import PPAC.Migration.Internal.LogicalOriginalNodeSyntax

/-! 原27个实际Shape节点与已验收节点逐一传输，最后拼接准确原表。 -/
namespace PPAC.Migration.Internal.LogicalOriginalNodes
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open YesMetaZFC.Automation

theorem rule0_iff {m} {Γ : Context m} (w row : Fin m) :
    Derives Γ ((LogicalOriginalNodeSyntax.node ObjectLogicalAxiom.rule0 w row).iff (LogicalStaticNodeSyntax.node 3 false (ObjectLogicalAxiom.rule0.head) w row)) := by
  apply HornApplicationBounds.existsMany_congr 4
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  rw [LogicalStaticPatterns.rule0_actual_list_bundle]
  exact SyntaxTypeLocalTransfer.iff_refl _

theorem rule1_iff {m} {Γ : Context m} (w row : Fin m) :
    Derives Γ ((LogicalOriginalNodeSyntax.node ObjectLogicalAxiom.rule1 w row).iff (LogicalStaticNodeSyntax.node 1 false (ObjectLogicalAxiom.rule1.head) w row)) := by
  apply HornApplicationBounds.existsMany_congr 2
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  rw [LogicalStaticPatterns.rule1_actual_list_bundle]
  exact SyntaxTypeLocalTransfer.iff_refl _

theorem rule2_iff {m} {Γ : Context m} (w row : Fin m) :
    Derives Γ ((LogicalOriginalNodeSyntax.node ObjectLogicalAxiom.rule2 w row).iff (LogicalStaticNodeSyntax.node 2 false (ObjectLogicalAxiom.rule2.head) w row)) := by
  apply HornApplicationBounds.existsMany_congr 3
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  rw [LogicalStaticPatterns.rule2_actual_list_bundle]
  exact SyntaxTypeLocalTransfer.iff_refl _

theorem rule3_iff {m} {Γ : Context m} (w row : Fin m) :
    Derives Γ ((LogicalOriginalNodeSyntax.node ObjectLogicalAxiom.rule3 w row).iff (LogicalStaticNodeSyntax.node 2 false (ObjectLogicalAxiom.rule3.head) w row)) := by
  apply HornApplicationBounds.existsMany_congr 3
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  rw [LogicalStaticPatterns.rule3_actual_list_bundle]
  exact SyntaxTypeLocalTransfer.iff_refl _

theorem rule4_iff {m} {Γ : Context m} (w row : Fin m) :
    Derives Γ ((LogicalOriginalNodeSyntax.node ObjectLogicalAxiom.rule4 w row).iff (LogicalStaticNodeSyntax.node 1 false (ObjectLogicalAxiom.rule4.head) w row)) := by
  apply HornApplicationBounds.existsMany_congr 2
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  rw [LogicalStaticPatterns.rule4_actual_list_bundle]
  exact SyntaxTypeLocalTransfer.iff_refl _

theorem rule5_iff {m} {Γ : Context m} (w row : Fin m) :
    Derives Γ ((LogicalOriginalNodeSyntax.node ObjectLogicalAxiom.rule5 w row).iff (LogicalStaticNodeSyntax.node 2 false (ObjectLogicalAxiom.rule5.head) w row)) := by
  apply HornApplicationBounds.existsMany_congr 3
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  rw [LogicalStaticPatterns.rule5_actual_list_bundle]
  exact SyntaxTypeLocalTransfer.iff_refl _

theorem rule6_iff {m} {Γ : Context m} (w row : Fin m) :
    Derives Γ ((LogicalOriginalNodeSyntax.node ObjectLogicalAxiom.rule6 w row).iff (LogicalStaticNodeSyntax.node 2 false (ObjectLogicalAxiom.rule6.head) w row)) := by
  apply HornApplicationBounds.existsMany_congr 3
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  rw [LogicalStaticPatterns.rule6_actual_list_bundle]
  exact SyntaxTypeLocalTransfer.iff_refl _

theorem rule7_iff {m} {Γ : Context m} (w row : Fin m) :
    Derives Γ ((LogicalOriginalNodeSyntax.node ObjectLogicalAxiom.rule7 w row).iff (LogicalStaticNodeSyntax.node 0 false (ObjectLogicalAxiom.rule7.head) w row)) := by
  apply HornApplicationBounds.existsMany_congr 1
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  rw [LogicalStaticPatterns.rule7_actual_list_bundle]
  exact SyntaxTypeLocalTransfer.iff_refl _

theorem rule8_iff {m} {Γ : Context m} (w row : Fin m) :
    Derives Γ ((LogicalOriginalNodeSyntax.node ObjectLogicalAxiom.rule8 w row).iff (LogicalStaticNodeSyntax.node 1 false (ObjectLogicalAxiom.rule8.head) w row)) := by
  apply HornApplicationBounds.existsMany_congr 2
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  rw [LogicalStaticPatterns.rule8_actual_list_bundle]
  exact SyntaxTypeLocalTransfer.iff_refl _

theorem rule9_iff {m} {Γ : Context m} (w row : Fin m) :
    Derives Γ ((LogicalOriginalNodeSyntax.node ObjectLogicalAxiom.rule9 w row).iff (LogicalStaticNodeSyntax.node 1 false (ObjectLogicalAxiom.rule9.head) w row)) := by
  apply HornApplicationBounds.existsMany_congr 2
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  rw [LogicalStaticPatterns.rule9_actual_list_bundle]
  exact SyntaxTypeLocalTransfer.iff_refl _

theorem rule10_iff {m} {Γ : Context m} (w row : Fin m) :
    Derives Γ ((LogicalOriginalNodeSyntax.node ObjectLogicalAxiom.rule10 w row).iff (LogicalStaticNodeSyntax.node 1 false (ObjectLogicalAxiom.rule10.head) w row)) := by
  apply HornApplicationBounds.existsMany_congr 2
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  rw [LogicalStaticPatterns.rule10_actual_list_bundle]
  exact SyntaxTypeLocalTransfer.iff_refl _

theorem rule11_iff {m} {Γ : Context m} (w row : Fin m) :
    Derives Γ ((LogicalOriginalNodeSyntax.node ObjectLogicalAxiom.rule11 w row).iff (LogicalStaticNodeSyntax.node 2 false (ObjectLogicalAxiom.rule11.head) w row)) := by
  apply HornApplicationBounds.existsMany_congr 3
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  rw [LogicalStaticPatterns.rule11_actual_list_bundle]
  exact SyntaxTypeLocalTransfer.iff_refl _

theorem rule12_iff {m} {Γ : Context m} (w row : Fin m) :
    Derives Γ ((LogicalOriginalNodeSyntax.node ObjectLogicalAxiom.rule12 w row).iff (LogicalStaticNodeSyntax.node 2 false (ObjectLogicalAxiom.rule12.head) w row)) := by
  apply HornApplicationBounds.existsMany_congr 3
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  rw [LogicalStaticPatterns.rule12_actual_list_bundle]
  exact SyntaxTypeLocalTransfer.iff_refl _

theorem rule13_iff {m} {Γ : Context m} (w row : Fin m) :
    Derives Γ ((LogicalOriginalNodeSyntax.node ObjectLogicalAxiom.rule13 w row).iff (LogicalStaticNodeSyntax.node 2 false (ObjectLogicalAxiom.rule13.head) w row)) := by
  apply HornApplicationBounds.existsMany_congr 3
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  rw [LogicalStaticPatterns.rule13_actual_list_bundle]
  exact SyntaxTypeLocalTransfer.iff_refl _

theorem rule14_iff {m} {Γ : Context m} (w row : Fin m) :
    Derives Γ ((LogicalOriginalNodeSyntax.node ObjectLogicalAxiom.rule14 w row).iff (LogicalStaticNodeSyntax.node 2 false (ObjectLogicalAxiom.rule14.head) w row)) := by
  apply HornApplicationBounds.existsMany_congr 3
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  rw [LogicalStaticPatterns.rule14_actual_list_bundle]
  exact SyntaxTypeLocalTransfer.iff_refl _

theorem rule15_iff {m} {Γ : Context m} (w row : Fin m) :
    Derives Γ ((LogicalOriginalNodeSyntax.node ObjectLogicalAxiom.rule15 w row).iff (LogicalStaticNodeSyntax.node 2 false (ObjectLogicalAxiom.rule15.head) w row)) := by
  apply HornApplicationBounds.existsMany_congr 3
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  rw [LogicalStaticPatterns.rule15_actual_list_bundle]
  exact SyntaxTypeLocalTransfer.iff_refl _

theorem rule16_iff {m} {Γ : Context m} (w row : Fin m) :
    Derives Γ ((LogicalOriginalNodeSyntax.node ObjectLogicalAxiom.rule16 w row).iff (LogicalStaticNodeSyntax.node 3 false (ObjectLogicalAxiom.rule16.head) w row)) := by
  apply HornApplicationBounds.existsMany_congr 4
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  rw [LogicalStaticPatterns.rule16_actual_list_bundle]
  exact SyntaxTypeLocalTransfer.iff_refl _

theorem rule17_iff {m} {Γ : Context m} (w row : Fin m) :
    Derives Γ ((LogicalOriginalNodeSyntax.node ObjectLogicalAxiom.rule17 w row).iff (LogicalStaticNodeSyntax.node 2 false (ObjectLogicalAxiom.rule17.head) w row)) := by
  apply HornApplicationBounds.existsMany_congr 3
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  rw [LogicalStaticPatterns.rule17_actual_list_bundle]
  exact SyntaxTypeLocalTransfer.iff_refl _

theorem rule18_iff {m} {Γ : Context m} (w row : Fin m) :
    Derives Γ ((LogicalOriginalNodeSyntax.node ObjectLogicalAxiom.rule18 w row).iff (LogicalStaticNodeSyntax.node 2 false (ObjectLogicalAxiom.rule18.head) w row)) := by
  apply HornApplicationBounds.existsMany_congr 3
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  rw [LogicalStaticPatterns.rule18_actual_list_bundle]
  exact SyntaxTypeLocalTransfer.iff_refl _

theorem rule19_iff {m} {Γ : Context m} (w row : Fin m) :
    Derives Γ ((LogicalOriginalNodeSyntax.node ObjectLogicalAxiom.rule19 w row).iff (LogicalStaticNodeSyntax.node 2 false (ObjectLogicalAxiom.rule19.head) w row)) := by
  apply HornApplicationBounds.existsMany_congr 3
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  rw [LogicalStaticPatterns.rule19_actual_list_bundle]
  exact SyntaxTypeLocalTransfer.iff_refl _

theorem rule20_iff {m} {Γ : Context m} (w row : Fin m) :
    Derives Γ ((LogicalOriginalNodeSyntax.node ObjectLogicalAxiom.rule20 w row).iff (LogicalInstantiateNodeSyntax.node4 true w row)) := by
  apply HornApplicationBounds.existsMany_congr 4
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  exact LogicalOriginalQueryBundles.original_bundle20_iff _ _

theorem rule21_iff {m} {Γ : Context m} (w row : Fin m) :
    Derives Γ ((LogicalOriginalNodeSyntax.node ObjectLogicalAxiom.rule21 w row).iff (LogicalAbstractNodeSyntax.node21 w row)) := by
  apply HornApplicationBounds.existsMany_congr 5
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  exact LogicalAbstractQueryList.original_bundle21_iff _ _

theorem rule22_iff {m} {Γ : Context m} (w row : Fin m) :
    Derives Γ ((LogicalOriginalNodeSyntax.node ObjectLogicalAxiom.rule22 w row).iff (LogicalStaticNodeSyntax.node 1 false (ObjectLogicalAxiom.rule22.head) w row)) := by
  apply HornApplicationBounds.existsMany_congr 2
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  rw [LogicalStaticPatterns.rule22_actual_list_bundle]
  exact SyntaxTypeLocalTransfer.iff_refl _

theorem rule23_iff {m} {Γ : Context m} (w row : Fin m) :
    Derives Γ ((LogicalOriginalNodeSyntax.node ObjectLogicalAxiom.rule23 w row).iff (LogicalInstantiateNodeSyntax.node4 false w row)) := by
  apply HornApplicationBounds.existsMany_congr 4
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  exact LogicalOriginalQueryBundles.original_bundle23_iff _ _

theorem rule24_iff {m} {Γ : Context m} (w row : Fin m) :
    Derives Γ ((LogicalOriginalNodeSyntax.node ObjectLogicalAxiom.rule24 w row).iff (LogicalAbstractNodeSyntax.node24 w row)) := by
  apply HornApplicationBounds.existsMany_congr 4
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  exact LogicalAbstractQueryList.original_bundle24_iff _ _

theorem rule25_iff {m} {Γ : Context m} (w row : Fin m) :
    Derives Γ ((LogicalOriginalNodeSyntax.node ObjectLogicalAxiom.rule25 w row).iff (LogicalInstantiateNodeSyntax.node6 w row)) := by
  apply HornApplicationBounds.existsMany_congr 6
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  exact LogicalOriginalQueryBundles.original_bundle25_iff _ _

theorem rule26_iff {m} {Γ : Context m} (w row : Fin m) :
    Derives Γ ((LogicalOriginalNodeSyntax.node ObjectLogicalAxiom.rule26 w row).iff (LogicalStaticNodeSyntax.node 1 true (ObjectLogicalAxiom.rule26.head) w row)) := by
  apply HornApplicationBounds.existsMany_congr 2
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  apply FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
  rw [LogicalStaticPatterns.rule26_actual_list_bundle]
  exact SyntaxTypeLocalTransfer.iff_refl _

theorem raw_table_iff {m} {Γ : Context m} (w row : Fin m) :
    Derives Γ ((LogicalOriginalNodeSyntax.table w row).iff (LogicalAllPatterns.node w row)) := by
  exact (SyntaxTypeLocalTransfer.disj_congr (rule0_iff w row) (SyntaxTypeLocalTransfer.disj_congr (rule1_iff w row) (SyntaxTypeLocalTransfer.disj_congr (rule2_iff w row) (SyntaxTypeLocalTransfer.disj_congr (rule3_iff w row) (SyntaxTypeLocalTransfer.disj_congr (rule4_iff w row) (SyntaxTypeLocalTransfer.disj_congr (rule5_iff w row) (SyntaxTypeLocalTransfer.disj_congr (rule6_iff w row) (SyntaxTypeLocalTransfer.disj_congr (rule7_iff w row) (SyntaxTypeLocalTransfer.disj_congr (rule8_iff w row) (SyntaxTypeLocalTransfer.disj_congr (rule9_iff w row) (SyntaxTypeLocalTransfer.disj_congr (rule10_iff w row) (SyntaxTypeLocalTransfer.disj_congr (rule11_iff w row) (SyntaxTypeLocalTransfer.disj_congr (rule12_iff w row) (SyntaxTypeLocalTransfer.disj_congr (rule13_iff w row) (SyntaxTypeLocalTransfer.disj_congr (rule14_iff w row) (SyntaxTypeLocalTransfer.disj_congr (rule15_iff w row) (SyntaxTypeLocalTransfer.disj_congr (rule16_iff w row) (SyntaxTypeLocalTransfer.disj_congr (rule17_iff w row) (SyntaxTypeLocalTransfer.disj_congr (rule18_iff w row) (SyntaxTypeLocalTransfer.disj_congr (rule19_iff w row) (SyntaxTypeLocalTransfer.disj_congr (rule20_iff w row) (SyntaxTypeLocalTransfer.disj_congr (rule21_iff w row) (SyntaxTypeLocalTransfer.disj_congr (rule22_iff w row) (SyntaxTypeLocalTransfer.disj_congr (rule23_iff w row) (SyntaxTypeLocalTransfer.disj_congr (rule24_iff w row) (SyntaxTypeLocalTransfer.disj_congr (rule25_iff w row) (SyntaxTypeLocalTransfer.disj_congr (rule26_iff w row) (SyntaxTypeLocalTransfer.iff_refl Formula.bot))))))))))))))))))))))))))))

theorem table_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z row : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) :
    Derives Γ ((LogicalOriginalNodeSyntax.table w row).iff (LogicalAllPatterns.specification w z row)) :=
  SyntaxTypeLocalTransfer.iff_trans (raw_table_iff w row) (LogicalAllPatterns.node_iff hZ w z row hw hz)

end PPAC.Migration.Internal.LogicalOriginalNodes
