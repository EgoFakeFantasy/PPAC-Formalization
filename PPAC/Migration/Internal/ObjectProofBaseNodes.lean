import PPAC.Migration.Internal.ProofAllNodes

/-! 原逻辑证明节点、参数化理论节点及准确六规则纯关系局部表的原核闭句；ZF/U测试未实例化。 -/
namespace PPAC.Migration.Internal.ObjectProofBaseNodes
open Source SourceAlgebra SourceLogic OmegaSyntax

def proofLogicalNumericHeadIffSentence {m} (env : Fin 3 → Fin m) (w row : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 3 w env).imp (((HornExprSyntax.graph YesMetaZFC.Automation.ObjectProofNode.logicalShape.head w env row).iff (SyntaxNodeSyntax.constructor 3 0 w env row))))).close

theorem source_proofLogicalNumericHeadIff {m} (env : Fin 3 → Fin m) (w row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (proofLogicalNumericHeadIffSentence env w row) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.environmentNat 3 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 3 w env) := .hyp (Or.inl rfl)
  exact ProofLogicalQueries.head_iff hZ w row env h0 h1

theorem proofLogicalNumericHeadIff_kernel_certificate {m} (env : Fin 3 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (proofLogicalNumericHeadIffSentence env w row)) := TheoryTransport.sentence (source_proofLogicalNumericHeadIff env w row)

theorem native_proofLogicalNumericHeadIff {m} (env : Fin 3 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (proofLogicalNumericHeadIffSentence env w row)) := ZFReplay.replay (proofLogicalNumericHeadIff_kernel_certificate env w row)

def proofLogicalQueryConstructorIffSentence {m} (env : Fin 3 → Fin m) (w : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 3 w env).imp (((ProofLogicalSyntax.bundle w env).iff (OriginalLogicalExprQuery.rowQuery 3 0 w (ProofLogicalSyntax.queryFields env)))))).close

theorem source_proofLogicalQueryConstructorIff {m} (env : Fin 3 → Fin m) (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (proofLogicalQueryConstructorIffSentence env w) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.environmentNat 3 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 3 w env) := .hyp (Or.inl rfl)
  exact ProofLogicalQueries.query_constructor_iff hZ w env h0 h1

theorem proofLogicalQueryConstructorIff_kernel_certificate {m} (env : Fin 3 → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (proofLogicalQueryConstructorIffSentence env w)) := TheoryTransport.sentence (source_proofLogicalQueryConstructorIff env w)

theorem native_proofLogicalQueryConstructorIff {m} (env : Fin 3 → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (proofLogicalQueryConstructorIffSentence env w)) := ZFReplay.replay (proofLogicalQueryConstructorIff_kernel_certificate env w)

def proofLogicalQueryNormalizedIffSentence {m} (env : Fin 3 → Fin m) (w z : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 3 w env).imp ((empty z).imp (((ProofLogicalSyntax.bundle w env).iff (ProofLogicalSyntax.specification w z env)))))).close

theorem source_proofLogicalQueryNormalizedIff {m} (env : Fin 3 → Fin m) (w z : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (proofLogicalQueryNormalizedIffSentence env w z) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (empty z) (Context.add (HornExprSyntax.environmentNat 3 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 3 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (empty z) := .hyp (Or.inl rfl)
  exact ProofLogicalQueries.query_normalized_iff hZ w z env h0 h1 h2

theorem proofLogicalQueryNormalizedIff_kernel_certificate {m} (env : Fin 3 → Fin m) (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (proofLogicalQueryNormalizedIffSentence env w z)) := TheoryTransport.sentence (source_proofLogicalQueryNormalizedIff env w z)

theorem native_proofLogicalQueryNormalizedIff {m} (env : Fin 3 → Fin m) (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (proofLogicalQueryNormalizedIffSentence env w z)) := ZFReplay.replay (proofLogicalQueryNormalizedIff_kernel_certificate env w z)

def proofLogicalAllAssignmentBoundsSentence {m} (env : Fin 3 → Fin m) (w row : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 3 w env).imp ((HornExprSyntax.graph YesMetaZFC.Automation.ObjectProofNode.logicalShape.head w env row).imp ((HornExprBounds.environmentBound 3 row env))))).close

theorem source_proofLogicalAllAssignmentBounds {m} (env : Fin 3 → Fin m) (w row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (proofLogicalAllAssignmentBoundsSentence env w row) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.graph YesMetaZFC.Automation.ObjectProofNode.logicalShape.head w env row) (Context.add (HornExprSyntax.environmentNat 3 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 3 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (HornExprSyntax.graph YesMetaZFC.Automation.ObjectProofNode.logicalShape.head w env row) := .hyp (Or.inl rfl)
  exact ProofLogicalQueries.all_assignment_bounds hZ w row env h0 h1 h2

theorem proofLogicalAllAssignmentBounds_kernel_certificate {m} (env : Fin 3 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (proofLogicalAllAssignmentBoundsSentence env w row)) := TheoryTransport.sentence (source_proofLogicalAllAssignmentBounds env w row)

theorem native_proofLogicalAllAssignmentBounds {m} (env : Fin 3 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (proofLogicalAllAssignmentBoundsSentence env w row)) := ZFReplay.replay (proofLogicalAllAssignmentBounds_kernel_certificate env w row)

def proofLogicalBoundedMatrixIffSentence {m} (env : Fin 3 → Fin m) (w z row : Fin m) : Source.Sentence := ((omega w).imp ((empty z).imp (((ProofLogicalNodeSyntax.boundedMatrix w row env).iff (ProofLogicalNodeSyntax.normalizedMatrix w z row env))))).close

theorem source_proofLogicalBoundedMatrixIff {m} (env : Fin 3 → Fin m) (w z row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (proofLogicalBoundedMatrixIffSentence env w z row) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (empty z) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (empty z) := .hyp (Or.inl rfl)
  exact ProofLogicalNode.matrix_iff hZ w z row env h0 h1

theorem proofLogicalBoundedMatrixIff_kernel_certificate {m} (env : Fin 3 → Fin m) (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (proofLogicalBoundedMatrixIffSentence env w z row)) := TheoryTransport.sentence (source_proofLogicalBoundedMatrixIff env w z row)

theorem native_proofLogicalBoundedMatrixIff {m} (env : Fin 3 → Fin m) (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (proofLogicalBoundedMatrixIffSentence env w z row)) := ZFReplay.replay (proofLogicalBoundedMatrixIff_kernel_certificate env w z row)

def proofLogicalWholeNodeIffSentence {m} (w z row : Fin m) : Source.Sentence := ((omega w).imp ((empty z).imp (((ProofLogicalNodeSyntax.node w row).iff (ProofLogicalNodeSyntax.normalized w z row))))).close

theorem source_proofLogicalWholeNodeIff {m} (w z row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (proofLogicalWholeNodeIffSentence w z row) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (empty z) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (empty z) := .hyp (Or.inl rfl)
  exact ProofLogicalNode.normalized_node_iff hZ w z row h0 h1

theorem proofLogicalWholeNodeIff_kernel_certificate {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (proofLogicalWholeNodeIffSentence w z row)) := TheoryTransport.sentence (source_proofLogicalWholeNodeIff w z row)

theorem native_proofLogicalWholeNodeIff {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (proofLogicalWholeNodeIffSentence w z row)) := ZFReplay.replay (proofLogicalWholeNodeIff_kernel_certificate w z row)

def proofTheoryNumericHeadIffSentence {m} (env : Fin 3 → Fin m) (w row : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 3 w env).imp (((HornExprSyntax.graph YesMetaZFC.Automation.ObjectProofNode.theoryShape.head w env row).iff (SyntaxNodeSyntax.constructor 3 1 w env row))))).close

theorem source_proofTheoryNumericHeadIff {m} (env : Fin 3 → Fin m) (w row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (proofTheoryNumericHeadIffSentence env w row) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.environmentNat 3 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 3 w env) := .hyp (Or.inl rfl)
  exact ProofTheoryQueries.head_iff hZ w row env h0 h1

theorem proofTheoryNumericHeadIff_kernel_certificate {m} (env : Fin 3 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (proofTheoryNumericHeadIffSentence env w row)) := TheoryTransport.sentence (source_proofTheoryNumericHeadIff env w row)

theorem native_proofTheoryNumericHeadIff {m} (env : Fin 3 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (proofTheoryNumericHeadIffSentence env w row)) := ZFReplay.replay (proofTheoryNumericHeadIff_kernel_certificate env w row)

def proofTheoryFormulaQueryIffSentence {m} (env : Fin 3 → Fin m) (w z : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 3 w env).imp ((empty z).imp (((PureSyntaxExprQuery.query ProofTheorySyntax.formulaExpr w env).iff (FormulaCodeSyntax.formulaCode w (env 1) z (env 0))))))).close

theorem source_proofTheoryFormulaQueryIff {m} (env : Fin 3 → Fin m) (w z : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (proofTheoryFormulaQueryIffSentence env w z) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (empty z) (Context.add (HornExprSyntax.environmentNat 3 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 3 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (empty z) := .hyp (Or.inl rfl)
  exact ProofTheoryQueries.formula_iff hZ w z env h0 h1 h2

theorem proofTheoryFormulaQueryIff_kernel_certificate {m} (env : Fin 3 → Fin m) (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (proofTheoryFormulaQueryIffSentence env w z)) := TheoryTransport.sentence (source_proofTheoryFormulaQueryIff env w z)

theorem native_proofTheoryFormulaQueryIff {m} (env : Fin 3 → Fin m) (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (proofTheoryFormulaQueryIffSentence env w z)) := ZFReplay.replay (proofTheoryFormulaQueryIff_kernel_certificate env w z)

def proofTheoryParameterizedAxiomQueryIffSentence {m} (test : Source.Formula 1) (env : Fin 3 → Fin m) (w : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 3 w env).imp (((OriginalAxiomExprQuery.query test ProofTheorySyntax.axiomExpr w env).iff (OriginalAxiomExprQuery.rowQuery test 2 0 w (ProofTheorySyntax.axiomFields env)))))).close

theorem source_proofTheoryParameterizedAxiomQueryIff {m} (test : Source.Formula 1) (env : Fin 3 → Fin m) (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (proofTheoryParameterizedAxiomQueryIffSentence test env w) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.environmentNat 3 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 3 w env) := .hyp (Or.inl rfl)
  exact ProofTheoryQueries.axiom_constructor_iff test hZ w env h0 h1

theorem proofTheoryParameterizedAxiomQueryIff_kernel_certificate {m} (test : Source.Formula 1) (env : Fin 3 → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (proofTheoryParameterizedAxiomQueryIffSentence test env w)) := TheoryTransport.sentence (source_proofTheoryParameterizedAxiomQueryIff test env w)

theorem native_proofTheoryParameterizedAxiomQueryIff {m} (test : Source.Formula 1) (env : Fin 3 → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (proofTheoryParameterizedAxiomQueryIffSentence test env w)) := ZFReplay.replay (proofTheoryParameterizedAxiomQueryIff_kernel_certificate test env w)

def proofTheoryParameterizedAllQueriesIffSentence {m} (test : Source.Formula 1) (env : Fin 3 → Fin m) (w z : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 3 w env).imp ((empty z).imp (((ProofTheorySyntax.bundle test w env).iff (ProofTheorySyntax.specification test w z env)))))).close

theorem source_proofTheoryParameterizedAllQueriesIff {m} (test : Source.Formula 1) (env : Fin 3 → Fin m) (w z : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (proofTheoryParameterizedAllQueriesIffSentence test env w z) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (empty z) (Context.add (HornExprSyntax.environmentNat 3 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 3 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (empty z) := .hyp (Or.inl rfl)
  exact ProofTheoryQueries.bundle_iff test hZ w z env h0 h1 h2

theorem proofTheoryParameterizedAllQueriesIff_kernel_certificate {m} (test : Source.Formula 1) (env : Fin 3 → Fin m) (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (proofTheoryParameterizedAllQueriesIffSentence test env w z)) := TheoryTransport.sentence (source_proofTheoryParameterizedAllQueriesIff test env w z)

theorem native_proofTheoryParameterizedAllQueriesIff {m} (test : Source.Formula 1) (env : Fin 3 → Fin m) (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (proofTheoryParameterizedAllQueriesIffSentence test env w z)) := ZFReplay.replay (proofTheoryParameterizedAllQueriesIff_kernel_certificate test env w z)

def proofTheoryAllAssignmentBoundsSentence {m} (env : Fin 3 → Fin m) (w row : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 3 w env).imp ((HornExprSyntax.graph YesMetaZFC.Automation.ObjectProofNode.theoryShape.head w env row).imp ((HornExprBounds.environmentBound 3 row env))))).close

theorem source_proofTheoryAllAssignmentBounds {m} (env : Fin 3 → Fin m) (w row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (proofTheoryAllAssignmentBoundsSentence env w row) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.graph YesMetaZFC.Automation.ObjectProofNode.theoryShape.head w env row) (Context.add (HornExprSyntax.environmentNat 3 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 3 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (HornExprSyntax.graph YesMetaZFC.Automation.ObjectProofNode.theoryShape.head w env row) := .hyp (Or.inl rfl)
  exact ProofTheoryQueries.all_assignment_bounds hZ w row env h0 h1 h2

theorem proofTheoryAllAssignmentBounds_kernel_certificate {m} (env : Fin 3 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (proofTheoryAllAssignmentBoundsSentence env w row)) := TheoryTransport.sentence (source_proofTheoryAllAssignmentBounds env w row)

theorem native_proofTheoryAllAssignmentBounds {m} (env : Fin 3 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (proofTheoryAllAssignmentBoundsSentence env w row)) := ZFReplay.replay (proofTheoryAllAssignmentBounds_kernel_certificate env w row)

def proofTheoryParameterizedBoundedMatrixIffSentence {m} (test : Source.Formula 1) (env : Fin 3 → Fin m) (w z row : Fin m) : Source.Sentence := ((omega w).imp ((empty z).imp (((ProofTheoryNodeSyntax.boundedMatrix test w row env).iff (ProofTheoryNodeSyntax.normalizedMatrix test w z row env))))).close

theorem source_proofTheoryParameterizedBoundedMatrixIff {m} (test : Source.Formula 1) (env : Fin 3 → Fin m) (w z row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (proofTheoryParameterizedBoundedMatrixIffSentence test env w z row) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (empty z) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (empty z) := .hyp (Or.inl rfl)
  exact ProofTheoryNode.matrix_iff test hZ w z row env h0 h1

theorem proofTheoryParameterizedBoundedMatrixIff_kernel_certificate {m} (test : Source.Formula 1) (env : Fin 3 → Fin m) (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (proofTheoryParameterizedBoundedMatrixIffSentence test env w z row)) := TheoryTransport.sentence (source_proofTheoryParameterizedBoundedMatrixIff test env w z row)

theorem native_proofTheoryParameterizedBoundedMatrixIff {m} (test : Source.Formula 1) (env : Fin 3 → Fin m) (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (proofTheoryParameterizedBoundedMatrixIffSentence test env w z row)) := ZFReplay.replay (proofTheoryParameterizedBoundedMatrixIff_kernel_certificate test env w z row)

def proofTheoryParameterizedWholeNodeIffSentence {m} (test : Source.Formula 1) (w z row : Fin m) : Source.Sentence := ((omega w).imp ((empty z).imp (((ProofTheoryNodeSyntax.node test w row).iff (ProofTheoryNodeSyntax.normalized test w z row))))).close

theorem source_proofTheoryParameterizedWholeNodeIff {m} (test : Source.Formula 1) (w z row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (proofTheoryParameterizedWholeNodeIffSentence test w z row) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (empty z) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (empty z) := .hyp (Or.inl rfl)
  exact ProofTheoryNode.normalized_node_iff test hZ w z row h0 h1

theorem proofTheoryParameterizedWholeNodeIff_kernel_certificate {m} (test : Source.Formula 1) (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (proofTheoryParameterizedWholeNodeIffSentence test w z row)) := TheoryTransport.sentence (source_proofTheoryParameterizedWholeNodeIff test w z row)

theorem native_proofTheoryParameterizedWholeNodeIff {m} (test : Source.Formula 1) (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (proofTheoryParameterizedWholeNodeIffSentence test w z row)) := ZFReplay.replay (proofTheoryParameterizedWholeNodeIff_kernel_certificate test w z row)

def proofSixRulesParameterizedActualShapeTableIffSentence {m} (test : Source.Formula 1) (w row : Fin m) : Source.Sentence := (((ProofAllNodeSyntax.table test w row).iff (ProofAllNodeSyntax.selected test w row))).close

theorem source_proofSixRulesParameterizedActualShapeTableIff {m} (test : Source.Formula 1) (w row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (proofSixRulesParameterizedActualShapeTableIffSentence test w row) := by
  apply close_derives
  let Δ : Context m := Source.SetLanguage.ZF.at m
  exact ProofAllNodes.raw_table_iff test w row

theorem proofSixRulesParameterizedActualShapeTableIff_kernel_certificate {m} (test : Source.Formula 1) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (proofSixRulesParameterizedActualShapeTableIffSentence test w row)) := TheoryTransport.sentence (source_proofSixRulesParameterizedActualShapeTableIff test w row)

theorem native_proofSixRulesParameterizedActualShapeTableIff {m} (test : Source.Formula 1) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (proofSixRulesParameterizedActualShapeTableIffSentence test w row)) := ZFReplay.replay (proofSixRulesParameterizedActualShapeTableIff_kernel_certificate test w row)

def proofSixRulesParameterizedSelectedNodesIffSentence {m} (test : Source.Formula 1) (w z row : Fin m) : Source.Sentence := ((omega w).imp ((empty z).imp (((ProofAllNodeSyntax.selected test w row).iff (ProofAllNodeSyntax.specification test w z row))))).close

theorem source_proofSixRulesParameterizedSelectedNodesIff {m} (test : Source.Formula 1) (w z row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (proofSixRulesParameterizedSelectedNodesIffSentence test w z row) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (empty z) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (empty z) := .hyp (Or.inl rfl)
  exact ProofAllNodes.selected_iff test hZ w z row h0 h1

theorem proofSixRulesParameterizedSelectedNodesIff_kernel_certificate {m} (test : Source.Formula 1) (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (proofSixRulesParameterizedSelectedNodesIffSentence test w z row)) := TheoryTransport.sentence (source_proofSixRulesParameterizedSelectedNodesIff test w z row)

theorem native_proofSixRulesParameterizedSelectedNodesIff {m} (test : Source.Formula 1) (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (proofSixRulesParameterizedSelectedNodesIffSentence test w z row)) := ZFReplay.replay (proofSixRulesParameterizedSelectedNodesIff_kernel_certificate test w z row)

def proofSixRulesParameterizedActualTableSpecificationIffSentence {m} (test : Source.Formula 1) (w z row : Fin m) : Source.Sentence := ((omega w).imp ((empty z).imp (((ProofAllNodeSyntax.table test w row).iff (ProofAllNodeSyntax.specification test w z row))))).close

theorem source_proofSixRulesParameterizedActualTableSpecificationIff {m} (test : Source.Formula 1) (w z row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (proofSixRulesParameterizedActualTableSpecificationIffSentence test w z row) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (empty z) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (empty z) := .hyp (Or.inl rfl)
  exact ProofAllNodes.table_iff test hZ w z row h0 h1

theorem proofSixRulesParameterizedActualTableSpecificationIff_kernel_certificate {m} (test : Source.Formula 1) (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (proofSixRulesParameterizedActualTableSpecificationIffSentence test w z row)) := TheoryTransport.sentence (source_proofSixRulesParameterizedActualTableSpecificationIff test w z row)

theorem native_proofSixRulesParameterizedActualTableSpecificationIff {m} (test : Source.Formula 1) (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (proofSixRulesParameterizedActualTableSpecificationIffSentence test w z row)) := ZFReplay.replay (proofSixRulesParameterizedActualTableSpecificationIff_kernel_certificate test w z row)

end PPAC.Migration.Internal.ObjectProofBaseNodes
