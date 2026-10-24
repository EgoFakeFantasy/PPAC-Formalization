import PPAC.Migration.Internal.ProofTreeNodeBackward

/-! 原Node六分支的准确局部表与子Node方程；内部可靠性归纳及最终Con仍未完成。 -/
namespace PPAC.Migration.Internal.ObjectProofTreeNode
open Source SourceAlgebra SourceLogic OmegaSyntax

def proofNodeFieldLocalIffSentence {m} (test : Source.Formula 1) (w row code z : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNodeSyntax.constructor 1 0 w (fun _ => code) row).imp ((empty z).imp (((ProofTreeRowLocalSyntax.fieldCheck test w row z).iff (ProofAllNodeSyntax.table test w code)))))).close

theorem source_proofNodeFieldLocalIff {m} (test : Source.Formula 1) (w row code z : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (proofNodeFieldLocalIffSentence test w row code z) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (empty z) (Context.add (SyntaxNodeSyntax.constructor 1 0 w (fun _ => code) row) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxNodeSyntax.constructor 1 0 w (fun _ => code) row) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (empty z) := .hyp (Or.inl rfl)
  exact ProofTreeNodeFieldLocal.fieldCheck_iff test hZ w row code z h0 h1 h2

theorem proofNodeFieldLocalIff_kernel_certificate {m} (test : Source.Formula 1) (w row code z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (proofNodeFieldLocalIffSentence test w row code z)) := TheoryTransport.sentence (source_proofNodeFieldLocalIff test w row code z)

theorem native_proofNodeFieldLocalIff {m} (test : Source.Formula 1) (w row code z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (proofNodeFieldLocalIffSentence test w row code z)) := ZFReplay.replay (proofNodeFieldLocalIff_kernel_certificate test w row code z)

def proofNodeActualTagLocalIffSentence {m} (test : Source.Formula 1) (w row code : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNodeSyntax.constructor 1 0 w (fun _ => code) row).imp (((ProofTreeRowLocalSyntax.localCondition test w row).iff (ProofAllNodeSyntax.table test w code))))).close

theorem source_proofNodeActualTagLocalIff {m} (test : Source.Formula 1) (w row code : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (proofNodeActualTagLocalIffSentence test w row code) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNodeSyntax.constructor 1 0 w (fun _ => code) row) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxNodeSyntax.constructor 1 0 w (fun _ => code) row) := .hyp (Or.inl rfl)
  exact ProofTreeNodeTag.local_iff test hZ w row code h0 h1

theorem proofNodeActualTagLocalIff_kernel_certificate {m} (test : Source.Formula 1) (w row code : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (proofNodeActualTagLocalIffSentence test w row code)) := TheoryTransport.sentence (source_proofNodeActualTagLocalIff test w row code)

theorem native_proofNodeActualTagLocalIff {m} (test : Source.Formula 1) (w row code : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (proofNodeActualTagLocalIffSentence test w row code)) := ZFReplay.replay (proofNodeActualTagLocalIff_kernel_certificate test w row code)

def proofNodeVariableChildIffSentence {m} (test : Source.Formula 1) {a} (i : Fin a) (env : Fin a → Fin m) (w : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat a w env).imp (((ProofTreeTracedStep.premise test (.node (.literal 0) [.var i]) w env).iff (ProofTreeEntrySyntax.node test w (env i)))))).close

theorem source_proofNodeVariableChildIff {m} (test : Source.Formula 1) {a} (i : Fin a) (env : Fin a → Fin m) (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (proofNodeVariableChildIffSentence test i env w) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.environmentNat a w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (HornExprSyntax.environmentNat a w env) := .hyp (Or.inl rfl)
  exact ProofTreeChildren.variable_premise_iff test hZ i w env h0 h1

theorem proofNodeVariableChildIff_kernel_certificate {m} (test : Source.Formula 1) {a} (i : Fin a) (env : Fin a → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (proofNodeVariableChildIffSentence test i env w)) := TheoryTransport.sentence (source_proofNodeVariableChildIff test i env w)

theorem native_proofNodeVariableChildIff {m} (test : Source.Formula 1) {a} (i : Fin a) (env : Fin a → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (proofNodeVariableChildIffSentence test i env w)) := ZFReplay.replay (proofNodeVariableChildIff_kernel_certificate test i env w)

def proofNodeAllChildrenIffSentence {m} (test : Source.Formula 1) {a} (is : List (Fin a)) (env : Fin a → Fin m) (w : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat a w env).imp (((ProofTreeTracedStep.premises test (is.map (fun i => .node (.literal 0) [.var i])) w env).iff (ProofTreeChildren.children test is w env))))).close

theorem source_proofNodeAllChildrenIff {m} (test : Source.Formula 1) {a} (is : List (Fin a)) (env : Fin a → Fin m) (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (proofNodeAllChildrenIffSentence test is env w) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.environmentNat a w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (HornExprSyntax.environmentNat a w env) := .hyp (Or.inl rfl)
  exact ProofTreeChildren.children_iff test hZ is w env h0 h1

theorem proofNodeAllChildrenIff_kernel_certificate {m} (test : Source.Formula 1) {a} (is : List (Fin a)) (env : Fin a → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (proofNodeAllChildrenIffSentence test is env w)) := TheoryTransport.sentence (source_proofNodeAllChildrenIff test is env w)

theorem native_proofNodeAllChildrenIff {m} (test : Source.Formula 1) {a} (is : List (Fin a)) (env : Fin a → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (proofNodeAllChildrenIffSentence test is env w)) := ZFReplay.replay (proofNodeAllChildrenIff_kernel_certificate test is env w)

def proofNodePayloadFieldBelowSentence {m} (kind : Fin 6) (env : Fin ((ProofTreeBranchConstruction.shape kind).extra+2) → Fin m) (i : Fin ((ProofTreeBranchConstruction.shape kind).extra+2)) (w code : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNodeSyntax.constructor ((ProofTreeBranchConstruction.shape kind).extra+2) (ProofTreeBranchConstruction.shape kind).tag w env code).imp ((Formula.mem (env i) code)))).close

theorem source_proofNodePayloadFieldBelow {m} (kind : Fin 6) (env : Fin ((ProofTreeBranchConstruction.shape kind).extra+2) → Fin m) (i : Fin ((ProofTreeBranchConstruction.shape kind).extra+2)) (w code : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (proofNodePayloadFieldBelowSentence kind env i w code) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNodeSyntax.constructor ((ProofTreeBranchConstruction.shape kind).extra+2) (ProofTreeBranchConstruction.shape kind).tag w env code) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxNodeSyntax.constructor ((ProofTreeBranchConstruction.shape kind).extra+2) (ProofTreeBranchConstruction.shape kind).tag w env code) := .hyp (Or.inl rfl)
  exact ProofTreeNodeSyntax.payload_field_below hZ kind w code env i h0 h1

theorem proofNodePayloadFieldBelow_kernel_certificate {m} (kind : Fin 6) (env : Fin ((ProofTreeBranchConstruction.shape kind).extra+2) → Fin m) (i : Fin ((ProofTreeBranchConstruction.shape kind).extra+2)) (w code : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (proofNodePayloadFieldBelowSentence kind env i w code)) := TheoryTransport.sentence (source_proofNodePayloadFieldBelow kind env i w code)

theorem native_proofNodePayloadFieldBelow {m} (kind : Fin 6) (env : Fin ((ProofTreeBranchConstruction.shape kind).extra+2) → Fin m) (i : Fin ((ProofTreeBranchConstruction.shape kind).extra+2)) (w code : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (proofNodePayloadFieldBelowSentence kind env i w code)) := ZFReplay.replay (proofNodePayloadFieldBelow_kernel_certificate kind env i w code)

def proofNodeSixCasesForwardSentence {m} (test : Source.Formula 1) (w code : Fin m) : Source.Sentence := ((omega w).imp ((ProofTreeEntrySyntax.node test w code).imp ((ProofTreeNodeSyntax.normalized test w code)))).close

theorem source_proofNodeSixCasesForward {m} (test : Source.Formula 1) (w code : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (proofNodeSixCasesForwardSentence test w code) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ProofTreeEntrySyntax.node test w code) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (ProofTreeEntrySyntax.node test w code) := .hyp (Or.inl rfl)
  exact ProofTreeNodeForward.node_forward test hZ w code h0 h1

theorem proofNodeSixCasesForward_kernel_certificate {m} (test : Source.Formula 1) (w code : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (proofNodeSixCasesForwardSentence test w code)) := TheoryTransport.sentence (source_proofNodeSixCasesForward test w code)

theorem native_proofNodeSixCasesForward {m} (test : Source.Formula 1) (w code : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (proofNodeSixCasesForwardSentence test w code)) := ZFReplay.replay (proofNodeSixCasesForward_kernel_certificate test w code)

def proofNodeSixCasesBackwardSentence {m} (test : Source.Formula 1) (w code : Fin m) : Source.Sentence := ((omega w).imp ((ProofTreeNodeSyntax.normalized test w code).imp ((ProofTreeEntrySyntax.node test w code)))).close

theorem source_proofNodeSixCasesBackward {m} (test : Source.Formula 1) (w code : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (proofNodeSixCasesBackwardSentence test w code) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ProofTreeNodeSyntax.normalized test w code) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (ProofTreeNodeSyntax.normalized test w code) := .hyp (Or.inl rfl)
  exact ProofTreeNodeBackward.node_backward test hZ w code h0 h1

theorem proofNodeSixCasesBackward_kernel_certificate {m} (test : Source.Formula 1) (w code : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (proofNodeSixCasesBackwardSentence test w code)) := TheoryTransport.sentence (source_proofNodeSixCasesBackward test w code)

theorem native_proofNodeSixCasesBackward {m} (test : Source.Formula 1) (w code : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (proofNodeSixCasesBackwardSentence test w code)) := ZFReplay.replay (proofNodeSixCasesBackward_kernel_certificate test w code)

def proofNodeExactSixCasesIffSentence {m} (test : Source.Formula 1) (w code : Fin m) : Source.Sentence := ((omega w).imp (((ProofTreeEntrySyntax.node test w code).iff (ProofTreeNodeSyntax.normalized test w code)))).close

theorem source_proofNodeExactSixCasesIff {m} (test : Source.Formula 1) (w code : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (proofNodeExactSixCasesIffSentence test w code) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact ProofTreeNodeBackward.node_iff test hZ w code h0

theorem proofNodeExactSixCasesIff_kernel_certificate {m} (test : Source.Formula 1) (w code : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (proofNodeExactSixCasesIffSentence test w code)) := TheoryTransport.sentence (source_proofNodeExactSixCasesIff test w code)

theorem native_proofNodeExactSixCasesIff {m} (test : Source.Formula 1) (w code : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (proofNodeExactSixCasesIffSentence test w code)) := ZFReplay.replay (proofNodeExactSixCasesIff_kernel_certificate test w code)

def proofRootExactNodeSixCasesIffSentence {m} (test : Source.Formula 1) (w code conclusion : Fin m) : Source.Sentence := ((omega w).imp (((ProofTreeEntrySyntax.root test w code conclusion).iff ((ProofTreeNodeSyntax.normalized test w code).conj (ProofTreeRootSyntax.closedPayload w code conclusion))))).close

theorem source_proofRootExactNodeSixCasesIff {m} (test : Source.Formula 1) (w code conclusion : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (proofRootExactNodeSixCasesIffSentence test w code conclusion) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact ProofTreeNodeBackward.root_iff test hZ w code conclusion h0

theorem proofRootExactNodeSixCasesIff_kernel_certificate {m} (test : Source.Formula 1) (w code conclusion : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (proofRootExactNodeSixCasesIffSentence test w code conclusion)) := TheoryTransport.sentence (source_proofRootExactNodeSixCasesIff test w code conclusion)

theorem native_proofRootExactNodeSixCasesIff {m} (test : Source.Formula 1) (w code conclusion : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (proofRootExactNodeSixCasesIffSentence test w code conclusion)) := ZFReplay.replay (proofRootExactNodeSixCasesIff_kernel_certificate test w code conclusion)

end PPAC.Migration.Internal.ObjectProofTreeNode
