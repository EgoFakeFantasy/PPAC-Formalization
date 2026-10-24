import PPAC.Migration.Internal.ProofTreeEntrySyntax

/-! 原12分支带局部测试轨迹的分离集合、递归方程及根／节点入口的原核闭句；专用ZF/U与可靠性未完成。 -/
namespace PPAC.Migration.Internal.ObjectProofTreeTrace
open Source SourceAlgebra SourceLogic OmegaSyntax

def proofTreeAllTraceRootsExistSentence {m} (test : Source.Formula 1) (w : Fin m) : Source.Sentence := ((ProofTreeUniversalSyntax.existsValue test w)).close

theorem source_proofTreeAllTraceRootsExist {m} (test : Source.Formula 1) (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (proofTreeAllTraceRootsExistSentence test w) := by
  apply close_derives
  let Δ : Context m := Source.SetLanguage.ZF.at m
  have hZ : ZFContext.Evidence Δ := by
    exact ZFContext.source_ZF m
  exact ProofTreeUniversalValue.exists_value test hZ w

theorem proofTreeAllTraceRootsExist_kernel_certificate {m} (test : Source.Formula 1) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (proofTreeAllTraceRootsExistSentence test w)) := TheoryTransport.sentence (source_proofTreeAllTraceRootsExist test w)

theorem native_proofTreeAllTraceRootsExist {m} (test : Source.Formula 1) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (proofTreeAllTraceRootsExistSentence test w)) := ZFReplay.replay (proofTreeAllTraceRootsExist_kernel_certificate test w)

def proofTreeTraceRangeSentence {m} (test : Source.Formula 1) (w r : Fin m) : Source.Sentence := ((ProofTreeTraceSyntax.condition test w r).imp ((Formula.mem r w))).close

theorem source_proofTreeTraceRange {m} (test : Source.Formula 1) (w r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (proofTreeTraceRangeSentence test w r) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (ProofTreeTraceSyntax.condition test w r) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (ProofTreeTraceSyntax.condition test w r) := .hyp (Or.inl rfl)
  exact ProofTreeUniversalValue.condition_natural test w r h0

theorem proofTreeTraceRange_kernel_certificate {m} (test : Source.Formula 1) (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (proofTreeTraceRangeSentence test w r)) := TheoryTransport.sentence (source_proofTreeTraceRange test w r)

theorem native_proofTreeTraceRange {m} (test : Source.Formula 1) (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (proofTreeTraceRangeSentence test w r)) := ZFReplay.replay (proofTreeTraceRange_kernel_certificate test w r)

def proofTreeAllRootsMembershipIffSentence {m} (test : Source.Formula 1) (w V r : Fin m) : Source.Sentence := ((ProofTreeUniversalSyntax.value test w V).imp (((Formula.mem r V).iff (ProofTreeTraceSyntax.condition test w r)))).close

theorem source_proofTreeAllRootsMembershipIff {m} (test : Source.Formula 1) (w V r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (proofTreeAllRootsMembershipIffSentence test w V r) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (ProofTreeUniversalSyntax.value test w V) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (ProofTreeUniversalSyntax.value test w V) := .hyp (Or.inl rfl)
  exact ProofTreeUniversalValue.member_iff test w V r h0

theorem proofTreeAllRootsMembershipIff_kernel_certificate {m} (test : Source.Formula 1) (w V r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (proofTreeAllRootsMembershipIffSentence test w V r)) := TheoryTransport.sentence (source_proofTreeAllRootsMembershipIff test w V r)

theorem native_proofTreeAllRootsMembershipIff {m} (test : Source.Formula 1) (w V r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (proofTreeAllRootsMembershipIffSentence test w V r)) := ZFReplay.replay (proofTreeAllRootsMembershipIff_kernel_certificate test w V r)

def proofTreeAllRootsClosedSentence {m} (test : Source.Formula 1) (w V : Fin m) : Source.Sentence := ((ProofTreeUniversalSyntax.value test w V).imp ((ProofTreeTraceSyntax.closed test w V))).close

theorem source_proofTreeAllRootsClosed {m} (test : Source.Formula 1) (w V : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (proofTreeAllRootsClosedSentence test w V) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (ProofTreeUniversalSyntax.value test w V) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (ProofTreeUniversalSyntax.value test w V) := .hyp (Or.inl rfl)
  exact ProofTreeUniversalClosed.closed test w V h0

theorem proofTreeAllRootsClosed_kernel_certificate {m} (test : Source.Formula 1) (w V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (proofTreeAllRootsClosedSentence test w V)) := TheoryTransport.sentence (source_proofTreeAllRootsClosed test w V)

theorem native_proofTreeAllRootsClosed {m} (test : Source.Formula 1) (w V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (proofTreeAllRootsClosedSentence test w V)) := ZFReplay.replay (proofTreeAllRootsClosed_kernel_certificate test w V)

def proofTreeTwelveRuleTracedStepIffSentence {m} (test : Source.Formula 1) (w V r : Fin m) : Source.Sentence := ((ProofTreeUniversalSyntax.value test w V).imp (((HornStepSyntax.step YesMetaZFC.Automation.ObjectProofTree.rules w r V).iff (ProofTreeTracedStep.step test YesMetaZFC.Automation.ObjectProofTree.rules w r)))).close

theorem source_proofTreeTwelveRuleTracedStepIff {m} (test : Source.Formula 1) (w V r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (proofTreeTwelveRuleTracedStepIffSentence test w V r) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (ProofTreeUniversalSyntax.value test w V) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (ProofTreeUniversalSyntax.value test w V) := .hyp (Or.inl rfl)
  exact ProofTreeTracedStep.step_iff test YesMetaZFC.Automation.ObjectProofTree.rules w V r h0

theorem proofTreeTwelveRuleTracedStepIff_kernel_certificate {m} (test : Source.Formula 1) (w V r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (proofTreeTwelveRuleTracedStepIffSentence test w V r)) := TheoryTransport.sentence (source_proofTreeTwelveRuleTracedStepIff test w V r)

theorem native_proofTreeTwelveRuleTracedStepIff {m} (test : Source.Formula 1) (w V r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (proofTreeTwelveRuleTracedStepIffSentence test w V r)) := ZFReplay.replay (proofTreeTwelveRuleTracedStepIff_kernel_certificate test w V r)

def proofTreeFullRecursiveTraceIffSentence {m} (test : Source.Formula 1) (w r : Fin m) : Source.Sentence := (((ProofTreeTraceSyntax.condition test w r).iff (ProofTreeTraceEquation.equation test w r))).close

theorem source_proofTreeFullRecursiveTraceIff {m} (test : Source.Formula 1) (w r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (proofTreeFullRecursiveTraceIffSentence test w r) := by
  apply close_derives
  let Δ : Context m := Source.SetLanguage.ZF.at m
  have hZ : ZFContext.Evidence Δ := by
    exact ZFContext.source_ZF m
  exact ProofTreeTraceEquation.recursive_iff test hZ w r

theorem proofTreeFullRecursiveTraceIff_kernel_certificate {m} (test : Source.Formula 1) (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (proofTreeFullRecursiveTraceIffSentence test w r)) := TheoryTransport.sentence (source_proofTreeFullRecursiveTraceIff test w r)

theorem native_proofTreeFullRecursiveTraceIff {m} (test : Source.Formula 1) (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (proofTreeFullRecursiveTraceIffSentence test w r)) := ZFReplay.replay (proofTreeFullRecursiveTraceIff_kernel_certificate test w r)

def proofTreeNodeEntryRecursiveIffSentence {m} (test : Source.Formula 1) (w code : Fin m) : Source.Sentence := (((ProofTreeEntrySyntax.node test w code).iff (ProofTreeEntrySyntax.nodeEquation test w code))).close

theorem source_proofTreeNodeEntryRecursiveIff {m} (test : Source.Formula 1) (w code : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (proofTreeNodeEntryRecursiveIffSentence test w code) := by
  apply close_derives
  let Δ : Context m := Source.SetLanguage.ZF.at m
  have hZ : ZFContext.Evidence Δ := by
    exact ZFContext.source_ZF m
  exact ProofTreeEntrySyntax.node_recursive_iff test hZ w code

theorem proofTreeNodeEntryRecursiveIff_kernel_certificate {m} (test : Source.Formula 1) (w code : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (proofTreeNodeEntryRecursiveIffSentence test w code)) := TheoryTransport.sentence (source_proofTreeNodeEntryRecursiveIff test w code)

theorem native_proofTreeNodeEntryRecursiveIff {m} (test : Source.Formula 1) (w code : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (proofTreeNodeEntryRecursiveIffSentence test w code)) := ZFReplay.replay (proofTreeNodeEntryRecursiveIff_kernel_certificate test w code)

def proofTreeRootEntryRecursiveIffSentence {m} (test : Source.Formula 1) (w code conclusion : Fin m) : Source.Sentence := (((ProofTreeEntrySyntax.root test w code conclusion).iff (ProofTreeEntrySyntax.rootEquation test w code conclusion))).close

theorem source_proofTreeRootEntryRecursiveIff {m} (test : Source.Formula 1) (w code conclusion : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (proofTreeRootEntryRecursiveIffSentence test w code conclusion) := by
  apply close_derives
  let Δ : Context m := Source.SetLanguage.ZF.at m
  have hZ : ZFContext.Evidence Δ := by
    exact ZFContext.source_ZF m
  exact ProofTreeEntrySyntax.root_recursive_iff test hZ w code conclusion

theorem proofTreeRootEntryRecursiveIff_kernel_certificate {m} (test : Source.Formula 1) (w code conclusion : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (proofTreeRootEntryRecursiveIffSentence test w code conclusion)) := TheoryTransport.sentence (source_proofTreeRootEntryRecursiveIff test w code conclusion)

theorem native_proofTreeRootEntryRecursiveIff {m} (test : Source.Formula 1) (w code conclusion : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (proofTreeRootEntryRecursiveIffSentence test w code conclusion)) := ZFReplay.replay (proofTreeRootEntryRecursiveIff_kernel_certificate test w code conclusion)

def proofTreeTwelveBranchAllAssignmentBoundsSentence {m} (kind : Fin 6) (isRoot : Bool) (env : Fin ((ProofTreeBranchConstruction.shape kind).extra+2) → Fin m) (w r : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat ((ProofTreeBranchConstruction.shape kind).extra+2) w env).imp ((HornExprSyntax.graph (YesMetaZFC.Automation.ObjectProofTree.branch (ProofTreeBranchConstruction.shape kind) isRoot).head w env r).imp ((HornExprBounds.environmentBound ((ProofTreeBranchConstruction.shape kind).extra+2) r env))))).close

theorem source_proofTreeTwelveBranchAllAssignmentBounds {m} (kind : Fin 6) (isRoot : Bool) (env : Fin ((ProofTreeBranchConstruction.shape kind).extra+2) → Fin m) (w r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (proofTreeTwelveBranchAllAssignmentBoundsSentence kind isRoot env w r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.graph (YesMetaZFC.Automation.ObjectProofTree.branch (ProofTreeBranchConstruction.shape kind) isRoot).head w env r) (Context.add (HornExprSyntax.environmentNat ((ProofTreeBranchConstruction.shape kind).extra+2) w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat ((ProofTreeBranchConstruction.shape kind).extra+2) w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (HornExprSyntax.graph (YesMetaZFC.Automation.ObjectProofTree.branch (ProofTreeBranchConstruction.shape kind) isRoot).head w env r) := .hyp (Or.inl rfl)
  exact ProofTreeBranchConstruction.all_bounds hZ kind isRoot w r env h0 h1 h2

theorem proofTreeTwelveBranchAllAssignmentBounds_kernel_certificate {m} (kind : Fin 6) (isRoot : Bool) (env : Fin ((ProofTreeBranchConstruction.shape kind).extra+2) → Fin m) (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (proofTreeTwelveBranchAllAssignmentBoundsSentence kind isRoot env w r)) := TheoryTransport.sentence (source_proofTreeTwelveBranchAllAssignmentBounds kind isRoot env w r)

theorem native_proofTreeTwelveBranchAllAssignmentBounds {m} (kind : Fin 6) (isRoot : Bool) (env : Fin ((ProofTreeBranchConstruction.shape kind).extra+2) → Fin m) (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (proofTreeTwelveBranchAllAssignmentBoundsSentence kind isRoot env w r)) := ZFReplay.replay (proofTreeTwelveBranchAllAssignmentBounds_kernel_certificate kind isRoot env w r)

def proofTreeTwelveBranchTraceCompositionSentence {m} (test : Source.Formula 1) (kind : Fin 6) (isRoot : Bool) (env : Fin ((ProofTreeBranchConstruction.shape kind).extra+2) → Fin m) (w r : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat ((ProofTreeBranchConstruction.shape kind).extra+2) w env).imp ((ProofTreeTracedStep.matrix test (YesMetaZFC.Automation.ObjectProofTree.branch (ProofTreeBranchConstruction.shape kind) isRoot) w r env).imp ((ProofTreeRowLocalSyntax.localCondition test w r).imp ((ProofTreeTraceSyntax.condition test w r)))))).close

theorem source_proofTreeTwelveBranchTraceComposition {m} (test : Source.Formula 1) (kind : Fin 6) (isRoot : Bool) (env : Fin ((ProofTreeBranchConstruction.shape kind).extra+2) → Fin m) (w r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (proofTreeTwelveBranchTraceCompositionSentence test kind isRoot env w r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ProofTreeRowLocalSyntax.localCondition test w r) (Context.add (ProofTreeTracedStep.matrix test (YesMetaZFC.Automation.ObjectProofTree.branch (ProofTreeBranchConstruction.shape kind) isRoot) w r env) (Context.add (HornExprSyntax.environmentNat ((ProofTreeBranchConstruction.shape kind).extra+2) w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (HornExprSyntax.environmentNat ((ProofTreeBranchConstruction.shape kind).extra+2) w env) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (ProofTreeTracedStep.matrix test (YesMetaZFC.Automation.ObjectProofTree.branch (ProofTreeBranchConstruction.shape kind) isRoot) w r env) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (ProofTreeRowLocalSyntax.localCondition test w r) := .hyp (Or.inl rfl)
  exact ProofTreeBranchConstruction.intro_branch test hZ kind isRoot w r env h0 h1 h2 h3

theorem proofTreeTwelveBranchTraceComposition_kernel_certificate {m} (test : Source.Formula 1) (kind : Fin 6) (isRoot : Bool) (env : Fin ((ProofTreeBranchConstruction.shape kind).extra+2) → Fin m) (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (proofTreeTwelveBranchTraceCompositionSentence test kind isRoot env w r)) := TheoryTransport.sentence (source_proofTreeTwelveBranchTraceComposition test kind isRoot env w r)

theorem native_proofTreeTwelveBranchTraceComposition {m} (test : Source.Formula 1) (kind : Fin 6) (isRoot : Bool) (env : Fin ((ProofTreeBranchConstruction.shape kind).extra+2) → Fin m) (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (proofTreeTwelveBranchTraceCompositionSentence test kind isRoot env w r)) := ZFReplay.replay (proofTreeTwelveBranchTraceComposition_kernel_certificate test kind isRoot env w r)

end PPAC.Migration.Internal.ObjectProofTreeTrace
