import PPAC.Migration.Internal.ProofTreeRootBackward

/-! 原12分支的根关闭性与精确结论字段对象原核闭句；可靠性归纳及最终Con尚未完成。 -/
namespace PPAC.Migration.Internal.ObjectProofTreeRoot
open Source SourceAlgebra SourceLogic OmegaSyntax

def proofRootOneNonemptySentence {m} (x : Fin m) : Source.Sentence := ((SyntaxNumeralSyntax.numeral 1 x).imp (((empty x).neg))).close

theorem source_proofRootOneNonempty {m} (x : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (proofRootOneNonemptySentence x) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNumeralSyntax.numeral 1 x) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (SyntaxNumeralSyntax.numeral 1 x) := .hyp (Or.inl rfl)
  exact ProofTreeZeroGuard.one_nonempty x h0

theorem proofRootOneNonempty_kernel_certificate {m} (x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (proofRootOneNonemptySentence x)) := TheoryTransport.sentence (source_proofRootOneNonempty x)

theorem native_proofRootOneNonempty {m} (x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (proofRootOneNonemptySentence x)) := ZFReplay.replay (proofRootOneNonempty_kernel_certificate x)

def proofRootOneMembershipSentence {m} (u x : Fin m) : Source.Sentence := ((SyntaxNumeralSyntax.numeral 1 x).imp (((Formula.mem u x).iff (empty u)))).close

theorem source_proofRootOneMembership {m} (u x : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (proofRootOneMembershipSentence u x) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNumeralSyntax.numeral 1 x) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (SyntaxNumeralSyntax.numeral 1 x) := .hyp (Or.inl rfl)
  exact ProofTreeZeroGuard.one_member_iff hZ u x h0

theorem proofRootOneMembership_kernel_certificate {m} (u x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (proofRootOneMembershipSentence u x)) := TheoryTransport.sentence (source_proofRootOneMembership u x)

theorem native_proofRootOneMembership {m} (u x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (proofRootOneMembershipSentence u x)) := ZFReplay.replay (proofRootOneMembership_kernel_certificate u x)

def proofRootZeroGuardIffSentence {m} {a} (i : Fin a) (env : Fin a → Fin m) (w : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat a w env).imp (((HornRuleSyntax.guard (.var i) (.literal 1) w env).iff (empty (env i)))))).close

theorem source_proofRootZeroGuardIff {m} {a} (i : Fin a) (env : Fin a → Fin m) (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (proofRootZeroGuardIffSentence i env w) := by
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
  exact ProofTreeZeroGuard.guard_iff hZ i w env h0 h1

theorem proofRootZeroGuardIff_kernel_certificate {m} {a} (i : Fin a) (env : Fin a → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (proofRootZeroGuardIffSentence i env w)) := TheoryTransport.sentence (source_proofRootZeroGuardIff i env w)

theorem native_proofRootZeroGuardIff {m} {a} (i : Fin a) (env : Fin a → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (proofRootZeroGuardIffSentence i env w)) := ZFReplay.replay (proofRootZeroGuardIff_kernel_certificate i env w)

def proofRootPayloadConstructorIffSentence {m} (s : YesMetaZFC.Automation.ObjectProofTree.Shape) (env : Fin (s.extra+2) → Fin m) (w code : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat (s.extra+2) w env).imp (((HornExprSyntax.graph (YesMetaZFC.Automation.ObjectProofTree.payload s) w env code).iff (SyntaxNodeSyntax.constructor (s.extra+2) s.tag w env code))))).close

theorem source_proofRootPayloadConstructorIff {m} (s : YesMetaZFC.Automation.ObjectProofTree.Shape) (env : Fin (s.extra+2) → Fin m) (w code : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (proofRootPayloadConstructorIffSentence s env w code) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.environmentNat (s.extra+2) w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (HornExprSyntax.environmentNat (s.extra+2) w env) := .hyp (Or.inl rfl)
  exact ProofTreeBranchHead.payload_iff hZ s w code env h0 h1

theorem proofRootPayloadConstructorIff_kernel_certificate {m} (s : YesMetaZFC.Automation.ObjectProofTree.Shape) (env : Fin (s.extra+2) → Fin m) (w code : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (proofRootPayloadConstructorIffSentence s env w code)) := TheoryTransport.sentence (source_proofRootPayloadConstructorIff s env w code)

theorem native_proofRootPayloadConstructorIff {m} (s : YesMetaZFC.Automation.ObjectProofTree.Shape) (env : Fin (s.extra+2) → Fin m) (w code : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (proofRootPayloadConstructorIffSentence s env w code)) := ZFReplay.replay (proofRootPayloadConstructorIff_kernel_certificate s env w code)

def proofRootActualLocalConditionSentence {m} (test : Source.Formula 1) (w code conclusion r : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNodeSyntax.constructor 2 1 w (SetLanguage.args2 code conclusion) r).imp ((ProofTreeRowLocalSyntax.localCondition test w r)))).close

theorem source_proofRootActualLocalCondition {m} (test : Source.Formula 1) (w code conclusion r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (proofRootActualLocalConditionSentence test w code conclusion r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNodeSyntax.constructor 2 1 w (SetLanguage.args2 code conclusion) r) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxNodeSyntax.constructor 2 1 w (SetLanguage.args2 code conclusion) r) := .hyp (Or.inl rfl)
  exact ProofTreeRootLocal.constructor_one test hZ 2 w r (SetLanguage.args2 code conclusion) h0 h1

theorem proofRootActualLocalCondition_kernel_certificate {m} (test : Source.Formula 1) (w code conclusion r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (proofRootActualLocalConditionSentence test w code conclusion r)) := TheoryTransport.sentence (source_proofRootActualLocalCondition test w code conclusion r)

theorem native_proofRootActualLocalCondition {m} (test : Source.Formula 1) (w code conclusion r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (proofRootActualLocalConditionSentence test w code conclusion r)) := ZFReplay.replay (proofRootActualLocalCondition_kernel_certificate test w code conclusion r)

def proofRootClosedFieldsForwardSentence {m} (test : Source.Formula 1) (w code conclusion : Fin m) : Source.Sentence := ((omega w).imp ((ProofTreeEntrySyntax.root test w code conclusion).imp ((ProofTreeRootSyntax.normalized test w code conclusion)))).close

theorem source_proofRootClosedFieldsForward {m} (test : Source.Formula 1) (w code conclusion : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (proofRootClosedFieldsForwardSentence test w code conclusion) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ProofTreeEntrySyntax.root test w code conclusion) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (ProofTreeEntrySyntax.root test w code conclusion) := .hyp (Or.inl rfl)
  exact ProofTreeRootForward.root_forward test hZ w code conclusion h0 h1

theorem proofRootClosedFieldsForward_kernel_certificate {m} (test : Source.Formula 1) (w code conclusion : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (proofRootClosedFieldsForwardSentence test w code conclusion)) := TheoryTransport.sentence (source_proofRootClosedFieldsForward test w code conclusion)

theorem native_proofRootClosedFieldsForward {m} (test : Source.Formula 1) (w code conclusion : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (proofRootClosedFieldsForwardSentence test w code conclusion)) := ZFReplay.replay (proofRootClosedFieldsForward_kernel_certificate test w code conclusion)

def proofRootClosedFieldsBackwardSentence {m} (test : Source.Formula 1) (w code conclusion : Fin m) : Source.Sentence := ((omega w).imp ((ProofTreeRootSyntax.normalized test w code conclusion).imp ((ProofTreeEntrySyntax.root test w code conclusion)))).close

theorem source_proofRootClosedFieldsBackward {m} (test : Source.Formula 1) (w code conclusion : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (proofRootClosedFieldsBackwardSentence test w code conclusion) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ProofTreeRootSyntax.normalized test w code conclusion) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (ProofTreeRootSyntax.normalized test w code conclusion) := .hyp (Or.inl rfl)
  exact ProofTreeRootBackward.root_backward test hZ w code conclusion h0 h1

theorem proofRootClosedFieldsBackward_kernel_certificate {m} (test : Source.Formula 1) (w code conclusion : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (proofRootClosedFieldsBackwardSentence test w code conclusion)) := TheoryTransport.sentence (source_proofRootClosedFieldsBackward test w code conclusion)

theorem native_proofRootClosedFieldsBackward {m} (test : Source.Formula 1) (w code conclusion : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (proofRootClosedFieldsBackwardSentence test w code conclusion)) := ZFReplay.replay (proofRootClosedFieldsBackward_kernel_certificate test w code conclusion)

def proofRootExactClosedFieldsIffSentence {m} (test : Source.Formula 1) (w code conclusion : Fin m) : Source.Sentence := ((omega w).imp (((ProofTreeEntrySyntax.root test w code conclusion).iff (ProofTreeRootSyntax.normalized test w code conclusion)))).close

theorem source_proofRootExactClosedFieldsIff {m} (test : Source.Formula 1) (w code conclusion : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (proofRootExactClosedFieldsIffSentence test w code conclusion) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact ProofTreeRootBackward.root_iff test hZ w code conclusion h0

theorem proofRootExactClosedFieldsIff_kernel_certificate {m} (test : Source.Formula 1) (w code conclusion : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (proofRootExactClosedFieldsIffSentence test w code conclusion)) := TheoryTransport.sentence (source_proofRootExactClosedFieldsIff test w code conclusion)

theorem native_proofRootExactClosedFieldsIff {m} (test : Source.Formula 1) (w code conclusion : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (proofRootExactClosedFieldsIffSentence test w code conclusion)) := ZFReplay.replay (proofRootExactClosedFieldsIff_kernel_certificate test w code conclusion)

end PPAC.Migration.Internal.ObjectProofTreeRoot
