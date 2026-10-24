import PPAC.Migration.Internal.InstantiateFrameTerm

/-! 原mode2完整变量数值对应、真实原规则分派及条件frame项程序的原核闭句。 -/
namespace PPAC.Migration.Internal.ObjectInstantiateVariable
open Source SourceAlgebra SourceLogic OmegaSyntax

def modeTwoWholeVariableValueIffSentence {m} (bound : Bool) (w mode depth P x idx y : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 2 mode).imp ((OriginalTermTraceSyntax.metadata w depth P).imp ((SyntaxVariableSyntax.code bound w idx x).imp (((OriginalTransformRowSyntax.run 1 w mode depth P x y).iff (InstantiateVariableValueSyntax.valueSpec bound w depth P idx x y))))))).close

theorem source_modeTwoWholeVariableValueIff {m} (bound : Bool) (w mode depth P x idx y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeTwoWholeVariableValueIffSentence bound w mode depth P x idx y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxVariableSyntax.code bound w idx x) (Context.add (OriginalTermTraceSyntax.metadata w depth P) (Context.add (SyntaxNumeralSyntax.numeral 2 mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 2 mode) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (OriginalTermTraceSyntax.metadata w depth P) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxVariableSyntax.code bound w idx x) := .hyp (Or.inl rfl)
  exact InstantiateVariableRun.run_iff hZ bound w mode depth P x idx y h0 h1 h2 h3

theorem modeTwoWholeVariableValueIff_kernel_certificate {m} (bound : Bool) (w mode depth P x idx y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeTwoWholeVariableValueIffSentence bound w mode depth P x idx y)) := TheoryTransport.sentence (source_modeTwoWholeVariableValueIff bound w mode depth P x idx y)

theorem native_modeTwoWholeVariableValueIff {m} (bound : Bool) (w mode depth P x idx y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeTwoWholeVariableValueIffSentence bound w mode depth P x idx y)) := ZFReplay.replay (modeTwoWholeVariableValueIff_kernel_certificate bound w mode depth P x idx y)

def modeTwoVariableTraceValueIffSentence {m} (bound : Bool) (xs : Fin 5 → Fin m) (w r idx : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNodeSyntax.constructor 5 1 w xs r).imp ((SyntaxNumeralSyntax.numeral 2 (xs 0)).imp ((SyntaxVariableSyntax.code bound w idx (xs 3)).imp (((HornLookupConditionSyntax.condition w r).iff (InstantiateVariableValueSyntax.valueSpec bound w (xs 1) (xs 2) idx (xs 3) (xs 4)))))))).close

theorem source_modeTwoVariableTraceValueIff {m} (bound : Bool) (xs : Fin 5 → Fin m) (w r idx : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeTwoVariableTraceValueIffSentence bound xs w r idx) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxVariableSyntax.code bound w idx (xs 3)) (Context.add (SyntaxNumeralSyntax.numeral 2 (xs 0)) (Context.add (SyntaxNodeSyntax.constructor 5 1 w xs r) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNodeSyntax.constructor 5 1 w xs r) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral 2 (xs 0)) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxVariableSyntax.code bound w idx (xs 3)) := .hyp (Or.inl rfl)
  exact InstantiateVariableRun.trace_iff_value hZ bound w r idx xs h0 h1 h2 h3

theorem modeTwoVariableTraceValueIff_kernel_certificate {m} (bound : Bool) (xs : Fin 5 → Fin m) (w r idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeTwoVariableTraceValueIffSentence bound xs w r idx)) := TheoryTransport.sentence (source_modeTwoVariableTraceValueIff bound xs w r idx)

theorem native_modeTwoVariableTraceValueIff {m} (bound : Bool) (xs : Fin 5 → Fin m) (w r idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeTwoVariableTraceValueIffSentence bound xs w r idx)) := ZFReplay.replay (modeTwoVariableTraceValueIff_kernel_certificate bound xs w r idx)

def modeTwoBoundCandidateIffSentence {m} (xs : Fin 5 → Fin m) (w r idx : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNodeSyntax.constructor 5 1 w xs r).imp ((SyntaxNumeralSyntax.numeral 2 (xs 0)).imp ((SyntaxVariableSyntax.code true w idx (xs 3)).imp (((HornLookupConditionSyntax.condition w r).iff (InstantiateVariableValueSyntax.boundValue w (xs 1) (xs 2) idx (xs 3) (xs 4)))))))).close

theorem source_modeTwoBoundCandidateIff {m} (xs : Fin 5 → Fin m) (w r idx : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeTwoBoundCandidateIffSentence xs w r idx) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxVariableSyntax.code true w idx (xs 3)) (Context.add (SyntaxNumeralSyntax.numeral 2 (xs 0)) (Context.add (SyntaxNodeSyntax.constructor 5 1 w xs r) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNodeSyntax.constructor 5 1 w xs r) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral 2 (xs 0)) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxVariableSyntax.code true w idx (xs 3)) := .hyp (Or.inl rfl)
  exact InstantiateVariableNumeric.bound_iff hZ w r idx xs h0 h1 h2 h3

theorem modeTwoBoundCandidateIff_kernel_certificate {m} (xs : Fin 5 → Fin m) (w r idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeTwoBoundCandidateIffSentence xs w r idx)) := TheoryTransport.sentence (source_modeTwoBoundCandidateIff xs w r idx)

theorem native_modeTwoBoundCandidateIff {m} (xs : Fin 5 → Fin m) (w r idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeTwoBoundCandidateIffSentence xs w r idx)) := ZFReplay.replay (modeTwoBoundCandidateIff_kernel_certificate xs w r idx)

def modeTwoFreeCandidateIffSentence {m} (xs : Fin 5 → Fin m) (w r idx : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNodeSyntax.constructor 5 1 w xs r).imp ((SyntaxNumeralSyntax.numeral 2 (xs 0)).imp ((SyntaxVariableSyntax.code false w idx (xs 3)).imp (((HornLookupConditionSyntax.condition w r).iff (Formula.equal (xs 4) (xs 3)))))))).close

theorem source_modeTwoFreeCandidateIff {m} (xs : Fin 5 → Fin m) (w r idx : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeTwoFreeCandidateIffSentence xs w r idx) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxVariableSyntax.code false w idx (xs 3)) (Context.add (SyntaxNumeralSyntax.numeral 2 (xs 0)) (Context.add (SyntaxNodeSyntax.constructor 5 1 w xs r) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNodeSyntax.constructor 5 1 w xs r) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral 2 (xs 0)) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxVariableSyntax.code false w idx (xs 3)) := .hyp (Or.inl rfl)
  exact InstantiateVariableNumeric.free_iff hZ w r idx xs h0 h1 h2 h3

theorem modeTwoFreeCandidateIff_kernel_certificate {m} (xs : Fin 5 → Fin m) (w r idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeTwoFreeCandidateIffSentence xs w r idx)) := TheoryTransport.sentence (source_modeTwoFreeCandidateIff xs w r idx)

theorem native_modeTwoFreeCandidateIff {m} (xs : Fin 5 → Fin m) (w r idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeTwoFreeCandidateIffSentence xs w r idx)) := ZFReplay.replay (modeTwoFreeCandidateIff_kernel_certificate xs w r idx)

def modeTwoOriginalVariableTraceStepIffSentence {m} (bound : Bool) (xs : Fin 5 → Fin m) (w r idx : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNodeSyntax.constructor 5 1 w xs r).imp ((SyntaxNumeralSyntax.numeral 2 (xs 0)).imp ((SyntaxVariableSyntax.code bound w idx (xs 3)).imp (((HornLookupConditionSyntax.condition w r).iff (OriginalInstantiateTrace.variableStep bound w r))))))).close

theorem source_modeTwoOriginalVariableTraceStepIff {m} (bound : Bool) (xs : Fin 5 → Fin m) (w r idx : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeTwoOriginalVariableTraceStepIffSentence bound xs w r idx) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxVariableSyntax.code bound w idx (xs 3)) (Context.add (SyntaxNumeralSyntax.numeral 2 (xs 0)) (Context.add (SyntaxNodeSyntax.constructor 5 1 w xs r) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNodeSyntax.constructor 5 1 w xs r) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral 2 (xs 0)) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxVariableSyntax.code bound w idx (xs 3)) := .hyp (Or.inl rfl)
  exact OriginalInstantiateTrace.variable_condition_iff hZ bound w r idx xs h0 h1 h2 h3

theorem modeTwoOriginalVariableTraceStepIff_kernel_certificate {m} (bound : Bool) (xs : Fin 5 → Fin m) (w r idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeTwoOriginalVariableTraceStepIffSentence bound xs w r idx)) := TheoryTransport.sentence (source_modeTwoOriginalVariableTraceStepIff bound xs w r idx)

theorem native_modeTwoOriginalVariableTraceStepIff {m} (bound : Bool) (xs : Fin 5 → Fin m) (w r idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeTwoOriginalVariableTraceStepIffSentence bound xs w r idx)) := ZFReplay.replay (modeTwoOriginalVariableTraceStepIff_kernel_certificate bound xs w r idx)

def modeTwoFiveRuleTermDispatchIffSentence {m} (xs : Fin 5 → Fin m) (w r T : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNodeSyntax.constructor 5 1 w xs r).imp ((SyntaxNumeralSyntax.numeral 2 (xs 0)).imp (((HornStepSyntax.originalStep w r T).iff (HornStepSyntax.step OriginalInstantiateClasses.selected w r T)))))).close

theorem source_modeTwoFiveRuleTermDispatchIff {m} (xs : Fin 5 → Fin m) (w r T : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeTwoFiveRuleTermDispatchIffSentence xs w r T) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNumeralSyntax.numeral 2 (xs 0)) (Context.add (SyntaxNodeSyntax.constructor 5 1 w xs r) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxNodeSyntax.constructor 5 1 w xs r) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral 2 (xs 0)) := .hyp (Or.inl rfl)
  exact OriginalInstantiateDispatch.dispatch_iff hZ w r T xs h0 h1 h2

theorem modeTwoFiveRuleTermDispatchIff_kernel_certificate {m} (xs : Fin 5 → Fin m) (w r T : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeTwoFiveRuleTermDispatchIffSentence xs w r T)) := TheoryTransport.sentence (source_modeTwoFiveRuleTermDispatchIff xs w r T)

theorem native_modeTwoFiveRuleTermDispatchIff {m} (xs : Fin 5 → Fin m) (w r T : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeTwoFiveRuleTermDispatchIffSentence xs w r T)) := ZFReplay.replay (modeTwoFiveRuleTermDispatchIff_kernel_certificate xs w r T)

def modeTwoBoundPreservedPositiveTraceSentence {m} (env : Fin 3 → Fin m) (w r : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 3 w env).imp ((HornExprSyntax.graph ((YesMetaZFC.Automation.ObjectSyntaxTransform.boundIdentity 2 true)).head w env r).imp ((Formula.mem (env 2) (env 0)).imp ((HornLookupConditionSyntax.condition w r)))))).close

theorem source_modeTwoBoundPreservedPositiveTrace {m} (env : Fin 3 → Fin m) (w r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeTwoBoundPreservedPositiveTraceSentence env w r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem (env 2) (env 0)) (Context.add (HornExprSyntax.graph ((YesMetaZFC.Automation.ObjectSyntaxTransform.boundIdentity 2 true)).head w env r) (Context.add (HornExprSyntax.environmentNat 3 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 3 w env) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (HornExprSyntax.graph ((YesMetaZFC.Automation.ObjectSyntaxTransform.boundIdentity 2 true)).head w env r) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (Formula.mem (env 2) (env 0)) := .hyp (Or.inl rfl)
  exact OriginalInstantiatePositive.bound_preserved hZ w r env h0 h1 h2 h3

theorem modeTwoBoundPreservedPositiveTrace_kernel_certificate {m} (env : Fin 3 → Fin m) (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeTwoBoundPreservedPositiveTraceSentence env w r)) := TheoryTransport.sentence (source_modeTwoBoundPreservedPositiveTrace env w r)

theorem native_modeTwoBoundPreservedPositiveTrace {m} (env : Fin 3 → Fin m) (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeTwoBoundPreservedPositiveTraceSentence env w r)) := ZFReplay.replay (modeTwoBoundPreservedPositiveTrace_kernel_certificate env w r)

def modeTwoBoundPointPositiveTraceSentence {m} (env : Fin 2 → Fin m) (w r : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 2 w env).imp ((HornExprSyntax.graph (YesMetaZFC.Automation.ObjectSyntaxTransform.boundPoint).head w env r).imp ((HornLookupConditionSyntax.condition w r))))).close

theorem source_modeTwoBoundPointPositiveTrace {m} (env : Fin 2 → Fin m) (w r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeTwoBoundPointPositiveTraceSentence env w r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.graph (YesMetaZFC.Automation.ObjectSyntaxTransform.boundPoint).head w env r) (Context.add (HornExprSyntax.environmentNat 2 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 2 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (HornExprSyntax.graph (YesMetaZFC.Automation.ObjectSyntaxTransform.boundPoint).head w env r) := .hyp (Or.inl rfl)
  exact OriginalInstantiatePositive.bound_point hZ w r env h0 h1 h2

theorem modeTwoBoundPointPositiveTrace_kernel_certificate {m} (env : Fin 2 → Fin m) (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeTwoBoundPointPositiveTraceSentence env w r)) := TheoryTransport.sentence (source_modeTwoBoundPointPositiveTrace env w r)

theorem native_modeTwoBoundPointPositiveTrace {m} (env : Fin 2 → Fin m) (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeTwoBoundPointPositiveTraceSentence env w r)) := ZFReplay.replay (modeTwoBoundPointPositiveTrace_kernel_certificate env w r)

def modeTwoBoundPredecessorPositiveTraceSentence {m} (env : Fin 3 → Fin m) (w r s : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 3 w env).imp ((HornExprSyntax.graph (YesMetaZFC.Automation.ObjectSyntaxTransform.boundPredecessor).head w env r).imp ((successor s (env 2)).imp ((Formula.mem (env 0) s).imp ((HornLookupConditionSyntax.condition w r))))))).close

theorem source_modeTwoBoundPredecessorPositiveTrace {m} (env : Fin 3 → Fin m) (w r s : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeTwoBoundPredecessorPositiveTraceSentence env w r s) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem (env 0) s) (Context.add (successor s (env 2)) (Context.add (HornExprSyntax.graph (YesMetaZFC.Automation.ObjectSyntaxTransform.boundPredecessor).head w env r) (Context.add (HornExprSyntax.environmentNat 3 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 3 w env) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (HornExprSyntax.graph (YesMetaZFC.Automation.ObjectSyntaxTransform.boundPredecessor).head w env r) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (successor s (env 2)) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (Formula.mem (env 0) s) := .hyp (Or.inl rfl)
  exact OriginalInstantiatePositive.bound_predecessor hZ w r s env h0 h1 h2 h3 h4

theorem modeTwoBoundPredecessorPositiveTrace_kernel_certificate {m} (env : Fin 3 → Fin m) (w r s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeTwoBoundPredecessorPositiveTraceSentence env w r s)) := TheoryTransport.sentence (source_modeTwoBoundPredecessorPositiveTrace env w r s)

theorem native_modeTwoBoundPredecessorPositiveTrace {m} (env : Fin 3 → Fin m) (w r s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeTwoBoundPredecessorPositiveTraceSentence env w r s)) := ZFReplay.replay (modeTwoBoundPredecessorPositiveTrace_kernel_certificate env w r s)

def modeTwoFreeIdentityPositiveTraceSentence {m} (env : Fin 3 → Fin m) (w r : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 3 w env).imp ((HornExprSyntax.graph (YesMetaZFC.Automation.ObjectSyntaxTransform.freeIdentity).head w env r).imp ((HornLookupConditionSyntax.condition w r))))).close

theorem source_modeTwoFreeIdentityPositiveTrace {m} (env : Fin 3 → Fin m) (w r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeTwoFreeIdentityPositiveTraceSentence env w r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.graph (YesMetaZFC.Automation.ObjectSyntaxTransform.freeIdentity).head w env r) (Context.add (HornExprSyntax.environmentNat 3 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 3 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (HornExprSyntax.graph (YesMetaZFC.Automation.ObjectSyntaxTransform.freeIdentity).head w env r) := .hyp (Or.inl rfl)
  exact OriginalInstantiatePositive.free_identity hZ w r env h0 h1 h2

theorem modeTwoFreeIdentityPositiveTrace_kernel_certificate {m} (env : Fin 3 → Fin m) (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeTwoFreeIdentityPositiveTraceSentence env w r)) := TheoryTransport.sentence (source_modeTwoFreeIdentityPositiveTrace env w r)

theorem native_modeTwoFreeIdentityPositiveTrace {m} (env : Fin 3 → Fin m) (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeTwoFreeIdentityPositiveTraceSentence env w r)) := ZFReplay.replay (modeTwoFreeIdentityPositiveTrace_kernel_certificate env w r)

def modeTwoClosedParameterFreeBranchSentence {m} (w e P : Fin m) : Source.Sentence := ((InstantiateOperationFrameSyntax.closedParameter w e P).imp ((SyntaxTermSyntax.branch false w e P))).close

theorem source_modeTwoClosedParameterFreeBranch {m} (w e P : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeTwoClosedParameterFreeBranchSentence w e P) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (InstantiateOperationFrameSyntax.closedParameter w e P) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (InstantiateOperationFrameSyntax.closedParameter w e P) := .hyp (Or.inl rfl)
  exact InstantiateOperationFrameSyntax.closedParameter_free w e P h0

theorem modeTwoClosedParameterFreeBranch_kernel_certificate {m} (w e P : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeTwoClosedParameterFreeBranchSentence w e P)) := TheoryTransport.sentence (source_modeTwoClosedParameterFreeBranch w e P)

theorem native_modeTwoClosedParameterFreeBranch {m} (w e P : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeTwoClosedParameterFreeBranchSentence w e P)) := ZFReplay.replay (modeTwoClosedParameterFreeBranch_kernel_certificate w e P)

def modeTwoFrameTermProgramIffSentence {m} (w mode depth P a b c e R S n q : Fin m) : Source.Sentence := ((omega w).imp ((InstantiateOperationFrameSyntax.frame w mode depth P a b c e R S).imp ((SyntaxTermSyntax.term w a b n).imp (((OriginalTransformRowSyntax.run 1 w mode depth P n q).iff (TermTransformProgramSyntax.run TermTransformProgramSyntax.termProgram w R S n q)))))).close

theorem source_modeTwoFrameTermProgramIff {m} (w mode depth P a b c e R S n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeTwoFrameTermProgramIffSentence w mode depth P a b c e R S n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTermSyntax.term w a b n) (Context.add (InstantiateOperationFrameSyntax.frame w mode depth P a b c e R S) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (InstantiateOperationFrameSyntax.frame w mode depth P a b c e R S) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxTermSyntax.term w a b n) := .hyp (Or.inl rfl)
  exact InstantiateFrameTerm.program_iff hZ w mode depth P a b c e R S n q h0 h1 h2

theorem modeTwoFrameTermProgramIff_kernel_certificate {m} (w mode depth P a b c e R S n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeTwoFrameTermProgramIffSentence w mode depth P a b c e R S n q)) := TheoryTransport.sentence (source_modeTwoFrameTermProgramIff w mode depth P a b c e R S n q)

theorem native_modeTwoFrameTermProgramIff {m} (w mode depth P a b c e R S n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeTwoFrameTermProgramIffSentence w mode depth P a b c e R S n q)) := ZFReplay.replay (modeTwoFrameTermProgramIff_kernel_certificate w mode depth P a b c e R S n q)

def modeTwoFrameTermCodedIffSentence {m} (w mode depth P a b c e R S n q : Fin m) : Source.Sentence := ((omega w).imp ((InstantiateOperationFrameSyntax.frame w mode depth P a b c e R S).imp ((SyntaxTermSyntax.term w a b n).imp (((OriginalTransformRowSyntax.run 1 w mode depth P n q).iff (SyntaxCodedMixedTermSyntax.substituted w R S a b c e n q)))))).close

theorem source_modeTwoFrameTermCodedIff {m} (w mode depth P a b c e R S n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeTwoFrameTermCodedIffSentence w mode depth P a b c e R S n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTermSyntax.term w a b n) (Context.add (InstantiateOperationFrameSyntax.frame w mode depth P a b c e R S) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (InstantiateOperationFrameSyntax.frame w mode depth P a b c e R S) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxTermSyntax.term w a b n) := .hyp (Or.inl rfl)
  exact InstantiateFrameTerm.coded_iff hZ w mode depth P a b c e R S n q h0 h1 h2

theorem modeTwoFrameTermCodedIff_kernel_certificate {m} (w mode depth P a b c e R S n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeTwoFrameTermCodedIffSentence w mode depth P a b c e R S n q)) := TheoryTransport.sentence (source_modeTwoFrameTermCodedIff w mode depth P a b c e R S n q)

theorem native_modeTwoFrameTermCodedIff {m} (w mode depth P a b c e R S n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeTwoFrameTermCodedIffSentence w mode depth P a b c e R S n q)) := ZFReplay.replay (modeTwoFrameTermCodedIff_kernel_certificate w mode depth P a b c e R S n q)

def modeTwoFrameGuardedTermCodedIffSentence {m} (w mode depth P a b c e R S n q : Fin m) : Source.Sentence := ((omega w).imp ((InstantiateOperationFrameSyntax.frame w mode depth P a b c e R S).imp ((((SyntaxTermSyntax.term w a b n).conj (OriginalTransformRowSyntax.run 1 w mode depth P n q)).iff (SyntaxCodedMixedTermSyntax.substituted w R S a b c e n q))))).close

theorem source_modeTwoFrameGuardedTermCodedIff {m} (w mode depth P a b c e R S n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeTwoFrameGuardedTermCodedIffSentence w mode depth P a b c e R S n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (InstantiateOperationFrameSyntax.frame w mode depth P a b c e R S) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (InstantiateOperationFrameSyntax.frame w mode depth P a b c e R S) := .hyp (Or.inl rfl)
  exact InstantiateFrameTerm.guarded_coded_iff hZ w mode depth P a b c e R S n q h0 h1

theorem modeTwoFrameGuardedTermCodedIff_kernel_certificate {m} (w mode depth P a b c e R S n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeTwoFrameGuardedTermCodedIffSentence w mode depth P a b c e R S n q)) := TheoryTransport.sentence (source_modeTwoFrameGuardedTermCodedIff w mode depth P a b c e R S n q)

theorem native_modeTwoFrameGuardedTermCodedIff {m} (w mode depth P a b c e R S n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeTwoFrameGuardedTermCodedIffSentence w mode depth P a b c e R S n q)) := ZFReplay.replay (modeTwoFrameGuardedTermCodedIff_kernel_certificate w mode depth P a b c e R S n q)

end PPAC.Migration.Internal.ObjectInstantiateVariable
