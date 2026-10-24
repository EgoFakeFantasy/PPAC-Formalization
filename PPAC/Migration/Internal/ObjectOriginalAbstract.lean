import PPAC.Migration.Internal.OriginalAbstractTrace

/-! 原mode1五规则分派、变量完整轨迹展开及四条实际轨迹引入的原核闭句。 -/
namespace PPAC.Migration.Internal.ObjectOriginalAbstract
open Source SourceAlgebra SourceLogic OmegaSyntax

def modeOneFiveRuleStepIffSentence {m} (xs : Fin 5 → Fin m) (w r R : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNodeSyntax.constructor 5 1 w xs r).imp ((SyntaxNumeralSyntax.numeral 1 (xs 0)).imp (((HornStepSyntax.originalStep w r R).iff (HornStepSyntax.step OriginalAbstractClasses.selected w r R)))))).close

theorem source_modeOneFiveRuleStepIff {m} (xs : Fin 5 → Fin m) (w r R : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeOneFiveRuleStepIffSentence xs w r R) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNumeralSyntax.numeral 1 (xs 0)) (Context.add (SyntaxNodeSyntax.constructor 5 1 w xs r) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxNodeSyntax.constructor 5 1 w xs r) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral 1 (xs 0)) := .hyp (Or.inl rfl)
  exact OriginalAbstractDispatch.dispatch_iff hZ w r R xs h0 h1 h2

theorem modeOneFiveRuleStepIff_kernel_certificate {m} (xs : Fin 5 → Fin m) (w r R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeOneFiveRuleStepIffSentence xs w r R)) := TheoryTransport.sentence (source_modeOneFiveRuleStepIff xs w r R)

theorem native_modeOneFiveRuleStepIff {m} (xs : Fin 5 → Fin m) (w r R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeOneFiveRuleStepIffSentence xs w r R)) := ZFReplay.replay (modeOneFiveRuleStepIff_kernel_certificate xs w r R)

def modeOneVariableTwoRuleStepIffSentence {m} (bound : Bool) (xs : Fin 5 → Fin m) (w r R idx : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNodeSyntax.constructor 5 1 w xs r).imp ((SyntaxNumeralSyntax.numeral 1 (xs 0)).imp ((SyntaxVariableSyntax.code bound w idx (xs 3)).imp (((HornStepSyntax.originalStep w r R).iff (HornStepSyntax.step (OriginalAbstractClasses.variableSelected bound) w r R))))))).close

theorem source_modeOneVariableTwoRuleStepIff {m} (bound : Bool) (xs : Fin 5 → Fin m) (w r R idx : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeOneVariableTwoRuleStepIffSentence bound xs w r R idx) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxVariableSyntax.code bound w idx (xs 3)) (Context.add (SyntaxNumeralSyntax.numeral 1 (xs 0)) (Context.add (SyntaxNodeSyntax.constructor 5 1 w xs r) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNodeSyntax.constructor 5 1 w xs r) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral 1 (xs 0)) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxVariableSyntax.code bound w idx (xs 3)) := .hyp (Or.inl rfl)
  exact OriginalAbstractDispatch.variable_dispatch_iff hZ bound w r R idx xs h0 h1 h2 h3

theorem modeOneVariableTwoRuleStepIff_kernel_certificate {m} (bound : Bool) (xs : Fin 5 → Fin m) (w r R idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeOneVariableTwoRuleStepIffSentence bound xs w r R idx)) := TheoryTransport.sentence (source_modeOneVariableTwoRuleStepIff bound xs w r R idx)

theorem native_modeOneVariableTwoRuleStepIff {m} (bound : Bool) (xs : Fin 5 → Fin m) (w r R idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeOneVariableTwoRuleStepIffSentence bound xs w r R idx)) := ZFReplay.replay (modeOneVariableTwoRuleStepIff_kernel_certificate bound xs w r R idx)

def modeOneVariableWholeTraceIffSentence {m} (bound : Bool) (xs : Fin 5 → Fin m) (w r idx : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNodeSyntax.constructor 5 1 w xs r).imp ((SyntaxNumeralSyntax.numeral 1 (xs 0)).imp ((SyntaxVariableSyntax.code bound w idx (xs 3)).imp (((HornLookupConditionSyntax.condition w r).iff (OriginalAbstractTrace.variableStep bound w r))))))).close

theorem source_modeOneVariableWholeTraceIff {m} (bound : Bool) (xs : Fin 5 → Fin m) (w r idx : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeOneVariableWholeTraceIffSentence bound xs w r idx) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxVariableSyntax.code bound w idx (xs 3)) (Context.add (SyntaxNumeralSyntax.numeral 1 (xs 0)) (Context.add (SyntaxNodeSyntax.constructor 5 1 w xs r) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNodeSyntax.constructor 5 1 w xs r) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral 1 (xs 0)) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxVariableSyntax.code bound w idx (xs 3)) := .hyp (Or.inl rfl)
  exact OriginalAbstractTrace.variable_condition_iff hZ bound w r idx xs h0 h1 h2 h3

theorem modeOneVariableWholeTraceIff_kernel_certificate {m} (bound : Bool) (xs : Fin 5 → Fin m) (w r idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeOneVariableWholeTraceIffSentence bound xs w r idx)) := TheoryTransport.sentence (source_modeOneVariableWholeTraceIff bound xs w r idx)

theorem native_modeOneVariableWholeTraceIff {m} (bound : Bool) (xs : Fin 5 → Fin m) (w r idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeOneVariableWholeTraceIffSentence bound xs w r idx)) := ZFReplay.replay (modeOneVariableWholeTraceIff_kernel_certificate bound xs w r idx)

def modeOneBoundIdentityGuardIffSentence {m} (env : Fin 3 → Fin m) (w : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 3 w env).imp (((HornRuleSyntax.guards (YesMetaZFC.Automation.ObjectSyntaxTransform.boundIdentity 1 true).guards w env).iff (Formula.mem (env 2) (env 0)))))).close

theorem source_modeOneBoundIdentityGuardIff {m} (env : Fin 3 → Fin m) (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeOneBoundIdentityGuardIffSentence env w) := by
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
  exact OriginalAbstractPositive.bound_identity_guard_iff hZ w env h0 h1

theorem modeOneBoundIdentityGuardIff_kernel_certificate {m} (env : Fin 3 → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeOneBoundIdentityGuardIffSentence env w)) := TheoryTransport.sentence (source_modeOneBoundIdentityGuardIff env w)

theorem native_modeOneBoundIdentityGuardIff {m} (env : Fin 3 → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeOneBoundIdentityGuardIffSentence env w)) := ZFReplay.replay (modeOneBoundIdentityGuardIff_kernel_certificate env w)

def modeOneBoundAbstractGuardIffSentence {m} (env : Fin 3 → Fin m) (w s : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 3 w env).imp ((successor s (env 2)).imp (((HornRuleSyntax.guards YesMetaZFC.Automation.ObjectSyntaxTransform.boundAbstract.guards w env).iff (Formula.mem (env 0) s)))))).close

theorem source_modeOneBoundAbstractGuardIff {m} (env : Fin 3 → Fin m) (w s : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeOneBoundAbstractGuardIffSentence env w s) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor s (env 2)) (Context.add (HornExprSyntax.environmentNat 3 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 3 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (successor s (env 2)) := .hyp (Or.inl rfl)
  exact OriginalAbstractPositive.bound_abstract_guard_iff hZ w s env h0 h1 h2

theorem modeOneBoundAbstractGuardIff_kernel_certificate {m} (env : Fin 3 → Fin m) (w s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeOneBoundAbstractGuardIffSentence env w s)) := TheoryTransport.sentence (source_modeOneBoundAbstractGuardIff env w s)

theorem native_modeOneBoundAbstractGuardIff {m} (env : Fin 3 → Fin m) (w s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeOneBoundAbstractGuardIffSentence env w s)) := ZFReplay.replay (modeOneBoundAbstractGuardIff_kernel_certificate env w s)

def modeOneBoundPreservedTraceSentence {m} (env : Fin 3 → Fin m) (w r : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 3 w env).imp ((HornExprSyntax.graph (YesMetaZFC.Automation.ObjectSyntaxTransform.boundIdentity 1 true).head w env r).imp ((Formula.mem (env 2) (env 0)).imp ((HornLookupConditionSyntax.condition w r)))))).close

theorem source_modeOneBoundPreservedTrace {m} (env : Fin 3 → Fin m) (w r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeOneBoundPreservedTraceSentence env w r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem (env 2) (env 0)) (Context.add (HornExprSyntax.graph (YesMetaZFC.Automation.ObjectSyntaxTransform.boundIdentity 1 true).head w env r) (Context.add (HornExprSyntax.environmentNat 3 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 3 w env) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (HornExprSyntax.graph (YesMetaZFC.Automation.ObjectSyntaxTransform.boundIdentity 1 true).head w env r) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (Formula.mem (env 2) (env 0)) := .hyp (Or.inl rfl)
  exact OriginalAbstractPositive.bound_preserved hZ w r env h0 h1 h2 h3

theorem modeOneBoundPreservedTrace_kernel_certificate {m} (env : Fin 3 → Fin m) (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeOneBoundPreservedTraceSentence env w r)) := TheoryTransport.sentence (source_modeOneBoundPreservedTrace env w r)

theorem native_modeOneBoundPreservedTrace {m} (env : Fin 3 → Fin m) (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeOneBoundPreservedTraceSentence env w r)) := ZFReplay.replay (modeOneBoundPreservedTrace_kernel_certificate env w r)

def modeOneBoundShiftedTraceSentence {m} (env : Fin 3 → Fin m) (w r s : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 3 w env).imp ((HornExprSyntax.graph YesMetaZFC.Automation.ObjectSyntaxTransform.boundAbstract.head w env r).imp ((successor s (env 2)).imp ((Formula.mem (env 0) s).imp ((HornLookupConditionSyntax.condition w r))))))).close

theorem source_modeOneBoundShiftedTrace {m} (env : Fin 3 → Fin m) (w r s : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeOneBoundShiftedTraceSentence env w r s) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem (env 0) s) (Context.add (successor s (env 2)) (Context.add (HornExprSyntax.graph YesMetaZFC.Automation.ObjectSyntaxTransform.boundAbstract.head w env r) (Context.add (HornExprSyntax.environmentNat 3 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 3 w env) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (HornExprSyntax.graph YesMetaZFC.Automation.ObjectSyntaxTransform.boundAbstract.head w env r) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (successor s (env 2)) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (Formula.mem (env 0) s) := .hyp (Or.inl rfl)
  exact OriginalAbstractPositive.bound_shifted hZ w r s env h0 h1 h2 h3 h4

theorem modeOneBoundShiftedTrace_kernel_certificate {m} (env : Fin 3 → Fin m) (w r s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeOneBoundShiftedTraceSentence env w r s)) := TheoryTransport.sentence (source_modeOneBoundShiftedTrace env w r s)

theorem native_modeOneBoundShiftedTrace {m} (env : Fin 3 → Fin m) (w r s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeOneBoundShiftedTraceSentence env w r s)) := ZFReplay.replay (modeOneBoundShiftedTrace_kernel_certificate env w r s)

def modeOneFreeHeadTraceSentence {m} (env : Fin 2 → Fin m) (w r : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 2 w env).imp ((HornExprSyntax.graph YesMetaZFC.Automation.ObjectSyntaxTransform.freeAbstractHead.head w env r).imp ((HornLookupConditionSyntax.condition w r))))).close

theorem source_modeOneFreeHeadTrace {m} (env : Fin 2 → Fin m) (w r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeOneFreeHeadTraceSentence env w r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.graph YesMetaZFC.Automation.ObjectSyntaxTransform.freeAbstractHead.head w env r) (Context.add (HornExprSyntax.environmentNat 2 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 2 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (HornExprSyntax.graph YesMetaZFC.Automation.ObjectSyntaxTransform.freeAbstractHead.head w env r) := .hyp (Or.inl rfl)
  exact OriginalAbstractPositive.free_head hZ w r env h0 h1 h2

theorem modeOneFreeHeadTrace_kernel_certificate {m} (env : Fin 2 → Fin m) (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeOneFreeHeadTraceSentence env w r)) := TheoryTransport.sentence (source_modeOneFreeHeadTrace env w r)

theorem native_modeOneFreeHeadTrace {m} (env : Fin 2 → Fin m) (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeOneFreeHeadTraceSentence env w r)) := ZFReplay.replay (modeOneFreeHeadTrace_kernel_certificate env w r)

def modeOneFreeTailTraceSentence {m} (env : Fin 3 → Fin m) (w r : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 3 w env).imp ((HornExprSyntax.graph YesMetaZFC.Automation.ObjectSyntaxTransform.freeAbstractTail.head w env r).imp ((HornLookupConditionSyntax.condition w r))))).close

theorem source_modeOneFreeTailTrace {m} (env : Fin 3 → Fin m) (w r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeOneFreeTailTraceSentence env w r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.graph YesMetaZFC.Automation.ObjectSyntaxTransform.freeAbstractTail.head w env r) (Context.add (HornExprSyntax.environmentNat 3 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 3 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (HornExprSyntax.graph YesMetaZFC.Automation.ObjectSyntaxTransform.freeAbstractTail.head w env r) := .hyp (Or.inl rfl)
  exact OriginalAbstractPositive.free_tail hZ w r env h0 h1 h2

theorem modeOneFreeTailTrace_kernel_certificate {m} (env : Fin 3 → Fin m) (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeOneFreeTailTraceSentence env w r)) := TheoryTransport.sentence (source_modeOneFreeTailTrace env w r)

theorem native_modeOneFreeTailTrace {m} (env : Fin 3 → Fin m) (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeOneFreeTailTraceSentence env w r)) := ZFReplay.replay (modeOneFreeTailTrace_kernel_certificate env w r)

end PPAC.Migration.Internal.ObjectOriginalAbstract
