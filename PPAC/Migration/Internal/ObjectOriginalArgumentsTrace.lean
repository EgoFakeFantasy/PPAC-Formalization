import PPAC.Migration.Internal.OriginalArgumentsTraceRules

/-! 原完整表通用轨迹实际集合、共享子轨迹及参数列表分派的原核证书。 -/
namespace PPAC.Migration.Internal.ObjectOriginalArgumentsTrace
open Source SourceAlgebra SourceLogic OmegaSyntax
open YesMetaZFC.Automation.ObjectHorn (Rule)

def actualUniversalOriginalTraceSentence {m} (w : Fin m) : Source.Sentence := ((HornUniversalTraceSyntax.existsValue w)).close

theorem source_actualUniversalOriginalTrace {m} (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (actualUniversalOriginalTraceSentence w) := by
  apply close_derives
  let Δ : Context m := Source.SetLanguage.ZF.at m
  have hZ : ZFContext.Evidence Δ := by
    exact ZFContext.source_ZF m
  exact HornUniversalTraceValue.exists_value hZ w

theorem actualUniversalOriginalTrace_kernel_certificate {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (actualUniversalOriginalTraceSentence w)) := TheoryTransport.sentence (source_actualUniversalOriginalTrace w)

theorem native_actualUniversalOriginalTrace {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (actualUniversalOriginalTraceSentence w)) := ZFReplay.replay (actualUniversalOriginalTrace_kernel_certificate w)

def universalOriginalTraceMembershipIffSentence {m} (w V r : Fin m) : Source.Sentence := ((HornUniversalTraceSyntax.value w V).imp (((Formula.mem r V).iff (HornLookupConditionSyntax.condition w r)))).close

theorem source_universalOriginalTraceMembershipIff {m} (w V r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (universalOriginalTraceMembershipIffSentence w V r) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (HornUniversalTraceSyntax.value w V) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (HornUniversalTraceSyntax.value w V) := .hyp (Or.inl rfl)
  exact HornUniversalTraceValue.member_iff w V r h0

theorem universalOriginalTraceMembershipIff_kernel_certificate {m} (w V r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (universalOriginalTraceMembershipIffSentence w V r)) := TheoryTransport.sentence (source_universalOriginalTraceMembershipIff w V r)

theorem native_universalOriginalTraceMembershipIff {m} (w V r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (universalOriginalTraceMembershipIffSentence w V r)) := ZFReplay.replay (universalOriginalTraceMembershipIff_kernel_certificate w V r)

def everyClosedOriginalTraceIncludedSentence {m} (w V R : Fin m) : Source.Sentence := ((HornUniversalTraceSyntax.value w V).imp ((RestrictionSyntax.subset R w).imp ((HornLookupSoundSyntax.closed w R).imp ((RestrictionSyntax.subset R V))))).close

theorem source_everyClosedOriginalTraceIncluded {m} (w V R : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (everyClosedOriginalTraceIncludedSentence w V R) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornLookupSoundSyntax.closed w R) (Context.add (RestrictionSyntax.subset R w) (Context.add (HornUniversalTraceSyntax.value w V) (Source.SetLanguage.ZF.at m)))
  have h0 : Derives Δ (HornUniversalTraceSyntax.value w V) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (RestrictionSyntax.subset R w) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (HornLookupSoundSyntax.closed w R) := .hyp (Or.inl rfl)
  exact HornUniversalTraceValue.subtrace_included w V R h0 h1 h2

theorem everyClosedOriginalTraceIncluded_kernel_certificate {m} (w V R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (everyClosedOriginalTraceIncludedSentence w V R)) := TheoryTransport.sentence (source_everyClosedOriginalTraceIncluded w V R)

theorem native_everyClosedOriginalTraceIncluded {m} (w V R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (everyClosedOriginalTraceIncludedSentence w V R)) := ZFReplay.replay (everyClosedOriginalTraceIncluded_kernel_certificate w V R)

def universalOriginalTraceClosedSentence {m} (w V : Fin m) : Source.Sentence := ((HornUniversalTraceSyntax.value w V).imp ((HornLookupSoundSyntax.closed w V))).close

theorem source_universalOriginalTraceClosed {m} (w V : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (universalOriginalTraceClosedSentence w V) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (HornUniversalTraceSyntax.value w V) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (HornUniversalTraceSyntax.value w V) := .hyp (Or.inl rfl)
  exact HornUniversalTraceClosed.closed w V h0

theorem universalOriginalTraceClosed_kernel_certificate {m} (w V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (universalOriginalTraceClosedSentence w V)) := TheoryTransport.sentence (source_universalOriginalTraceClosed w V)

theorem native_universalOriginalTraceClosed {m} (w V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (universalOriginalTraceClosedSentence w V)) := ZFReplay.replay (universalOriginalTraceClosed_kernel_certificate w V)

def originalFullTraceOneStepIffSentence {m} (w V r : Fin m) : Source.Sentence := ((HornUniversalTraceSyntax.value w V).imp ((Formula.mem r w).imp (((HornLookupConditionSyntax.condition w r).iff (HornStepSyntax.originalStep w r V))))).close

theorem source_originalFullTraceOneStepIff {m} (w V r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalFullTraceOneStepIffSentence w V r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem r w) (Context.add (HornUniversalTraceSyntax.value w V) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (HornUniversalTraceSyntax.value w V) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (Formula.mem r w) := .hyp (Or.inl rfl)
  exact HornUniversalTraceClosed.unfold_iff hZ w V r h0 h1

theorem originalFullTraceOneStepIff_kernel_certificate {m} (w V r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalFullTraceOneStepIffSentence w V r)) := TheoryTransport.sentence (source_originalFullTraceOneStepIff w V r)

theorem native_originalFullTraceOneStepIff {m} (w V r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalFullTraceOneStepIffSentence w V r)) := ZFReplay.replay (originalFullTraceOneStepIff_kernel_certificate w V r)

def originalWholeTableRuleFromTracesSentence {m} (rule : Rule) (_hr : rule ∈ YesMetaZFC.Automation.ObjectSyntaxTransform.rules) (env : Fin rule.arity → Fin m) (w r : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat rule.arity w env).imp ((HornUniversalTraceRules.tracedMatrix rule w r env).imp ((HornLookupConditionSyntax.condition w r))))).close

theorem source_originalWholeTableRuleFromTraces {m} (rule : Rule) (_hr : rule ∈ YesMetaZFC.Automation.ObjectSyntaxTransform.rules) (env : Fin rule.arity → Fin m) (w r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalWholeTableRuleFromTracesSentence rule _hr env w r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornUniversalTraceRules.tracedMatrix rule w r env) (Context.add (HornExprSyntax.environmentNat rule.arity w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat rule.arity w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (HornUniversalTraceRules.tracedMatrix rule w r env) := .hyp (Or.inl rfl)
  exact OriginalRuleHeadVariables.apply_original_rule hZ rule _hr w r env h0 h1 h2

theorem originalWholeTableRuleFromTraces_kernel_certificate {m} (rule : Rule) (_hr : rule ∈ YesMetaZFC.Automation.ObjectSyntaxTransform.rules) (env : Fin rule.arity → Fin m) (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalWholeTableRuleFromTracesSentence rule _hr env w r)) := TheoryTransport.sentence (source_originalWholeTableRuleFromTraces rule _hr env w r)

theorem native_originalWholeTableRuleFromTraces {m} (rule : Rule) (_hr : rule ∈ YesMetaZFC.Automation.ObjectSyntaxTransform.rules) (env : Fin rule.arity → Fin m) (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalWholeTableRuleFromTracesSentence rule _hr env w r)) := ZFReplay.replay (originalWholeTableRuleFromTraces_kernel_certificate rule _hr env w r)

def originalArgumentFullTableDispatchIffSentence {m} (xs : Fin 5 → Fin m) (w r R : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNodeSyntax.constructor 5 2 w xs r).imp (((HornStepSyntax.originalStep w r R).iff (HornStepSyntax.step OriginalArgumentsClasses.selected w r R))))).close

theorem source_originalArgumentFullTableDispatchIff {m} (xs : Fin 5 → Fin m) (w r R : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalArgumentFullTableDispatchIffSentence xs w r R) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNodeSyntax.constructor 5 2 w xs r) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxNodeSyntax.constructor 5 2 w xs r) := .hyp (Or.inl rfl)
  exact OriginalArgumentsDispatch.dispatch_iff hZ w r R xs h0 h1

theorem originalArgumentFullTableDispatchIff_kernel_certificate {m} (xs : Fin 5 → Fin m) (w r R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalArgumentFullTableDispatchIffSentence xs w r R)) := TheoryTransport.sentence (source_originalArgumentFullTableDispatchIff xs w r R)

theorem native_originalArgumentFullTableDispatchIff {m} (xs : Fin 5 → Fin m) (w r R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalArgumentFullTableDispatchIffSentence xs w r R)) := ZFReplay.replay (originalArgumentFullTableDispatchIff_kernel_certificate xs w r R)

def originalArgumentTraceSelectedIffSentence {m} (xs : Fin 5 → Fin m) (w r V : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNodeSyntax.constructor 5 2 w xs r).imp ((HornUniversalTraceSyntax.value w V).imp (((HornLookupConditionSyntax.condition w r).iff (HornStepSyntax.step OriginalArgumentsClasses.selected w r V)))))).close

theorem source_originalArgumentTraceSelectedIff {m} (xs : Fin 5 → Fin m) (w r V : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalArgumentTraceSelectedIffSentence xs w r V) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornUniversalTraceSyntax.value w V) (Context.add (SyntaxNodeSyntax.constructor 5 2 w xs r) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxNodeSyntax.constructor 5 2 w xs r) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (HornUniversalTraceSyntax.value w V) := .hyp (Or.inl rfl)
  exact OriginalArgumentsDispatch.trace_iff_selected hZ w r V xs h0 h1 h2

theorem originalArgumentTraceSelectedIff_kernel_certificate {m} (xs : Fin 5 → Fin m) (w r V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalArgumentTraceSelectedIffSentence xs w r V)) := TheoryTransport.sentence (source_originalArgumentTraceSelectedIff xs w r V)

theorem native_originalArgumentTraceSelectedIff {m} (xs : Fin 5 → Fin m) (w r V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalArgumentTraceSelectedIffSentence xs w r V)) := ZFReplay.replay (originalArgumentTraceSelectedIff_kernel_certificate xs w r V)

def originalNilArgumentsTraceSentence {m} (env : Fin 3 → Fin m) (w r : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 3 w env).imp ((HornExprSyntax.graph (YesMetaZFC.Automation.ObjectSyntaxTransform.nilArguments).head w env r).imp ((HornRuleSyntax.guards (YesMetaZFC.Automation.ObjectSyntaxTransform.nilArguments).guards w env).imp ((HornLookupConditionSyntax.condition w r)))))).close

theorem source_originalNilArgumentsTrace {m} (env : Fin 3 → Fin m) (w r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalNilArgumentsTraceSentence env w r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornRuleSyntax.guards (YesMetaZFC.Automation.ObjectSyntaxTransform.nilArguments).guards w env) (Context.add (HornExprSyntax.graph (YesMetaZFC.Automation.ObjectSyntaxTransform.nilArguments).head w env r) (Context.add (HornExprSyntax.environmentNat 3 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 3 w env) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (HornExprSyntax.graph (YesMetaZFC.Automation.ObjectSyntaxTransform.nilArguments).head w env r) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (HornRuleSyntax.guards (YesMetaZFC.Automation.ObjectSyntaxTransform.nilArguments).guards w env) := .hyp (Or.inl rfl)
  exact OriginalArgumentsTraceRules.nil_condition hZ w r env h0 h1 h2 h3

theorem originalNilArgumentsTrace_kernel_certificate {m} (env : Fin 3 → Fin m) (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalNilArgumentsTraceSentence env w r)) := TheoryTransport.sentence (source_originalNilArgumentsTrace env w r)

theorem native_originalNilArgumentsTrace {m} (env : Fin 3 → Fin m) (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalNilArgumentsTraceSentence env w r)) := ZFReplay.replay (originalNilArgumentsTrace_kernel_certificate env w r)

def originalConsArgumentsTraceSentence {m} (env : Fin 7 → Fin m) (w r : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 7 w env).imp ((HornExprSyntax.graph (YesMetaZFC.Automation.ObjectSyntaxTransform.consArguments).head w env r).imp ((HornUniversalTraceRules.tracedPremise OriginalArgumentsTraceRules.headPremise w env).imp ((HornUniversalTraceRules.tracedPremise OriginalArgumentsTraceRules.tailPremise w env).imp ((HornLookupConditionSyntax.condition w r))))))).close

theorem source_originalConsArgumentsTrace {m} (env : Fin 7 → Fin m) (w r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalConsArgumentsTraceSentence env w r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornUniversalTraceRules.tracedPremise OriginalArgumentsTraceRules.tailPremise w env) (Context.add (HornUniversalTraceRules.tracedPremise OriginalArgumentsTraceRules.headPremise w env) (Context.add (HornExprSyntax.graph (YesMetaZFC.Automation.ObjectSyntaxTransform.consArguments).head w env r) (Context.add (HornExprSyntax.environmentNat 7 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 7 w env) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (HornExprSyntax.graph (YesMetaZFC.Automation.ObjectSyntaxTransform.consArguments).head w env r) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (HornUniversalTraceRules.tracedPremise OriginalArgumentsTraceRules.headPremise w env) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (HornUniversalTraceRules.tracedPremise OriginalArgumentsTraceRules.tailPremise w env) := .hyp (Or.inl rfl)
  exact OriginalArgumentsTraceRules.cons_condition hZ w r env h0 h1 h2 h3 h4

theorem originalConsArgumentsTrace_kernel_certificate {m} (env : Fin 7 → Fin m) (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalConsArgumentsTraceSentence env w r)) := TheoryTransport.sentence (source_originalConsArgumentsTrace env w r)

theorem native_originalConsArgumentsTrace {m} (env : Fin 7 → Fin m) (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalConsArgumentsTraceSentence env w r)) := ZFReplay.replay (originalConsArgumentsTrace_kernel_certificate env w r)

def originalConsArgumentActualChildTracesSentence {m} (env : Fin 7 → Fin m) (w r first rest : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 7 w env).imp ((HornExprSyntax.graph (YesMetaZFC.Automation.ObjectSyntaxTransform.consArguments).head w env r).imp ((HornExprSyntax.graph OriginalArgumentsTraceRules.headPremise w env first).imp ((HornExprSyntax.graph OriginalArgumentsTraceRules.tailPremise w env rest).imp ((HornLookupConditionSyntax.condition w first).imp ((HornLookupConditionSyntax.condition w rest).imp ((HornLookupConditionSyntax.condition w r))))))))).close

theorem source_originalConsArgumentActualChildTraces {m} (env : Fin 7 → Fin m) (w r first rest : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalConsArgumentActualChildTracesSentence env w r first rest) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornLookupConditionSyntax.condition w rest) (Context.add (HornLookupConditionSyntax.condition w first) (Context.add (HornExprSyntax.graph OriginalArgumentsTraceRules.tailPremise w env rest) (Context.add (HornExprSyntax.graph OriginalArgumentsTraceRules.headPremise w env first) (Context.add (HornExprSyntax.graph (YesMetaZFC.Automation.ObjectSyntaxTransform.consArguments).head w env r) (Context.add (HornExprSyntax.environmentNat 7 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 7 w env) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h2 : Derives Δ (HornExprSyntax.graph (YesMetaZFC.Automation.ObjectSyntaxTransform.consArguments).head w env r) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h3 : Derives Δ (HornExprSyntax.graph OriginalArgumentsTraceRules.headPremise w env first) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : Derives Δ (HornExprSyntax.graph OriginalArgumentsTraceRules.tailPremise w env rest) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h5 : Derives Δ (HornLookupConditionSyntax.condition w first) := .hyp (Or.inr (Or.inl rfl))
  have h6 : Derives Δ (HornLookupConditionSyntax.condition w rest) := .hyp (Or.inl rfl)
  exact OriginalArgumentsTraceRules.cons_conditions_at_values hZ w r first rest env h0 h1 h2 h3 h4 h5 h6

theorem originalConsArgumentActualChildTraces_kernel_certificate {m} (env : Fin 7 → Fin m) (w r first rest : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalConsArgumentActualChildTracesSentence env w r first rest)) := TheoryTransport.sentence (source_originalConsArgumentActualChildTraces env w r first rest)

theorem native_originalConsArgumentActualChildTraces {m} (env : Fin 7 → Fin m) (w r first rest : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalConsArgumentActualChildTracesSentence env w r first rest)) := ZFReplay.replay (originalConsArgumentActualChildTraces_kernel_certificate env w r first rest)

end PPAC.Migration.Internal.ObjectOriginalArgumentsTrace
