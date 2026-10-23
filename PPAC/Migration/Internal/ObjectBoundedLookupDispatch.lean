import PPAC.Migration.Internal.HornSearchRules

/-! 实际原规则的内部有界量化、完整全表查找分派及后继搜索界的原YesMetaZFC核证书。 -/
namespace PPAC.Migration.Internal.ObjectBoundedLookupDispatch
open Source SourceAlgebra SourceLogic OmegaSyntax

def naturalAssignmentFromSearchBoundSentence {m} {n} (env : Fin n → Fin m) (w row : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem row w).imp ((HornExprBounds.environmentBound n row env).imp ((HornExprSyntax.environmentNat n w env))))).close

theorem source_naturalAssignmentFromSearchBound {m} {n} (env : Fin n → Fin m) (w row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (naturalAssignmentFromSearchBoundSentence env w row) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprBounds.environmentBound n row env) (Context.add (Formula.mem row w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (Formula.mem row w) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (HornExprBounds.environmentBound n row env) := .hyp (Or.inl rfl)
  exact HornApplicationRules.natural_environment hZ w row env h0 h1 h2

theorem naturalAssignmentFromSearchBound_kernel_certificate {m} {n} (env : Fin n → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (naturalAssignmentFromSearchBoundSentence env w row)) := TheoryTransport.sentence (source_naturalAssignmentFromSearchBound env w row)

theorem native_naturalAssignmentFromSearchBound {m} {n} (env : Fin n → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (naturalAssignmentFromSearchBoundSentence env w row)) := ZFReplay.replay (naturalAssignmentFromSearchBound_kernel_certificate env w row)

def boundedRuleApplicationSentence {m} (rule : YesMetaZFC.Automation.ObjectHorn.Rule) (env : Fin rule.arity → Fin m) (w row trace : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem row w).imp ((HornExprBounds.environmentBound rule.arity row env).imp ((HornRuleSyntax.matrix rule w row trace env).imp ((HornApplicationSyntax.application rule w row trace)))))).close

theorem source_boundedRuleApplication {m} (rule : YesMetaZFC.Automation.ObjectHorn.Rule) (env : Fin rule.arity → Fin m) (w row trace : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (boundedRuleApplicationSentence rule env w row trace) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornRuleSyntax.matrix rule w row trace env) (Context.add (HornExprBounds.environmentBound rule.arity row env) (Context.add (Formula.mem row w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (Formula.mem row w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (HornExprBounds.environmentBound rule.arity row env) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (HornRuleSyntax.matrix rule w row trace env) := .hyp (Or.inl rfl)
  exact HornApplicationRules.intro_bounded hZ rule w row trace env h0 h1 h2 h3

theorem boundedRuleApplication_kernel_certificate {m} (rule : YesMetaZFC.Automation.ObjectHorn.Rule) (env : Fin rule.arity → Fin m) (w row trace : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (boundedRuleApplicationSentence rule env w row trace)) := TheoryTransport.sentence (source_boundedRuleApplication rule env w row trace)

theorem native_boundedRuleApplication {m} (rule : YesMetaZFC.Automation.ObjectHorn.Rule) (env : Fin rule.arity → Fin m) (w row trace : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (boundedRuleApplicationSentence rule env w row trace)) := ZFReplay.replay (boundedRuleApplication_kernel_certificate rule env w row trace)

def originalLookupHeadApplicationSentence {m} (env : Fin 2 → Fin m) (w row trace : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 2 w env).imp ((HornRuleSyntax.matrix YesMetaZFC.Automation.ObjectSyntaxTransform.lookupHead w row trace env).imp ((HornApplicationSyntax.application YesMetaZFC.Automation.ObjectSyntaxTransform.lookupHead w row trace))))).close

theorem source_originalLookupHeadApplication {m} (env : Fin 2 → Fin m) (w row trace : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalLookupHeadApplicationSentence env w row trace) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornRuleSyntax.matrix YesMetaZFC.Automation.ObjectSyntaxTransform.lookupHead w row trace env) (Context.add (HornExprSyntax.environmentNat 2 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 2 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (HornRuleSyntax.matrix YesMetaZFC.Automation.ObjectSyntaxTransform.lookupHead w row trace env) := .hyp (Or.inl rfl)
  exact HornApplicationRules.lookup_head_intro hZ w row trace env h0 h1 h2

theorem originalLookupHeadApplication_kernel_certificate {m} (env : Fin 2 → Fin m) (w row trace : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalLookupHeadApplicationSentence env w row trace)) := TheoryTransport.sentence (source_originalLookupHeadApplication env w row trace)

theorem native_originalLookupHeadApplication {m} (env : Fin 2 → Fin m) (w row trace : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalLookupHeadApplicationSentence env w row trace)) := ZFReplay.replay (originalLookupHeadApplication_kernel_certificate env w row trace)

def originalLookupTailApplicationSentence {m} (env : Fin 4 → Fin m) (w row trace : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 4 w env).imp ((HornRuleSyntax.matrix YesMetaZFC.Automation.ObjectSyntaxTransform.lookupTail w row trace env).imp ((HornApplicationSyntax.application YesMetaZFC.Automation.ObjectSyntaxTransform.lookupTail w row trace))))).close

theorem source_originalLookupTailApplication {m} (env : Fin 4 → Fin m) (w row trace : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalLookupTailApplicationSentence env w row trace) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornRuleSyntax.matrix YesMetaZFC.Automation.ObjectSyntaxTransform.lookupTail w row trace env) (Context.add (HornExprSyntax.environmentNat 4 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 4 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (HornRuleSyntax.matrix YesMetaZFC.Automation.ObjectSyntaxTransform.lookupTail w row trace env) := .hyp (Or.inl rfl)
  exact HornApplicationRules.lookup_tail_intro hZ w row trace env h0 h1 h2

theorem originalLookupTailApplication_kernel_certificate {m} (env : Fin 4 → Fin m) (w row trace : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalLookupTailApplicationSentence env w row trace)) := TheoryTransport.sentence (source_originalLookupTailApplication env w row trace)

theorem native_originalLookupTailApplication {m} (env : Fin 4 → Fin m) (w row trace : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalLookupTailApplicationSentence env w row trace)) := ZFReplay.replay (originalLookupTailApplication_kernel_certificate env w row trace)

def searchBoundMembershipIffSentence {m} {n} (env : Fin n → Fin m) (row s : Fin m) : Source.Sentence := ((successor s row).imp (((HornExprBounds.environmentBound n row env).iff (HornExprSyntax.environmentNat n s env)))).close

theorem source_searchBoundMembershipIff {m} {n} (env : Fin n → Fin m) (row s : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (searchBoundMembershipIffSentence env row s) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (successor s row) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (successor s row) := .hyp (Or.inl rfl)
  exact HornApplicationBounds.bound_iff_inside row s env h0

theorem searchBoundMembershipIff_kernel_certificate {m} {n} (env : Fin n → Fin m) (row s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (searchBoundMembershipIffSentence env row s)) := TheoryTransport.sentence (source_searchBoundMembershipIff env row s)

theorem native_searchBoundMembershipIff {m} {n} (env : Fin n → Fin m) (row s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (searchBoundMembershipIffSentence env row s)) := ZFReplay.replay (searchBoundMembershipIff_kernel_certificate env row s)

def originalBoundedMatrixIffSentence {m} (rule : YesMetaZFC.Automation.ObjectHorn.Rule) (env : Fin rule.arity → Fin m) (w row trace s : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem row w).imp ((successor s row).imp (((HornApplicationSyntax.boundedMatrix rule w row trace env).iff ((HornExprSyntax.environmentNat rule.arity s env).conj (HornRuleSyntax.matrix rule w row trace env))))))).close

theorem source_originalBoundedMatrixIff {m} (rule : YesMetaZFC.Automation.ObjectHorn.Rule) (env : Fin rule.arity → Fin m) (w row trace s : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalBoundedMatrixIffSentence rule env w row trace s) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor s row) (Context.add (Formula.mem row w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (Formula.mem row w) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (successor s row) := .hyp (Or.inl rfl)
  exact HornApplicationBounds.matrix_iff_inside hZ rule w row trace s env h0 h1 h2

theorem originalBoundedMatrixIff_kernel_certificate {m} (rule : YesMetaZFC.Automation.ObjectHorn.Rule) (env : Fin rule.arity → Fin m) (w row trace s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalBoundedMatrixIffSentence rule env w row trace s)) := TheoryTransport.sentence (source_originalBoundedMatrixIff rule env w row trace s)

theorem native_originalBoundedMatrixIff {m} (rule : YesMetaZFC.Automation.ObjectHorn.Rule) (env : Fin rule.arity → Fin m) (w row trace s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalBoundedMatrixIffSentence rule env w row trace s)) := ZFReplay.replay (originalBoundedMatrixIff_kernel_certificate rule env w row trace s)

def originalQuantifiedApplicationIffSentence {m} (rule : YesMetaZFC.Automation.ObjectHorn.Rule) (w row trace s : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem row w).imp ((successor s row).imp (((HornApplicationSyntax.application rule w row trace).iff (HornApplicationBounds.boundedAt rule w row trace s)))))).close

theorem source_originalQuantifiedApplicationIff {m} (rule : YesMetaZFC.Automation.ObjectHorn.Rule) (w row trace s : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalQuantifiedApplicationIffSentence rule w row trace s) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor s row) (Context.add (Formula.mem row w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (Formula.mem row w) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (successor s row) := .hyp (Or.inl rfl)
  exact HornApplicationBounds.application_iff_boundedAt hZ rule w row trace s h0 h1 h2

theorem originalQuantifiedApplicationIff_kernel_certificate {m} (rule : YesMetaZFC.Automation.ObjectHorn.Rule) (w row trace s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalQuantifiedApplicationIffSentence rule w row trace s)) := TheoryTransport.sentence (source_originalQuantifiedApplicationIff rule w row trace s)

theorem native_originalQuantifiedApplicationIff {m} (rule : YesMetaZFC.Automation.ObjectHorn.Rule) (w row trace s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalQuantifiedApplicationIffSentence rule w row trace s)) := ZFReplay.replay (originalQuantifiedApplicationIff_kernel_certificate rule w row trace s)

def wholeRuleTableBoundedSearchIffSentence {m} (rules : List YesMetaZFC.Automation.ObjectHorn.Rule) (w row trace s : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem row w).imp ((successor s row).imp (((HornStepSyntax.step rules w row trace).iff (HornSearchSyntax.boundedStep rules w row trace s)))))).close

theorem source_wholeRuleTableBoundedSearchIff {m} (rules : List YesMetaZFC.Automation.ObjectHorn.Rule) (w row trace s : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (wholeRuleTableBoundedSearchIffSentence rules w row trace s) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor s row) (Context.add (Formula.mem row w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (Formula.mem row w) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (successor s row) := .hyp (Or.inl rfl)
  exact HornSearchRules.step_iff_bounded hZ rules w row trace s h0 h1 h2

theorem wholeRuleTableBoundedSearchIff_kernel_certificate {m} (rules : List YesMetaZFC.Automation.ObjectHorn.Rule) (w row trace s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (wholeRuleTableBoundedSearchIffSentence rules w row trace s)) := TheoryTransport.sentence (source_wholeRuleTableBoundedSearchIff rules w row trace s)

theorem native_wholeRuleTableBoundedSearchIff {m} (rules : List YesMetaZFC.Automation.ObjectHorn.Rule) (w row trace s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (wholeRuleTableBoundedSearchIffSentence rules w row trace s)) := ZFReplay.replay (wholeRuleTableBoundedSearchIff_kernel_certificate rules w row trace s)

def wholeRuleTableActualSearchIffSentence {m} (rules : List YesMetaZFC.Automation.ObjectHorn.Rule) (w row trace : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem row w).imp (((HornStepSyntax.step rules w row trace).iff (HornSearchSyntax.searchStep rules w row trace))))).close

theorem source_wholeRuleTableActualSearchIff {m} (rules : List YesMetaZFC.Automation.ObjectHorn.Rule) (w row trace : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (wholeRuleTableActualSearchIffSentence rules w row trace) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem row w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (Formula.mem row w) := .hyp (Or.inl rfl)
  exact HornSearchRules.step_iff_search hZ rules w row trace h0 h1

theorem wholeRuleTableActualSearchIff_kernel_certificate {m} (rules : List YesMetaZFC.Automation.ObjectHorn.Rule) (w row trace : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (wholeRuleTableActualSearchIffSentence rules w row trace)) := TheoryTransport.sentence (source_wholeRuleTableActualSearchIff rules w row trace)

theorem native_wholeRuleTableActualSearchIff {m} (rules : List YesMetaZFC.Automation.ObjectHorn.Rule) (w row trace : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (wholeRuleTableActualSearchIffSentence rules w row trace)) := ZFReplay.replay (wholeRuleTableActualSearchIff_kernel_certificate rules w row trace)

def originalOtherRulesRejectedSentence {m} {k} (xs : Fin k → Fin m) (w row trace : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNodeSyntax.constructor k 0 w xs row).imp ((HornStepSyntax.step OriginalRuleTags.remaining w row trace).imp ((.bot))))).close

theorem source_originalOtherRulesRejected {m} {k} (xs : Fin k → Fin m) (w row trace : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalOtherRulesRejectedSentence xs w row trace) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornStepSyntax.step OriginalRuleTags.remaining w row trace) (Context.add (SyntaxNodeSyntax.constructor k 0 w xs row) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxNodeSyntax.constructor k 0 w xs row) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (HornStepSyntax.step OriginalRuleTags.remaining w row trace) := .hyp (Or.inl rfl)
  exact OriginalLookupDispatch.remaining_rejected hZ k w row trace xs h0 h1 h2

theorem originalOtherRulesRejected_kernel_certificate {m} {k} (xs : Fin k → Fin m) (w row trace : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalOtherRulesRejectedSentence xs w row trace)) := TheoryTransport.sentence (source_originalOtherRulesRejected xs w row trace)

theorem native_originalOtherRulesRejected {m} {k} (xs : Fin k → Fin m) (w row trace : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalOtherRulesRejectedSentence xs w row trace)) := ZFReplay.replay (originalOtherRulesRejected_kernel_certificate xs w row trace)

def originalWholeTableLookupDispatchIffSentence {m} {k} (xs : Fin k → Fin m) (w row trace : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNodeSyntax.constructor k 0 w xs row).imp (((HornStepSyntax.originalStep w row trace).iff (HornStepSyntax.lookupStep w row trace))))).close

theorem source_originalWholeTableLookupDispatchIff {m} {k} (xs : Fin k → Fin m) (w row trace : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalWholeTableLookupDispatchIffSentence xs w row trace) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNodeSyntax.constructor k 0 w xs row) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxNodeSyntax.constructor k 0 w xs row) := .hyp (Or.inl rfl)
  exact OriginalLookupDispatch.dispatch_iff hZ k w row trace xs h0 h1

theorem originalWholeTableLookupDispatchIff_kernel_certificate {m} {k} (xs : Fin k → Fin m) (w row trace : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalWholeTableLookupDispatchIffSentence xs w row trace)) := TheoryTransport.sentence (source_originalWholeTableLookupDispatchIff xs w row trace)

theorem native_originalWholeTableLookupDispatchIff {m} {k} (xs : Fin k → Fin m) (w row trace : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalWholeTableLookupDispatchIffSentence xs w row trace)) := ZFReplay.replay (originalWholeTableLookupDispatchIff_kernel_certificate xs w row trace)

def originalActualSearchLookupDispatchIffSentence {m} {k} (xs : Fin k → Fin m) (w row trace : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNodeSyntax.constructor k 0 w xs row).imp (((HornSearchSyntax.originalSearchStep w row trace).iff (HornStepSyntax.lookupStep w row trace))))).close

theorem source_originalActualSearchLookupDispatchIff {m} {k} (xs : Fin k → Fin m) (w row trace : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalActualSearchLookupDispatchIffSentence xs w row trace) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNodeSyntax.constructor k 0 w xs row) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxNodeSyntax.constructor k 0 w xs row) := .hyp (Or.inl rfl)
  exact HornSearchRules.original_search_iff_lookup hZ k w row trace xs h0 h1

theorem originalActualSearchLookupDispatchIff_kernel_certificate {m} {k} (xs : Fin k → Fin m) (w row trace : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalActualSearchLookupDispatchIffSentence xs w row trace)) := TheoryTransport.sentence (source_originalActualSearchLookupDispatchIff xs w row trace)

theorem native_originalActualSearchLookupDispatchIff {m} {k} (xs : Fin k → Fin m) (w row trace : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalActualSearchLookupDispatchIffSentence xs w row trace)) := ZFReplay.replay (originalActualSearchLookupDispatchIff_kernel_certificate xs w row trace)

def originalLookupIntoWholeTableSentence {m} (w row trace : Fin m) : Source.Sentence := ((HornStepSyntax.lookupStep w row trace).imp ((HornStepSyntax.originalStep w row trace))).close

theorem source_originalLookupIntoWholeTable {m} (w row trace : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalLookupIntoWholeTableSentence w row trace) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (HornStepSyntax.lookupStep w row trace) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (HornStepSyntax.lookupStep w row trace) := .hyp (Or.inl rfl)
  exact OriginalLookupDispatch.lookup_intro w row trace h0

theorem originalLookupIntoWholeTable_kernel_certificate {m} (w row trace : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalLookupIntoWholeTableSentence w row trace)) := TheoryTransport.sentence (source_originalLookupIntoWholeTable w row trace)

theorem native_originalLookupIntoWholeTable {m} (w row trace : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalLookupIntoWholeTableSentence w row trace)) := ZFReplay.replay (originalLookupIntoWholeTable_kernel_certificate w row trace)

end PPAC.Migration.Internal.ObjectBoundedLookupDispatch
