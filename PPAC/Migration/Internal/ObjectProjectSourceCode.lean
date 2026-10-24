import PPAC.Migration.Internal.ProjectSourceCodeRecursive

/-! Independent twelve-constructor Project source grammar and its all-internal recursive equation in the original nativeZF kernel; complete schema tests and Con remain unproved. -/
namespace PPAC.Migration.Internal.ObjectProjectSourceCode
open Source SourceAlgebra SourceLogic OmegaSyntax

def projectSourceStateExistsSentence {m} (w c n h : Fin m) : Source.Sentence := ((ProjectSourceTypeStateSyntax.existsState w c n h)).close

theorem source_projectSourceStateExists {m} (w c n h : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (projectSourceStateExistsSentence w c n h) := by
  apply close_derives
  let Δ : Context m := Source.SetLanguage.ZF.at m
  have hZ : ZFContext.Evidence Δ := by
    exact ZFContext.source_ZF m
  exact ProjectSourceTypeStateExistence.exists_state hZ w c n h

theorem projectSourceStateExists_kernel_certificate {m} (w c n h : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (projectSourceStateExistsSentence w c n h)) := TheoryTransport.sentence (source_projectSourceStateExists w c n h)

theorem native_projectSourceStateExists {m} (w c n h : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (projectSourceStateExistsSentence w c n h)) := ZFReplay.replay (projectSourceStateExists_kernel_certificate w c n h)

def projectSourceStateUniqueFiberSentence {m} (w c n h : Fin m) : Source.Sentence := ((ProjectSourceTypeStateSyntax.fiber w c n h)).close

theorem source_projectSourceStateUniqueFiber {m} (w c n h : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (projectSourceStateUniqueFiberSentence w c n h) := by
  apply close_derives
  let Δ : Context m := Source.SetLanguage.ZF.at m
  have hZ : ZFContext.Evidence Δ := by
    exact ZFContext.source_ZF m
  exact ProjectSourceTypeStateExistence.actual_fiber hZ w c n h

theorem projectSourceStateUniqueFiber_kernel_certificate {m} (w c n h : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (projectSourceStateUniqueFiberSentence w c n h)) := TheoryTransport.sentence (source_projectSourceStateUniqueFiber w c n h)

theorem native_projectSourceStateUniqueFiber {m} (w c n h : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (projectSourceStateUniqueFiberSentence w c n h)) := ZFReplay.replay (projectSourceStateUniqueFiber_kernel_certificate w c n h)

def projectSourceStateEdgesIffSentence {m} (w a c n h v b f : Fin m) : Source.Sentence := ((PowerSetSyntax.powerOf a w).imp ((PowerSetSyntax.powerOf c a).imp ((ProjectSourceTypeStateSyntax.state w c n h v).imp (((GraphSyntax.edge v b f).iff (ProjectSourceLocalSyntax.localType w b f h n)))))).close

theorem source_projectSourceStateEdgesIff {m} (w a c n h v b f : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (projectSourceStateEdgesIffSentence w a c n h v b f) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ProjectSourceTypeStateSyntax.state w c n h v) (Context.add (PowerSetSyntax.powerOf c a) (Context.add (PowerSetSyntax.powerOf a w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (PowerSetSyntax.powerOf a w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (PowerSetSyntax.powerOf c a) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (ProjectSourceTypeStateSyntax.state w c n h v) := .hyp (Or.inl rfl)
  exact ProjectSourceTypeStateMembership.edge_iff hZ w a c n h v b f h0 h1 h2

theorem projectSourceStateEdgesIff_kernel_certificate {m} (w a c n h v b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (projectSourceStateEdgesIffSentence w a c n h v b f)) := TheoryTransport.sentence (source_projectSourceStateEdgesIff w a c n h v b f)

theorem native_projectSourceStateEdgesIff {m} (w a c n h v b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (projectSourceStateEdgesIffSentence w a c n h v b f)) := ZFReplay.replay (projectSourceStateEdgesIff_kernel_certificate w a c n h v b f)

def projectSourceRecursorsSentence {m} (w c : Fin m) : Source.Sentence := ((ProjectSourceTypeRecursionSyntax.recursors w c)).close

theorem source_projectSourceRecursors {m} (w c : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (projectSourceRecursorsSentence w c) := by
  apply close_derives
  let Δ : Context m := Source.SetLanguage.ZF.at m
  have hZ : ZFContext.Evidence Δ := by
    exact ZFContext.source_ZF m
  exact ProjectSourceTypeRecursors.all_unique hZ w c

theorem projectSourceRecursors_kernel_certificate {m} (w c : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (projectSourceRecursorsSentence w c)) := TheoryTransport.sentence (source_projectSourceRecursors w c)

theorem native_projectSourceRecursors {m} (w c : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (projectSourceRecursorsSentence w c)) := ZFReplay.replay (projectSourceRecursors_kernel_certificate w c)

def projectSourceActualCarrierRecursorsSentence {m} (w : Fin m) : Source.Sentence := ((ProjectSourceTypeRecursionSyntax.actualRecursors w)).close

theorem source_projectSourceActualCarrierRecursors {m} (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (projectSourceActualCarrierRecursorsSentence w) := by
  apply close_derives
  let Δ : Context m := Source.SetLanguage.ZF.at m
  have hZ : ZFContext.Evidence Δ := by
    exact ZFContext.source_ZF m
  exact ProjectSourceTypeRecursors.actual_carrier_recursors hZ w

theorem projectSourceActualCarrierRecursors_kernel_certificate {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (projectSourceActualCarrierRecursorsSentence w)) := TheoryTransport.sentence (source_projectSourceActualCarrierRecursors w)

theorem native_projectSourceActualCarrierRecursors {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (projectSourceActualCarrierRecursorsSentence w)) := ZFReplay.replay (projectSourceActualCarrierRecursors_kernel_certificate w)

def projectSourceNaturalEvaluationExistsSentence {m} (w c n : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem n w).imp ((ProjectSourceTypeEvaluationSyntax.existsValue w c n)))).close

theorem source_projectSourceNaturalEvaluationExists {m} (w c n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (projectSourceNaturalEvaluationExistsSentence w c n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem n w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (Formula.mem n w) := .hyp (Or.inl rfl)
  exact ProjectSourceTypeEvaluationExistence.at_natural hZ w c n h0 h1

theorem projectSourceNaturalEvaluationExists_kernel_certificate {m} (w c n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (projectSourceNaturalEvaluationExistsSentence w c n)) := TheoryTransport.sentence (source_projectSourceNaturalEvaluationExists w c n)

theorem native_projectSourceNaturalEvaluationExists {m} (w c n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (projectSourceNaturalEvaluationExistsSentence w c n)) := ZFReplay.replay (projectSourceNaturalEvaluationExists_kernel_certificate w c n)

def projectSourceEvaluationUniqueFiberSentence {m} (w c n : Fin m) : Source.Sentence := ((OrdinalSyntax.ordinal n).imp ((ProjectSourceTypeEvaluationSyntax.fiber w c n))).close

theorem source_projectSourceEvaluationUniqueFiber {m} (w c n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (projectSourceEvaluationUniqueFiberSentence w c n) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (OrdinalSyntax.ordinal n) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (OrdinalSyntax.ordinal n) := .hyp (Or.inl rfl)
  exact ProjectSourceTypeEvaluationUnique.exists_unique hZ w c n h0

theorem projectSourceEvaluationUniqueFiber_kernel_certificate {m} (w c n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (projectSourceEvaluationUniqueFiberSentence w c n)) := TheoryTransport.sentence (source_projectSourceEvaluationUniqueFiber w c n)

theorem native_projectSourceEvaluationUniqueFiber {m} (w c n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (projectSourceEvaluationUniqueFiberSentence w c n)) := ZFReplay.replay (projectSourceEvaluationUniqueFiber_kernel_certificate w c n)

def projectSourceTypedRecursiveIffSentence {m} (w a c n b f : Fin m) : Source.Sentence := ((omega w).imp ((PowerSetSyntax.powerOf a w).imp ((PowerSetSyntax.powerOf c a).imp (((ProjectSourceTypeJudgmentSyntax.typed w c n b f).iff (ProjectSourceTypeRecursiveSyntax.criterion w c n b f)))))).close

theorem source_projectSourceTypedRecursiveIff {m} (w a c n b f : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (projectSourceTypedRecursiveIffSentence w a c n b f) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PowerSetSyntax.powerOf c a) (Context.add (PowerSetSyntax.powerOf a w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (PowerSetSyntax.powerOf a w) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (PowerSetSyntax.powerOf c a) := .hyp (Or.inl rfl)
  exact ProjectSourceTypeRecursive.recursive_iff hZ w a c n b f h0 h1 h2

theorem projectSourceTypedRecursiveIff_kernel_certificate {m} (w a c n b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (projectSourceTypedRecursiveIffSentence w a c n b f)) := TheoryTransport.sentence (source_projectSourceTypedRecursiveIff w a c n b f)

theorem native_projectSourceTypedRecursiveIff {m} (w a c n b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (projectSourceTypedRecursiveIffSentence w a c n b f)) := ZFReplay.replay (projectSourceTypedRecursiveIff_kernel_certificate w a c n b f)

def projectSourceCodeCarrierExistsSentence {m} (w : Fin m) : Source.Sentence := ((ProjectSourceCodeSyntax.existsCarrier w)).close

theorem source_projectSourceCodeCarrierExists {m} (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (projectSourceCodeCarrierExistsSentence w) := by
  apply close_derives
  let Δ : Context m := Source.SetLanguage.ZF.at m
  have hZ : ZFContext.Evidence Δ := by
    exact ZFContext.source_ZF m
  exact ProjectSourceCodeCarrier.exists_carrier hZ w

theorem projectSourceCodeCarrierExists_kernel_certificate {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (projectSourceCodeCarrierExistsSentence w)) := TheoryTransport.sentence (source_projectSourceCodeCarrierExists w)

theorem native_projectSourceCodeCarrierExists {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (projectSourceCodeCarrierExistsSentence w)) := ZFReplay.replay (projectSourceCodeCarrierExists_kernel_certificate w)

def projectSourceCodeAtCarrierIffSentence {m} (w a c n b f : Fin m) : Source.Sentence := ((ProjectSourceCodeSyntax.carrier w a c).imp (((ProjectSourceCodeSyntax.sourceCode w n b f).iff (ProjectSourceTypeJudgmentSyntax.typed w c n b f)))).close

theorem source_projectSourceCodeAtCarrierIff {m} (w a c n b f : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (projectSourceCodeAtCarrierIffSentence w a c n b f) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (ProjectSourceCodeSyntax.carrier w a c) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (ProjectSourceCodeSyntax.carrier w a c) := .hyp (Or.inl rfl)
  exact ProjectSourceCodeCarrier.code_iff_typed hZ w a c n b f h0

theorem projectSourceCodeAtCarrierIff_kernel_certificate {m} (w a c n b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (projectSourceCodeAtCarrierIffSentence w a c n b f)) := TheoryTransport.sentence (source_projectSourceCodeAtCarrierIff w a c n b f)

theorem native_projectSourceCodeAtCarrierIff {m} (w a c n b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (projectSourceCodeAtCarrierIffSentence w a c n b f)) := ZFReplay.replay (projectSourceCodeAtCarrierIff_kernel_certificate w a c n b f)

def projectSourceCodeGuardsSentence {m} (w n b f : Fin m) : Source.Sentence := ((ProjectSourceCodeSyntax.sourceCode w n b f).imp (((Formula.mem n w).conj (SyntaxTermSyntax.contexts w b f)))).close

theorem source_projectSourceCodeGuards {m} (w n b f : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (projectSourceCodeGuardsSentence w n b f) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (ProjectSourceCodeSyntax.sourceCode w n b f) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (ProjectSourceCodeSyntax.sourceCode w n b f) := .hyp (Or.inl rfl)
  exact ProjectSourceCodeProperties.guards w n b f h0

theorem projectSourceCodeGuards_kernel_certificate {m} (w n b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (projectSourceCodeGuardsSentence w n b f)) := TheoryTransport.sentence (source_projectSourceCodeGuards w n b f)

theorem native_projectSourceCodeGuards {m} (w n b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (projectSourceCodeGuardsSentence w n b f)) := ZFReplay.replay (projectSourceCodeGuards_kernel_certificate w n b f)

def projectSourceNonNaturalCodeRejectedSentence {m} (w n b f : Fin m) : Source.Sentence := (((Formula.mem n w).neg).imp (((ProjectSourceCodeSyntax.sourceCode w n b f).neg))).close

theorem source_projectSourceNonNaturalCodeRejected {m} (w n b f : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (projectSourceNonNaturalCodeRejectedSentence w n b f) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add ((Formula.mem n w).neg) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ ((Formula.mem n w).neg) := .hyp (Or.inl rfl)
  exact ProjectSourceCodeProperties.reject_code w n b f h0

theorem projectSourceNonNaturalCodeRejected_kernel_certificate {m} (w n b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (projectSourceNonNaturalCodeRejectedSentence w n b f)) := TheoryTransport.sentence (source_projectSourceNonNaturalCodeRejected w n b f)

theorem native_projectSourceNonNaturalCodeRejected {m} (w n b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (projectSourceNonNaturalCodeRejectedSentence w n b f)) := ZFReplay.replay (projectSourceNonNaturalCodeRejected_kernel_certificate w n b f)

def projectSourceInvalidContextRejectedSentence {m} (w n b f : Fin m) : Source.Sentence := (((SyntaxTermSyntax.contexts w b f).neg).imp (((ProjectSourceCodeSyntax.sourceCode w n b f).neg))).close

theorem source_projectSourceInvalidContextRejected {m} (w n b f : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (projectSourceInvalidContextRejectedSentence w n b f) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add ((SyntaxTermSyntax.contexts w b f).neg) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ ((SyntaxTermSyntax.contexts w b f).neg) := .hyp (Or.inl rfl)
  exact ProjectSourceCodeProperties.reject_context w n b f h0

theorem projectSourceInvalidContextRejected_kernel_certificate {m} (w n b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (projectSourceInvalidContextRejectedSentence w n b f)) := TheoryTransport.sentence (source_projectSourceInvalidContextRejected w n b f)

theorem native_projectSourceInvalidContextRejected {m} (w n b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (projectSourceInvalidContextRejectedSentence w n b f)) := ZFReplay.replay (projectSourceInvalidContextRejected_kernel_certificate w n b f)

def projectSourceCodeOmegaIndependentSentence {m} (w v n b f : Fin m) : Source.Sentence := ((omega w).imp ((omega v).imp (((ProjectSourceCodeSyntax.sourceCode w n b f).iff (ProjectSourceCodeSyntax.sourceCode v n b f))))).close

theorem source_projectSourceCodeOmegaIndependent {m} (w v n b f : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (projectSourceCodeOmegaIndependentSentence w v n b f) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (omega v) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (omega v) := .hyp (Or.inl rfl)
  exact ProjectSourceCodeProperties.omega_independent hZ w v n b f h0 h1

theorem projectSourceCodeOmegaIndependent_kernel_certificate {m} (w v n b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (projectSourceCodeOmegaIndependentSentence w v n b f)) := TheoryTransport.sentence (source_projectSourceCodeOmegaIndependent w v n b f)

theorem native_projectSourceCodeOmegaIndependent {m} (w v n b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (projectSourceCodeOmegaIndependentSentence w v n b f)) := ZFReplay.replay (projectSourceCodeOmegaIndependent_kernel_certificate w v n b f)

def projectSourceCodeRecursiveIffSentence {m} (w n b f : Fin m) : Source.Sentence := ((omega w).imp (((ProjectSourceCodeSyntax.sourceCode w n b f).iff (ProjectSourceCodeRecursiveSyntax.criterion w n b f)))).close

theorem source_projectSourceCodeRecursiveIff {m} (w n b f : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (projectSourceCodeRecursiveIffSentence w n b f) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact ProjectSourceCodeRecursive.recursive_iff hZ w n b f h0

theorem projectSourceCodeRecursiveIff_kernel_certificate {m} (w n b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (projectSourceCodeRecursiveIffSentence w n b f)) := TheoryTransport.sentence (source_projectSourceCodeRecursiveIff w n b f)

theorem native_projectSourceCodeRecursiveIff {m} (w n b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (projectSourceCodeRecursiveIffSentence w n b f)) := ZFReplay.replay (projectSourceCodeRecursiveIff_kernel_certificate w n b f)

def projectSourceAllInternalRecursiveLawSentence {m} (w : Fin m) : Source.Sentence := ((omega w).imp ((ProjectSourceCodeRecursive.universalLaw w))).close

theorem source_projectSourceAllInternalRecursiveLaw {m} (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (projectSourceAllInternalRecursiveLawSentence w) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact ProjectSourceCodeRecursive.all_law hZ w h0

theorem projectSourceAllInternalRecursiveLaw_kernel_certificate {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (projectSourceAllInternalRecursiveLawSentence w)) := TheoryTransport.sentence (source_projectSourceAllInternalRecursiveLaw w)

theorem native_projectSourceAllInternalRecursiveLaw {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (projectSourceAllInternalRecursiveLawSentence w)) := ZFReplay.replay (projectSourceAllInternalRecursiveLaw_kernel_certificate w)

end PPAC.Migration.Internal.ObjectProjectSourceCode
