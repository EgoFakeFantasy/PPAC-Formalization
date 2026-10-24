import PPAC.Migration.Internal.ProjectCompilerBase

/-! Actual Project compiler recursion, parent certificates and base executions; full source correctness remains unproved in the original nativeZF kernel; complete schema tests and Con remain unproved. -/
namespace PPAC.Migration.Internal.ObjectProjectCompiler
open Source SourceAlgebra SourceLogic OmegaSyntax

def compilerStateExistsSentence {m} (w c n h : Fin m) : Source.Sentence := ((ProjectCompilerStateSyntax.existsState w c n h)).close

theorem source_compilerStateExists {m} (w c n h : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (compilerStateExistsSentence w c n h) := by
  apply close_derives
  let Δ : Context m := Source.SetLanguage.ZF.at m
  have hZ : ZFContext.Evidence Δ := by
    exact ZFContext.source_ZF m
  exact ProjectCompilerStateExistence.exists_state hZ w c n h

theorem compilerStateExists_kernel_certificate {m} (w c n h : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (compilerStateExistsSentence w c n h)) := TheoryTransport.sentence (source_compilerStateExists w c n h)

theorem native_compilerStateExists {m} (w c n h : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (compilerStateExistsSentence w c n h)) := ZFReplay.replay (compilerStateExists_kernel_certificate w c n h)

def compilerStateUniqueFiberSentence {m} (w c n h : Fin m) : Source.Sentence := ((ProjectCompilerStateSyntax.fiber w c n h)).close

theorem source_compilerStateUniqueFiber {m} (w c n h : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (compilerStateUniqueFiberSentence w c n h) := by
  apply close_derives
  let Δ : Context m := Source.SetLanguage.ZF.at m
  have hZ : ZFContext.Evidence Δ := by
    exact ZFContext.source_ZF m
  exact ProjectCompilerStateExistence.actual_fiber hZ w c n h

theorem compilerStateUniqueFiber_kernel_certificate {m} (w c n h : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (compilerStateUniqueFiberSentence w c n h)) := TheoryTransport.sentence (source_compilerStateUniqueFiber w c n h)

theorem native_compilerStateUniqueFiber {m} (w c n h : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (compilerStateUniqueFiberSentence w c n h)) := ZFReplay.replay (compilerStateUniqueFiber_kernel_certificate w c n h)

def compilerStateEdgesIffSentence {m} (w a c n h v b q : Fin m) : Source.Sentence := ((PowerSetSyntax.powerOf a w).imp ((PowerSetSyntax.powerOf c a).imp ((ProjectCompilerStateSyntax.state w c n h v).imp (((GraphSyntax.edge v b q).iff (ProjectCompilerLocalSyntax.localStep w b q h n)))))).close

theorem source_compilerStateEdgesIff {m} (w a c n h v b q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (compilerStateEdgesIffSentence w a c n h v b q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ProjectCompilerStateSyntax.state w c n h v) (Context.add (PowerSetSyntax.powerOf c a) (Context.add (PowerSetSyntax.powerOf a w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (PowerSetSyntax.powerOf a w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (PowerSetSyntax.powerOf c a) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (ProjectCompilerStateSyntax.state w c n h v) := .hyp (Or.inl rfl)
  exact ProjectCompilerStateMembership.edge_iff hZ w a c n h v b q h0 h1 h2

theorem compilerStateEdgesIff_kernel_certificate {m} (w a c n h v b q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (compilerStateEdgesIffSentence w a c n h v b q)) := TheoryTransport.sentence (source_compilerStateEdgesIff w a c n h v b q)

theorem native_compilerStateEdgesIff {m} (w a c n h v b q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (compilerStateEdgesIffSentence w a c n h v b q)) := ZFReplay.replay (compilerStateEdgesIff_kernel_certificate w a c n h v b q)

def compilerAllRecursorsSentence {m} (w c : Fin m) : Source.Sentence := ((ProjectCompilerRecursionSyntax.recursors w c)).close

theorem source_compilerAllRecursors {m} (w c : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (compilerAllRecursorsSentence w c) := by
  apply close_derives
  let Δ : Context m := Source.SetLanguage.ZF.at m
  have hZ : ZFContext.Evidence Δ := by
    exact ZFContext.source_ZF m
  exact ProjectCompilerRecursors.all_unique hZ w c

theorem compilerAllRecursors_kernel_certificate {m} (w c : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (compilerAllRecursorsSentence w c)) := TheoryTransport.sentence (source_compilerAllRecursors w c)

theorem native_compilerAllRecursors {m} (w c : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (compilerAllRecursorsSentence w c)) := ZFReplay.replay (compilerAllRecursors_kernel_certificate w c)

def compilerActualCarrierRecursorsSentence {m} (w : Fin m) : Source.Sentence := ((ProjectCompilerRecursionSyntax.actualRecursors w)).close

theorem source_compilerActualCarrierRecursors {m} (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (compilerActualCarrierRecursorsSentence w) := by
  apply close_derives
  let Δ : Context m := Source.SetLanguage.ZF.at m
  have hZ : ZFContext.Evidence Δ := by
    exact ZFContext.source_ZF m
  exact ProjectCompilerRecursors.actual_carrier_recursors hZ w

theorem compilerActualCarrierRecursors_kernel_certificate {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (compilerActualCarrierRecursorsSentence w)) := TheoryTransport.sentence (source_compilerActualCarrierRecursors w)

theorem native_compilerActualCarrierRecursors {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (compilerActualCarrierRecursorsSentence w)) := ZFReplay.replay (compilerActualCarrierRecursors_kernel_certificate w)

def compilerNaturalEvaluationExistsSentence {m} (w c n : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem n w).imp ((ProjectCompilerEvaluationSyntax.existsValue w c n)))).close

theorem source_compilerNaturalEvaluationExists {m} (w c n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (compilerNaturalEvaluationExistsSentence w c n) := by
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
  exact ProjectCompilerEvaluationExistence.at_natural hZ w c n h0 h1

theorem compilerNaturalEvaluationExists_kernel_certificate {m} (w c n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (compilerNaturalEvaluationExistsSentence w c n)) := TheoryTransport.sentence (source_compilerNaturalEvaluationExists w c n)

theorem native_compilerNaturalEvaluationExists {m} (w c n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (compilerNaturalEvaluationExistsSentence w c n)) := ZFReplay.replay (compilerNaturalEvaluationExists_kernel_certificate w c n)

def compilerEvaluationStateUniqueSentence {m} (w c n y u : Fin m) : Source.Sentence := ((OrdinalSyntax.ordinal n).imp ((ProjectCompilerEvaluationSyntax.evaluation w c n y).imp ((ProjectCompilerEvaluationSyntax.evaluation w c n u).imp ((Formula.equal y u))))).close

theorem source_compilerEvaluationStateUnique {m} (w c n y u : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (compilerEvaluationStateUniqueSentence w c n y u) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ProjectCompilerEvaluationSyntax.evaluation w c n u) (Context.add (ProjectCompilerEvaluationSyntax.evaluation w c n y) (Context.add (OrdinalSyntax.ordinal n) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (OrdinalSyntax.ordinal n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (ProjectCompilerEvaluationSyntax.evaluation w c n y) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (ProjectCompilerEvaluationSyntax.evaluation w c n u) := .hyp (Or.inl rfl)
  exact ProjectCompilerEvaluationUnique.unique hZ w c n y u h0 h1 h2

theorem compilerEvaluationStateUnique_kernel_certificate {m} (w c n y u : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (compilerEvaluationStateUniqueSentence w c n y u)) := TheoryTransport.sentence (source_compilerEvaluationStateUnique w c n y u)

theorem native_compilerEvaluationStateUnique {m} (w c n y u : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (compilerEvaluationStateUniqueSentence w c n y u)) := ZFReplay.replay (compilerEvaluationStateUnique_kernel_certificate w c n y u)

def compilerProducedOutputRootCertificateSentence {m} (w n b q : Fin m) : Source.Sentence := ((omega w).imp ((ProjectCompilerCodeSyntax.compiled w n b q).imp ((ProjectCompilerRootSyntax.certificate w n b q)))).close

theorem source_compilerProducedOutputRootCertificate {m} (w n b q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (compilerProducedOutputRootCertificateSentence w n b q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ProjectCompilerCodeSyntax.compiled w n b q) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (ProjectCompilerCodeSyntax.compiled w n b q) := .hyp (Or.inl rfl)
  exact ProjectCompilerRoot.certificate_of_compiled hZ w n b q h0 h1

theorem compilerProducedOutputRootCertificate_kernel_certificate {m} (w n b q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (compilerProducedOutputRootCertificateSentence w n b q)) := TheoryTransport.sentence (source_compilerProducedOutputRootCertificate w n b q)

theorem native_compilerProducedOutputRootCertificate {m} (w n b q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (compilerProducedOutputRootCertificateSentence w n b q)) := ZFReplay.replay (compilerProducedOutputRootCertificate_kernel_certificate w n b q)

def compilerCarrierExistsSentence {m} (w : Fin m) : Source.Sentence := ((ProjectCompilerCodeSyntax.existsCarrier w)).close

theorem source_compilerCarrierExists {m} (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (compilerCarrierExistsSentence w) := by
  apply close_derives
  let Δ : Context m := Source.SetLanguage.ZF.at m
  have hZ : ZFContext.Evidence Δ := by
    exact ZFContext.source_ZF m
  exact ProjectCompilerCodeCarrier.exists_carrier hZ w

theorem compilerCarrierExists_kernel_certificate {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (compilerCarrierExistsSentence w)) := TheoryTransport.sentence (source_compilerCarrierExists w)

theorem native_compilerCarrierExists {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (compilerCarrierExistsSentence w)) := ZFReplay.replay (compilerCarrierExists_kernel_certificate w)

def compilerAtActualCarrierIffSentence {m} (w a c n b q : Fin m) : Source.Sentence := ((ProjectCompilerCodeSyntax.carrier w a c).imp (((ProjectCompilerCodeSyntax.compiled w n b q).iff (ProjectCompilerJudgmentSyntax.atCarrier w c n b q)))).close

theorem source_compilerAtActualCarrierIff {m} (w a c n b q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (compilerAtActualCarrierIffSentence w a c n b q) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (ProjectCompilerCodeSyntax.carrier w a c) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (ProjectCompilerCodeSyntax.carrier w a c) := .hyp (Or.inl rfl)
  exact ProjectCompilerCodeCarrier.code_iff_atCarrier hZ w a c n b q h0

theorem compilerAtActualCarrierIff_kernel_certificate {m} (w a c n b q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (compilerAtActualCarrierIffSentence w a c n b q)) := TheoryTransport.sentence (source_compilerAtActualCarrierIff w a c n b q)

theorem native_compilerAtActualCarrierIff {m} (w a c n b q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (compilerAtActualCarrierIffSentence w a c n b q)) := ZFReplay.replay (compilerAtActualCarrierIff_kernel_certificate w a c n b q)

def compilerNaturalGuardsSentence {m} (w n b q : Fin m) : Source.Sentence := ((ProjectCompilerCodeSyntax.compiled w n b q).imp (((Formula.mem n w).conj (SyntaxTermSyntax.contexts w b q)))).close

theorem source_compilerNaturalGuards {m} (w n b q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (compilerNaturalGuardsSentence w n b q) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (ProjectCompilerCodeSyntax.compiled w n b q) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (ProjectCompilerCodeSyntax.compiled w n b q) := .hyp (Or.inl rfl)
  exact ProjectCompilerCodeProperties.guards w n b q h0

theorem compilerNaturalGuards_kernel_certificate {m} (w n b q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (compilerNaturalGuardsSentence w n b q)) := TheoryTransport.sentence (source_compilerNaturalGuards w n b q)

theorem native_compilerNaturalGuards {m} (w n b q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (compilerNaturalGuardsSentence w n b q)) := ZFReplay.replay (compilerNaturalGuards_kernel_certificate w n b q)

def compilerNonNaturalInputRejectedSentence {m} (w n b q : Fin m) : Source.Sentence := (((Formula.mem n w).neg).imp (((ProjectCompilerCodeSyntax.compiled w n b q).neg))).close

theorem source_compilerNonNaturalInputRejected {m} (w n b q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (compilerNonNaturalInputRejectedSentence w n b q) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add ((Formula.mem n w).neg) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ ((Formula.mem n w).neg) := .hyp (Or.inl rfl)
  exact ProjectCompilerCodeProperties.reject_code w n b q h0

theorem compilerNonNaturalInputRejected_kernel_certificate {m} (w n b q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (compilerNonNaturalInputRejectedSentence w n b q)) := TheoryTransport.sentence (source_compilerNonNaturalInputRejected w n b q)

theorem native_compilerNonNaturalInputRejected {m} (w n b q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (compilerNonNaturalInputRejectedSentence w n b q)) := ZFReplay.replay (compilerNonNaturalInputRejected_kernel_certificate w n b q)

def compilerInvalidCoordinatesRejectedSentence {m} (w n b q : Fin m) : Source.Sentence := (((SyntaxTermSyntax.contexts w b q).neg).imp (((ProjectCompilerCodeSyntax.compiled w n b q).neg))).close

theorem source_compilerInvalidCoordinatesRejected {m} (w n b q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (compilerInvalidCoordinatesRejectedSentence w n b q) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add ((SyntaxTermSyntax.contexts w b q).neg) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ ((SyntaxTermSyntax.contexts w b q).neg) := .hyp (Or.inl rfl)
  exact ProjectCompilerCodeProperties.reject_context w n b q h0

theorem compilerInvalidCoordinatesRejected_kernel_certificate {m} (w n b q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (compilerInvalidCoordinatesRejectedSentence w n b q)) := TheoryTransport.sentence (source_compilerInvalidCoordinatesRejected w n b q)

theorem native_compilerInvalidCoordinatesRejected {m} (w n b q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (compilerInvalidCoordinatesRejectedSentence w n b q)) := ZFReplay.replay (compilerInvalidCoordinatesRejected_kernel_certificate w n b q)

def compilerOmegaIndependentSentence {m} (w v n b q : Fin m) : Source.Sentence := ((omega w).imp ((omega v).imp (((ProjectCompilerCodeSyntax.compiled w n b q).iff (ProjectCompilerCodeSyntax.compiled v n b q))))).close

theorem source_compilerOmegaIndependent {m} (w v n b q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (compilerOmegaIndependentSentence w v n b q) := by
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
  exact ProjectCompilerCodeProperties.omega_independent hZ w v n b q h0 h1

theorem compilerOmegaIndependent_kernel_certificate {m} (w v n b q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (compilerOmegaIndependentSentence w v n b q)) := TheoryTransport.sentence (source_compilerOmegaIndependent w v n b q)

theorem native_compilerOmegaIndependent {m} (w v n b q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (compilerOmegaIndependentSentence w v n b q)) := ZFReplay.replay (compilerOmegaIndependent_kernel_certificate w v n b q)

def compilerConstantsActuallyProducedSentence {m} (truth : Bool) (w n b : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem b w).imp ((SyntaxNodeSyntax.constructor 0 (SyntaxAtomSyntax.nullaryTag truth) w Fin.elim0 n).imp ((ProjectCompilerCodeSyntax.compiled w n b n))))).close

theorem source_compilerConstantsActuallyProduced {m} (truth : Bool) (w n b : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (compilerConstantsActuallyProducedSentence truth w n b) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNodeSyntax.constructor 0 (SyntaxAtomSyntax.nullaryTag truth) w Fin.elim0 n) (Context.add (Formula.mem b w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (Formula.mem b w) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxNodeSyntax.constructor 0 (SyntaxAtomSyntax.nullaryTag truth) w Fin.elim0 n) := .hyp (Or.inl rfl)
  exact ProjectCompilerBase.constant_compiled hZ truth w n b h0 h1 h2

theorem compilerConstantsActuallyProduced_kernel_certificate {m} (truth : Bool) (w n b : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (compilerConstantsActuallyProducedSentence truth w n b)) := TheoryTransport.sentence (source_compilerConstantsActuallyProduced truth w n b)

theorem native_compilerConstantsActuallyProduced {m} (truth : Bool) (w n b : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (compilerConstantsActuallyProducedSentence truth w n b)) := ZFReplay.replay (compilerConstantsActuallyProduced_kernel_certificate truth w n b)

def compilerThreeAtomsActuallyProducedSentence {m} (kind : Fin 3) (w b z x y n q : Fin m) : Source.Sentence := ((omega w).imp ((empty z).imp ((ProjectAtomicSyntax.compiled kind w b z x y n q).imp ((ProjectCompilerCodeSyntax.compiled w n b q))))).close

theorem source_compilerThreeAtomsActuallyProduced {m} (kind : Fin 3) (w b z x y n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (compilerThreeAtomsActuallyProducedSentence kind w b z x y n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ProjectAtomicSyntax.compiled kind w b z x y n q) (Context.add (empty z) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (empty z) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (ProjectAtomicSyntax.compiled kind w b z x y n q) := .hyp (Or.inl rfl)
  exact ProjectCompilerBase.atomic_compiled hZ kind w b z x y n q h0 h1 h2

theorem compilerThreeAtomsActuallyProduced_kernel_certificate {m} (kind : Fin 3) (w b z x y n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (compilerThreeAtomsActuallyProducedSentence kind w b z x y n q)) := TheoryTransport.sentence (source_compilerThreeAtomsActuallyProduced kind w b z x y n q)

theorem native_compilerThreeAtomsActuallyProduced {m} (kind : Fin 3) (w b z x y n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (compilerThreeAtomsActuallyProducedSentence kind w b z x y n q)) := ZFReplay.replay (compilerThreeAtomsActuallyProduced_kernel_certificate kind w b z x y n q)

def compilerThreeAtomsTypedOutputExistsSentence {m} (kind : Fin 3) (w b z x y n : Fin m) : Source.Sentence := ((omega w).imp ((empty z).imp ((ProjectAtomicSyntax.sourceAt kind w b x y n).imp ((ProjectCompilerBase.existsTyped w n b z))))).close

theorem source_compilerThreeAtomsTypedOutputExists {m} (kind : Fin 3) (w b z x y n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (compilerThreeAtomsTypedOutputExistsSentence kind w b z x y n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ProjectAtomicSyntax.sourceAt kind w b x y n) (Context.add (empty z) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (empty z) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (ProjectAtomicSyntax.sourceAt kind w b x y n) := .hyp (Or.inl rfl)
  exact ProjectCompilerBase.atomic_exists_typed hZ kind w b z x y n h0 h1 h2

theorem compilerThreeAtomsTypedOutputExists_kernel_certificate {m} (kind : Fin 3) (w b z x y n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (compilerThreeAtomsTypedOutputExistsSentence kind w b z x y n)) := TheoryTransport.sentence (source_compilerThreeAtomsTypedOutputExists kind w b z x y n)

theorem native_compilerThreeAtomsTypedOutputExists {m} (kind : Fin 3) (w b z x y n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (compilerThreeAtomsTypedOutputExistsSentence kind w b z x y n)) := ZFReplay.replay (compilerThreeAtomsTypedOutputExists_kernel_certificate kind w b z x y n)

def compilerHistoryIndependentActualOutputSentence {m} (w n b q : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem n w).imp ((ProjectCompilerIndependent.allHistories w n b q).imp ((ProjectCompilerCodeSyntax.compiled w n b q))))).close

theorem source_compilerHistoryIndependentActualOutput {m} (w n b q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (compilerHistoryIndependentActualOutputSentence w n b q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ProjectCompilerIndependent.allHistories w n b q) (Context.add (Formula.mem n w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (Formula.mem n w) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (ProjectCompilerIndependent.allHistories w n b q) := .hyp (Or.inl rfl)
  exact ProjectCompilerIndependent.compiled hZ w n b q h0 h1 h2

theorem compilerHistoryIndependentActualOutput_kernel_certificate {m} (w n b q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (compilerHistoryIndependentActualOutputSentence w n b q)) := TheoryTransport.sentence (source_compilerHistoryIndependentActualOutput w n b q)

theorem native_compilerHistoryIndependentActualOutput {m} (w n b q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (compilerHistoryIndependentActualOutputSentence w n b q)) := ZFReplay.replay (compilerHistoryIndependentActualOutput_kernel_certificate w n b q)

def compilerEvaluationStateUniqueFiberSentence {m} (w c n : Fin m) : Source.Sentence := ((OrdinalSyntax.ordinal n).imp ((ProjectCompilerEvaluationSyntax.fiber w c n))).close

theorem source_compilerEvaluationStateUniqueFiber {m} (w c n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (compilerEvaluationStateUniqueFiberSentence w c n) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (OrdinalSyntax.ordinal n) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (OrdinalSyntax.ordinal n) := .hyp (Or.inl rfl)
  exact ProjectCompilerEvaluationUnique.exists_unique hZ w c n h0

theorem compilerEvaluationStateUniqueFiber_kernel_certificate {m} (w c n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (compilerEvaluationStateUniqueFiberSentence w c n)) := TheoryTransport.sentence (source_compilerEvaluationStateUniqueFiber w c n)

theorem native_compilerEvaluationStateUniqueFiber {m} (w c n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (compilerEvaluationStateUniqueFiberSentence w c n)) := ZFReplay.replay (compilerEvaluationStateUniqueFiber_kernel_certificate w c n)

def compilerActualHistoryFromValueSentence {m} (w c n v : Fin m) : Source.Sentence := ((OrdinalSyntax.ordinal n).imp ((ProjectCompilerEvaluationSyntax.evaluation w c n v).imp ((ProjectCompilerHistory.stepHistory w c n v)))).close

theorem source_compilerActualHistoryFromValue {m} (w c n v : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (compilerActualHistoryFromValueSentence w c n v) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ProjectCompilerEvaluationSyntax.evaluation w c n v) (Context.add (OrdinalSyntax.ordinal n) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (OrdinalSyntax.ordinal n) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (ProjectCompilerEvaluationSyntax.evaluation w c n v) := .hyp (Or.inl rfl)
  exact ProjectCompilerHistory.from_value hZ w c n v h0 h1

theorem compilerActualHistoryFromValue_kernel_certificate {m} (w c n v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (compilerActualHistoryFromValueSentence w c n v)) := TheoryTransport.sentence (source_compilerActualHistoryFromValue w c n v)

theorem native_compilerActualHistoryFromValue {m} (w c n v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (compilerActualHistoryFromValueSentence w c n v)) := ZFReplay.replay (compilerActualHistoryFromValue_kernel_certificate w c n v)

end PPAC.Migration.Internal.ObjectProjectCompiler
