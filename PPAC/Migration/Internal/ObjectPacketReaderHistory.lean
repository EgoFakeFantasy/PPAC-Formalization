import PPAC.Migration.Internal.PacketReaderHistoryBase

/-! Actual raw state codes and coded transition are exact and deterministic. Independent internal history checks all adjacent steps and has a real singleton zero-step base. Arbitrary-length history construction, complete runs, EOF reverse, Basic AST, Proof and Con remain unproved -/
namespace PPAC.Migration.Internal.ObjectPacketReaderHistory
open Source SourceAlgebra SourceLogic OmegaSyntax

def packetReaderHistoryStateCodeExactRawDomainSentence {m} (w l v s a : Fin m) : Source.Sentence := ((omega w).imp (((PacketReaderStateSyntax.existsCode w l v s a).iff (PacketReaderStepSyntax.state w l v s a)))).close

theorem source_packetReaderHistoryStateCodeExactRawDomain {m} (w l v s a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderHistoryStateCodeExactRawDomainSentence w l v s a) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact PacketReaderStateCode.exists_iff hZ w l v s a h0

theorem packetReaderHistoryStateCodeExactRawDomain_kernel_certificate {m} (w l v s a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderHistoryStateCodeExactRawDomainSentence w l v s a)) := TheoryTransport.sentence (source_packetReaderHistoryStateCodeExactRawDomain w l v s a)

theorem native_packetReaderHistoryStateCodeExactRawDomain {m} (w l v s a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderHistoryStateCodeExactRawDomainSentence w l v s a)) := ZFReplay.replay (packetReaderHistoryStateCodeExactRawDomain_kernel_certificate w l v s a)

def packetReaderHistoryStateCodeOutputUniqueSentence {m} (w l v s a n r : Fin m) : Source.Sentence := ((omega w).imp ((PacketReaderStateSyntax.code w l v s a n).imp ((PacketReaderStateSyntax.code w l v s a r).imp ((Formula.equal n r))))).close

theorem source_packetReaderHistoryStateCodeOutputUnique {m} (w l v s a n r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderHistoryStateCodeOutputUniqueSentence w l v s a n r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderStateSyntax.code w l v s a r) (Context.add (PacketReaderStateSyntax.code w l v s a n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (PacketReaderStateSyntax.code w l v s a n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (PacketReaderStateSyntax.code w l v s a r) := .hyp (Or.inl rfl)
  exact PacketReaderStateCode.unique hZ w l v s a n r h0 h1 h2

theorem packetReaderHistoryStateCodeOutputUnique_kernel_certificate {m} (w l v s a n r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderHistoryStateCodeOutputUniqueSentence w l v s a n r)) := TheoryTransport.sentence (source_packetReaderHistoryStateCodeOutputUnique w l v s a n r)

theorem native_packetReaderHistoryStateCodeOutputUnique {m} (w l v s a n r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderHistoryStateCodeOutputUniqueSentence w l v s a n r)) := ZFReplay.replay (packetReaderHistoryStateCodeOutputUnique_kernel_certificate w l v s a n r)

def packetReaderHistoryStateCodeAllFieldsInjectiveSentence {m} (w l v s a x y q c n : Fin m) : Source.Sentence := ((omega w).imp ((PacketReaderStateSyntax.code w l v s a n).imp ((PacketReaderStateSyntax.code w x y q c n).imp ((PacketReaderStep.same l v s a x y q c))))).close

theorem source_packetReaderHistoryStateCodeAllFieldsInjective {m} (w l v s a x y q c n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderHistoryStateCodeAllFieldsInjectiveSentence w l v s a x y q c n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderStateSyntax.code w x y q c n) (Context.add (PacketReaderStateSyntax.code w l v s a n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (PacketReaderStateSyntax.code w l v s a n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (PacketReaderStateSyntax.code w x y q c n) := .hyp (Or.inl rfl)
  exact PacketReaderStateCode.fields_unique hZ w l v s a x y q c n h0 h1 h2

theorem packetReaderHistoryStateCodeAllFieldsInjective_kernel_certificate {m} (w l v s a x y q c n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderHistoryStateCodeAllFieldsInjectiveSentence w l v s a x y q c n)) := TheoryTransport.sentence (source_packetReaderHistoryStateCodeAllFieldsInjective w l v s a x y q c n)

theorem native_packetReaderHistoryStateCodeAllFieldsInjective {m} (w l v s a x y q c n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderHistoryStateCodeAllFieldsInjectiveSentence w l v s a x y q c n)) := ZFReplay.replay (packetReaderHistoryStateCodeAllFieldsInjective_kernel_certificate w l v s a x y q c n)

def packetReaderHistoryStateCodeNaturalSentence {m} (w l v s a n : Fin m) : Source.Sentence := ((omega w).imp ((PacketReaderStateSyntax.code w l v s a n).imp ((Formula.mem n w)))).close

theorem source_packetReaderHistoryStateCodeNatural {m} (w l v s a n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderHistoryStateCodeNaturalSentence w l v s a n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderStateSyntax.code w l v s a n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PacketReaderStateSyntax.code w l v s a n) := .hyp (Or.inl rfl)
  exact PacketReaderStateCode.range hZ w l v s a n h0 h1

theorem packetReaderHistoryStateCodeNatural_kernel_certificate {m} (w l v s a n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderHistoryStateCodeNaturalSentence w l v s a n)) := TheoryTransport.sentence (source_packetReaderHistoryStateCodeNatural w l v s a n)

theorem native_packetReaderHistoryStateCodeNatural {m} (w l v s a n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderHistoryStateCodeNaturalSentence w l v s a n)) := ZFReplay.replay (packetReaderHistoryStateCodeNatural_kernel_certificate w l v s a n)

def packetReaderHistoryCodedTransitionAtActualSourceSentence {m} (w B z o n r l v s a : Fin m) : Source.Sentence := ((omega w).imp ((PacketReaderStateSyntax.code w l v s a n).imp (((PacketReaderCodedSyntax.step w B z o n r).iff (PacketReaderCodedSyntax.nextAt w B z o l v s a r))))).close

theorem source_packetReaderHistoryCodedTransitionAtActualSource {m} (w B z o n r l v s a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderHistoryCodedTransitionAtActualSourceSentence w B z o n r l v s a) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderStateSyntax.code w l v s a n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PacketReaderStateSyntax.code w l v s a n) := .hyp (Or.inl rfl)
  exact PacketReaderCodedNormalize.at_source hZ w B z o n r l v s a h0 h1

theorem packetReaderHistoryCodedTransitionAtActualSource_kernel_certificate {m} (w B z o n r l v s a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderHistoryCodedTransitionAtActualSourceSentence w B z o n r l v s a)) := TheoryTransport.sentence (source_packetReaderHistoryCodedTransitionAtActualSource w B z o n r l v s a)

theorem native_packetReaderHistoryCodedTransitionAtActualSource {m} (w B z o n r l v s a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderHistoryCodedTransitionAtActualSourceSentence w B z o n r l v s a)) := ZFReplay.replay (packetReaderHistoryCodedTransitionAtActualSource_kernel_certificate w B z o n r l v s a)

def packetReaderHistoryCodedTransitionNaturalDomainSentence {m} (w B z o n r : Fin m) : Source.Sentence := ((omega w).imp ((PacketReaderCodedSyntax.step w B z o n r).imp (((Formula.mem n w).conj (.mem r w))))).close

theorem source_packetReaderHistoryCodedTransitionNaturalDomain {m} (w B z o n r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderHistoryCodedTransitionNaturalDomainSentence w B z o n r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderCodedSyntax.step w B z o n r) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PacketReaderCodedSyntax.step w B z o n r) := .hyp (Or.inl rfl)
  exact PacketReaderCodedNormalize.domain hZ w B z o n r h0 h1

theorem packetReaderHistoryCodedTransitionNaturalDomain_kernel_certificate {m} (w B z o n r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderHistoryCodedTransitionNaturalDomainSentence w B z o n r)) := TheoryTransport.sentence (source_packetReaderHistoryCodedTransitionNaturalDomain w B z o n r)

theorem native_packetReaderHistoryCodedTransitionNaturalDomain {m} (w B z o n r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderHistoryCodedTransitionNaturalDomainSentence w B z o n r)) := ZFReplay.replay (packetReaderHistoryCodedTransitionNaturalDomain_kernel_certificate w B z o n r)

def packetReaderHistoryCodedTransitionExactCarriersSentence {m} (w B z o n r : Fin m) : Source.Sentence := ((PacketReaderCodedSyntax.step w B z o n r).imp (((PacketReaderStateSyntax.carrier w n).conj (PacketReaderStateSyntax.carrier w r)))).close

theorem source_packetReaderHistoryCodedTransitionExactCarriers {m} (w B z o n r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderHistoryCodedTransitionExactCarriersSentence w B z o n r) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderCodedSyntax.step w B z o n r) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (PacketReaderCodedSyntax.step w B z o n r) := .hyp (Or.inl rfl)
  exact PacketReaderCodedNormalize.carriers w B z o n r h0

theorem packetReaderHistoryCodedTransitionExactCarriers_kernel_certificate {m} (w B z o n r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderHistoryCodedTransitionExactCarriersSentence w B z o n r)) := TheoryTransport.sentence (source_packetReaderHistoryCodedTransitionExactCarriers w B z o n r)

theorem native_packetReaderHistoryCodedTransitionExactCarriers {m} (w B z o n r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderHistoryCodedTransitionExactCarriersSentence w B z o n r)) := ZFReplay.replay (packetReaderHistoryCodedTransitionExactCarriers_kernel_certificate w B z o n r)

def packetReaderHistoryCodedTransitionOutputUniqueSentence {m} (w B z o n r t : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem B w).imp ((PacketReaderCodedSyntax.step w B z o n r).imp ((PacketReaderCodedSyntax.step w B z o n t).imp ((Formula.equal r t)))))).close

theorem source_packetReaderHistoryCodedTransitionOutputUnique {m} (w B z o n r t : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderHistoryCodedTransitionOutputUniqueSentence w B z o n r t) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderCodedSyntax.step w B z o n t) (Context.add (PacketReaderCodedSyntax.step w B z o n r) (Context.add (Formula.mem B w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (Formula.mem B w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (PacketReaderCodedSyntax.step w B z o n r) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (PacketReaderCodedSyntax.step w B z o n t) := .hyp (Or.inl rfl)
  exact PacketReaderCodedUnique.unique hZ w B z o n r t h0 h1 h2 h3

theorem packetReaderHistoryCodedTransitionOutputUnique_kernel_certificate {m} (w B z o n r t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderHistoryCodedTransitionOutputUniqueSentence w B z o n r t)) := TheoryTransport.sentence (source_packetReaderHistoryCodedTransitionOutputUnique w B z o n r t)

theorem native_packetReaderHistoryCodedTransitionOutputUnique {m} (w B z o n r t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderHistoryCodedTransitionOutputUniqueSentence w B z o n r t)) := ZFReplay.replay (packetReaderHistoryCodedTransitionOutputUnique_kernel_certificate w B z o n r t)

def packetReaderHistoryCodedSuccessorExactRawDomainSentence {m} (w B z o n l v s a : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem B w).imp ((Formula.mem z w).imp ((Formula.mem o w).imp ((PacketReaderStateSyntax.code w l v s a n).imp (((PacketReaderCodedSyntax.existsNext w B z o n).iff (PacketReaderInputExistence.admissible w B z o l v s a)))))))).close

theorem source_packetReaderHistoryCodedSuccessorExactRawDomain {m} (w B z o n l v s a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderHistoryCodedSuccessorExactRawDomainSentence w B z o n l v s a) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderStateSyntax.code w l v s a n) (Context.add (Formula.mem o w) (Context.add (Formula.mem z w) (Context.add (Formula.mem B w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (Formula.mem B w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (Formula.mem z w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (Formula.mem o w) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (PacketReaderStateSyntax.code w l v s a n) := .hyp (Or.inl rfl)
  exact PacketReaderCodedExistence.exists_iff hZ w B z o n l v s a h0 h1 h2 h3 h4

theorem packetReaderHistoryCodedSuccessorExactRawDomain_kernel_certificate {m} (w B z o n l v s a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderHistoryCodedSuccessorExactRawDomainSentence w B z o n l v s a)) := TheoryTransport.sentence (source_packetReaderHistoryCodedSuccessorExactRawDomain w B z o n l v s a)

theorem native_packetReaderHistoryCodedSuccessorExactRawDomain {m} (w B z o n l v s a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderHistoryCodedSuccessorExactRawDomainSentence w B z o n l v s a)) := ZFReplay.replay (packetReaderHistoryCodedSuccessorExactRawDomain_kernel_certificate w B z o n l v s a)

def packetReaderHistoryActualInternalIndexHasAdjacentStepSentence {m} (w B z o n r l d f i : Fin m) : Source.Sentence := ((PacketReaderHistorySyntax.history w B z o n r l d f).imp ((Formula.mem i l).imp ((PacketReaderHistorySyntax.row w B z o f i)))).close

theorem source_packetReaderHistoryActualInternalIndexHasAdjacentStep {m} (w B z o n r l d f i : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderHistoryActualInternalIndexHasAdjacentStepSentence w B z o n r l d f i) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem i l) (Context.add (PacketReaderHistorySyntax.history w B z o n r l d f) (Source.SetLanguage.ZF.at m))
  have h0 : Derives Δ (PacketReaderHistorySyntax.history w B z o n r l d f) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (Formula.mem i l) := .hyp (Or.inl rfl)
  exact PacketReaderHistoryLaws.row_at w B z o n r l d f i h0 h1

theorem packetReaderHistoryActualInternalIndexHasAdjacentStep_kernel_certificate {m} (w B z o n r l d f i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderHistoryActualInternalIndexHasAdjacentStepSentence w B z o n r l d f i)) := TheoryTransport.sentence (source_packetReaderHistoryActualInternalIndexHasAdjacentStep w B z o n r l d f i)

theorem native_packetReaderHistoryActualInternalIndexHasAdjacentStep {m} (w B z o n r l d f i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderHistoryActualInternalIndexHasAdjacentStepSentence w B z o n r l d f i)) := ZFReplay.replay (packetReaderHistoryActualInternalIndexHasAdjacentStep_kernel_certificate w B z o n r l d f i)

def packetReaderHistoryActualHistoryEndpointsNaturalSentence {m} (w B z o n r l d f : Fin m) : Source.Sentence := ((PacketReaderHistorySyntax.history w B z o n r l d f).imp (((Formula.mem n w).conj (.mem r w)))).close

theorem source_packetReaderHistoryActualHistoryEndpointsNatural {m} (w B z o n r l d f : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderHistoryActualHistoryEndpointsNaturalSentence w B z o n r l d f) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderHistorySyntax.history w B z o n r l d f) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (PacketReaderHistorySyntax.history w B z o n r l d f) := .hyp (Or.inl rfl)
  exact PacketReaderHistoryLaws.endpoint_range w B z o n r l d f h0

theorem packetReaderHistoryActualHistoryEndpointsNatural_kernel_certificate {m} (w B z o n r l d f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderHistoryActualHistoryEndpointsNaturalSentence w B z o n r l d f)) := TheoryTransport.sentence (source_packetReaderHistoryActualHistoryEndpointsNatural w B z o n r l d f)

theorem native_packetReaderHistoryActualHistoryEndpointsNatural {m} (w B z o n r l d f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderHistoryActualHistoryEndpointsNaturalSentence w B z o n r l d f)) := ZFReplay.replay (packetReaderHistoryActualHistoryEndpointsNatural_kernel_certificate w B z o n r l d f)

def packetReaderHistoryEveryZeroHistoryHasSameEndpointSentence {m} (w B z o n r l d f : Fin m) : Source.Sentence := ((PacketReaderHistorySyntax.history w B z o n r l d f).imp ((empty l).imp ((Formula.equal n r)))).close

theorem source_packetReaderHistoryEveryZeroHistoryHasSameEndpoint {m} (w B z o n r l d f : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderHistoryEveryZeroHistoryHasSameEndpointSentence w B z o n r l d f) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (empty l) (Context.add (PacketReaderHistorySyntax.history w B z o n r l d f) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (PacketReaderHistorySyntax.history w B z o n r l d f) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (empty l) := .hyp (Or.inl rfl)
  exact PacketReaderHistoryLaws.zero_value hZ w B z o n r l d f h0 h1

theorem packetReaderHistoryEveryZeroHistoryHasSameEndpoint_kernel_certificate {m} (w B z o n r l d f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderHistoryEveryZeroHistoryHasSameEndpointSentence w B z o n r l d f)) := TheoryTransport.sentence (source_packetReaderHistoryEveryZeroHistoryHasSameEndpoint w B z o n r l d f)

theorem native_packetReaderHistoryEveryZeroHistoryHasSameEndpoint {m} (w B z o n r l d f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderHistoryEveryZeroHistoryHasSameEndpointSentence w B z o n r l d f)) := ZFReplay.replay (packetReaderHistoryEveryZeroHistoryHasSameEndpoint_kernel_certificate w B z o n r l d f)

def packetReaderHistoryActualSingletonZeroHistoryExistsSentence {m} (w B z o n d : Fin m) : Source.Sentence := ((omega w).imp ((empty z).imp ((successor d z).imp ((Formula.mem n w).imp ((PacketReaderStateSyntax.carrier w n).imp ((PacketReaderHistorySyntax.existsHistory w B z o n n z d))))))).close

theorem source_packetReaderHistoryActualSingletonZeroHistoryExists {m} (w B z o n d : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderHistoryActualSingletonZeroHistoryExistsSentence w B z o n d) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderStateSyntax.carrier w n) (Context.add (Formula.mem n w) (Context.add (successor d z) (Context.add (empty z) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (empty z) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (successor d z) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (Formula.mem n w) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (PacketReaderStateSyntax.carrier w n) := .hyp (Or.inl rfl)
  exact PacketReaderHistoryBase.exists_zero hZ w B z o n d h0 h1 h2 h3 h4

theorem packetReaderHistoryActualSingletonZeroHistoryExists_kernel_certificate {m} (w B z o n d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderHistoryActualSingletonZeroHistoryExistsSentence w B z o n d)) := TheoryTransport.sentence (source_packetReaderHistoryActualSingletonZeroHistoryExists w B z o n d)

theorem native_packetReaderHistoryActualSingletonZeroHistoryExists {m} (w B z o n d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderHistoryActualSingletonZeroHistoryExistsSentence w B z o n d)) := ZFReplay.replay (packetReaderHistoryActualSingletonZeroHistoryExists_kernel_certificate w B z o n d)

def packetReaderHistoryActualStateCodeSeedsZeroHistorySentence {m} (w B z o n d l v s a : Fin m) : Source.Sentence := ((omega w).imp ((empty z).imp ((successor d z).imp ((PacketReaderStateSyntax.code w l v s a n).imp ((PacketReaderHistorySyntax.existsHistory w B z o n n z d)))))).close

theorem source_packetReaderHistoryActualStateCodeSeedsZeroHistory {m} (w B z o n d l v s a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderHistoryActualStateCodeSeedsZeroHistorySentence w B z o n d l v s a) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderStateSyntax.code w l v s a n) (Context.add (successor d z) (Context.add (empty z) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (empty z) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (successor d z) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (PacketReaderStateSyntax.code w l v s a n) := .hyp (Or.inl rfl)
  exact PacketReaderHistoryBase.exists_zero hZ w B z o n d h0 h1 h2 (PacketReaderStateCode.range hZ w l v s a n h0 h3) (PacketReaderStateSyntax.intro_carrier w l v s a n h3)

theorem packetReaderHistoryActualStateCodeSeedsZeroHistory_kernel_certificate {m} (w B z o n d l v s a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderHistoryActualStateCodeSeedsZeroHistorySentence w B z o n d l v s a)) := TheoryTransport.sentence (source_packetReaderHistoryActualStateCodeSeedsZeroHistory w B z o n d l v s a)

theorem native_packetReaderHistoryActualStateCodeSeedsZeroHistory {m} (w B z o n d l v s a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderHistoryActualStateCodeSeedsZeroHistorySentence w B z o n d l v s a)) := ZFReplay.replay (packetReaderHistoryActualStateCodeSeedsZeroHistory_kernel_certificate w B z o n d l v s a)

def packetReaderHistoryOriginalLiteralCodedDomainSentence {m} (w B z o n l v s a : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 128 B).imp ((SyntaxNumeralSyntax.numeral 0 z).imp ((SyntaxNumeralSyntax.numeral 1 o).imp ((PacketReaderStateSyntax.code w l v s a n).imp (((PacketReaderCodedSyntax.existsNext w B z o n).iff (PacketReaderInputExistence.admissible w B z o l v s a)))))))).close

theorem source_packetReaderHistoryOriginalLiteralCodedDomain {m} (w B z o n l v s a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderHistoryOriginalLiteralCodedDomainSentence w B z o n l v s a) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderStateSyntax.code w l v s a n) (Context.add (SyntaxNumeralSyntax.numeral 1 o) (Context.add (SyntaxNumeralSyntax.numeral 0 z) (Context.add (SyntaxNumeralSyntax.numeral 128 B) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 128 B) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral 0 z) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (SyntaxNumeralSyntax.numeral 1 o) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (PacketReaderStateSyntax.code w l v s a n) := .hyp (Or.inl rfl)
  exact PacketReaderCodedExistence.exists_iff hZ w B z o n l v s a h0 (SyntaxNumerals.range hZ 128 w B h0 h1) (SyntaxNumerals.range hZ 0 w z h0 h2) (SyntaxNumerals.range hZ 1 w o h0 h3) h4

theorem packetReaderHistoryOriginalLiteralCodedDomain_kernel_certificate {m} (w B z o n l v s a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderHistoryOriginalLiteralCodedDomainSentence w B z o n l v s a)) := TheoryTransport.sentence (source_packetReaderHistoryOriginalLiteralCodedDomain w B z o n l v s a)

theorem native_packetReaderHistoryOriginalLiteralCodedDomain {m} (w B z o n l v s a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderHistoryOriginalLiteralCodedDomainSentence w B z o n l v s a)) := ZFReplay.replay (packetReaderHistoryOriginalLiteralCodedDomain_kernel_certificate w B z o n l v s a)

end PPAC.Migration.Internal.ObjectPacketReaderHistory
