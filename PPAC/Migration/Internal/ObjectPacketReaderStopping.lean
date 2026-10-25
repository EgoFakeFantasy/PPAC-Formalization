import PPAC.Migration.Internal.PacketReaderStoppingContract

/-! Original internal progress and length bound construct a real complete stopped history. Endpoint, length, domain and graph are jointly unique in object ALL4/EX4. EOF reverse, full reader bridge, Basic AST, Proof and Con remain unproved -/
namespace PPAC.Migration.Internal.ObjectPacketReaderStopping
open Source SourceAlgebra SourceLogic OmegaSyntax

def packetReaderStoppingActualSourceCarrierNaturalSentence {m} (w n : Fin m) : Source.Sentence := ((omega w).imp ((PacketReaderStateSyntax.carrier w n).imp ((Formula.mem n w)))).close

theorem source_packetReaderStoppingActualSourceCarrierNatural {m} (w n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderStoppingActualSourceCarrierNaturalSentence w n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderStateSyntax.carrier w n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PacketReaderStateSyntax.carrier w n) := .hyp (Or.inl rfl)
  exact PacketReaderStoppingInitial.carrier_natural hZ w n h0 h1

theorem packetReaderStoppingActualSourceCarrierNatural_kernel_certificate {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderStoppingActualSourceCarrierNaturalSentence w n)) := TheoryTransport.sentence (source_packetReaderStoppingActualSourceCarrierNatural w n)

theorem native_packetReaderStoppingActualSourceCarrierNatural {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderStoppingActualSourceCarrierNaturalSentence w n)) := ZFReplay.replay (packetReaderStoppingActualSourceCarrierNatural_kernel_certificate w n)

def packetReaderStoppingActualZeroPrefixSentence {m} (w B z o n : Fin m) : Source.Sentence := ((omega w).imp ((empty z).imp ((PacketReaderStateSyntax.carrier w n).imp ((PacketReaderStoppingSyntax.prefixAt w B z o n z))))).close

theorem source_packetReaderStoppingActualZeroPrefix {m} (w B z o n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderStoppingActualZeroPrefixSentence w B z o n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderStateSyntax.carrier w n) (Context.add (empty z) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (empty z) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (PacketReaderStateSyntax.carrier w n) := .hyp (Or.inl rfl)
  exact PacketReaderStoppingInitial.zero_prefix hZ w B z o n h0 h1 h2

theorem packetReaderStoppingActualZeroPrefix_kernel_certificate {m} (w B z o n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderStoppingActualZeroPrefixSentence w B z o n)) := TheoryTransport.sentence (source_packetReaderStoppingActualZeroPrefix w B z o n)

theorem native_packetReaderStoppingActualZeroPrefix {m} (w B z o n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderStoppingActualZeroPrefixSentence w B z o n)) := ZFReplay.replay (packetReaderStoppingActualZeroPrefix_kernel_certificate w B z o n)

def packetReaderStoppingActualHistoryStopsOrExtendsSentence {m} (w B z o n r i d f j : Fin m) : Source.Sentence := ((omega w).imp ((PacketReaderHistorySyntax.history w B z o n r i d f).imp ((successor j i).imp ((PacketReaderStoppingSyntax.progress w B z o n j))))).close

theorem source_packetReaderStoppingActualHistoryStopsOrExtends {m} (w B z o n r i d f j : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderStoppingActualHistoryStopsOrExtendsSentence w B z o n r i d f j) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor j i) (Context.add (PacketReaderHistorySyntax.history w B z o n r i d f) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (PacketReaderHistorySyntax.history w B z o n r i d f) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (successor j i) := .hyp (Or.inl rfl)
  exact PacketReaderStoppingAdvance.from_history hZ w B z o n r i d f j h0 h1 h2

theorem packetReaderStoppingActualHistoryStopsOrExtends_kernel_certificate {m} (w B z o n r i d f j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderStoppingActualHistoryStopsOrExtendsSentence w B z o n r i d f j)) := TheoryTransport.sentence (source_packetReaderStoppingActualHistoryStopsOrExtends w B z o n r i d f j)

theorem native_packetReaderStoppingActualHistoryStopsOrExtends {m} (w B z o n r i d f j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderStoppingActualHistoryStopsOrExtendsSentence w B z o n r i d f j)) := ZFReplay.replay (packetReaderStoppingActualHistoryStopsOrExtends_kernel_certificate w B z o n r i d f j)

def packetReaderStoppingInternalSuccessorProgressSentence {m} (w B z o n i j : Fin m) : Source.Sentence := ((omega w).imp ((PacketReaderStoppingSyntax.progress w B z o n i).imp ((successor j i).imp ((PacketReaderStoppingSyntax.progress w B z o n j))))).close

theorem source_packetReaderStoppingInternalSuccessorProgress {m} (w B z o n i j : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderStoppingInternalSuccessorProgressSentence w B z o n i j) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor j i) (Context.add (PacketReaderStoppingSyntax.progress w B z o n i) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (PacketReaderStoppingSyntax.progress w B z o n i) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (successor j i) := .hyp (Or.inl rfl)
  exact PacketReaderStoppingAdvance.successor_point hZ w B z o n i j h0 h1 h2

theorem packetReaderStoppingInternalSuccessorProgress_kernel_certificate {m} (w B z o n i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderStoppingInternalSuccessorProgressSentence w B z o n i j)) := TheoryTransport.sentence (source_packetReaderStoppingInternalSuccessorProgress w B z o n i j)

theorem native_packetReaderStoppingInternalSuccessorProgress {m} (w B z o n i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderStoppingInternalSuccessorProgressSentence w B z o n i j)) := ZFReplay.replay (packetReaderStoppingInternalSuccessorProgress_kernel_certificate w B z o n i j)

def packetReaderStoppingAllInternalProgressSentence {m} (w B z o n : Fin m) : Source.Sentence := ((omega w).imp ((empty z).imp ((PacketReaderStateSyntax.carrier w n).imp ((PacketReaderStoppingSyntax.allProgress w B z o n))))).close

theorem source_packetReaderStoppingAllInternalProgress {m} (w B z o n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderStoppingAllInternalProgressSentence w B z o n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderStateSyntax.carrier w n) (Context.add (empty z) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (empty z) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (PacketReaderStateSyntax.carrier w n) := .hyp (Or.inl rfl)
  exact PacketReaderStoppingInduction.all_progress hZ w B z o n h0 h1 h2

theorem packetReaderStoppingAllInternalProgress_kernel_certificate {m} (w B z o n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderStoppingAllInternalProgressSentence w B z o n)) := TheoryTransport.sentence (source_packetReaderStoppingAllInternalProgress w B z o n)

theorem native_packetReaderStoppingAllInternalProgress {m} (w B z o n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderStoppingAllInternalProgressSentence w B z o n)) := ZFReplay.replay (packetReaderStoppingAllInternalProgress_kernel_certificate w B z o n)

def packetReaderStoppingTooLongActualPrefixImpossibleSentence {m} (w B z o n L N j : Fin m) : Source.Sentence := ((omega w).imp ((PacketReaderConsumptionSyntax.input w n L).imp ((StructuralListLengthSyntax.hasLength w L N).imp ((successor j N).imp ((PacketReaderStoppingSyntax.prefixAt w B z o n j).imp ((Formula.bot))))))).close

theorem source_packetReaderStoppingTooLongActualPrefixImpossible {m} (w B z o n L N j : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderStoppingTooLongActualPrefixImpossibleSentence w B z o n L N j) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderStoppingSyntax.prefixAt w B z o n j) (Context.add (successor j N) (Context.add (StructuralListLengthSyntax.hasLength w L N) (Context.add (PacketReaderConsumptionSyntax.input w n L) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (PacketReaderConsumptionSyntax.input w n L) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (StructuralListLengthSyntax.hasLength w L N) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (successor j N) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (PacketReaderStoppingSyntax.prefixAt w B z o n j) := .hyp (Or.inl rfl)
  exact PacketReaderStoppingExistence.exclude_prefix hZ w B z o n L N j h0 h1 h2 h3 h4

theorem packetReaderStoppingTooLongActualPrefixImpossible_kernel_certificate {m} (w B z o n L N j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderStoppingTooLongActualPrefixImpossibleSentence w B z o n L N j)) := TheoryTransport.sentence (source_packetReaderStoppingTooLongActualPrefixImpossible w B z o n L N j)

theorem native_packetReaderStoppingTooLongActualPrefixImpossible {m} (w B z o n L N j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderStoppingTooLongActualPrefixImpossibleSentence w B z o n L N j)) := ZFReplay.replay (packetReaderStoppingTooLongActualPrefixImpossible_kernel_certificate w B z o n L N j)

def packetReaderStoppingFromInitialActualLengthExistsCompleteSentence {m} (w B z o n L N : Fin m) : Source.Sentence := ((omega w).imp ((empty z).imp ((PacketReaderStateSyntax.carrier w n).imp ((PacketReaderConsumptionSyntax.input w n L).imp ((StructuralListLengthSyntax.hasLength w L N).imp ((PacketReaderStoppingSyntax.complete w B z o n))))))).close

theorem source_packetReaderStoppingFromInitialActualLengthExistsComplete {m} (w B z o n L N : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderStoppingFromInitialActualLengthExistsCompleteSentence w B z o n L N) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralListLengthSyntax.hasLength w L N) (Context.add (PacketReaderConsumptionSyntax.input w n L) (Context.add (PacketReaderStateSyntax.carrier w n) (Context.add (empty z) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (empty z) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (PacketReaderStateSyntax.carrier w n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (PacketReaderConsumptionSyntax.input w n L) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (StructuralListLengthSyntax.hasLength w L N) := .hyp (Or.inl rfl)
  exact PacketReaderStoppingExistence.from_length hZ w B z o n L N h0 h1 h2 h3 h4

theorem packetReaderStoppingFromInitialActualLengthExistsComplete_kernel_certificate {m} (w B z o n L N : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderStoppingFromInitialActualLengthExistsCompleteSentence w B z o n L N)) := TheoryTransport.sentence (source_packetReaderStoppingFromInitialActualLengthExistsComplete w B z o n L N)

theorem native_packetReaderStoppingFromInitialActualLengthExistsComplete {m} (w B z o n L N : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderStoppingFromInitialActualLengthExistsCompleteSentence w B z o n L N)) := ZFReplay.replay (packetReaderStoppingFromInitialActualLengthExistsComplete_kernel_certificate w B z o n L N)

def packetReaderStoppingFromActualSourceCodeExistsCompleteSentence {m} (w B z o n L v s a : Fin m) : Source.Sentence := ((omega w).imp ((empty z).imp ((PacketReaderStateSyntax.code w L v s a n).imp ((PacketReaderStoppingSyntax.complete w B z o n))))).close

theorem source_packetReaderStoppingFromActualSourceCodeExistsComplete {m} (w B z o n L v s a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderStoppingFromActualSourceCodeExistsCompleteSentence w B z o n L v s a) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderStateSyntax.code w L v s a n) (Context.add (empty z) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (empty z) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (PacketReaderStateSyntax.code w L v s a n) := .hyp (Or.inl rfl)
  exact PacketReaderStoppingExistence.from_actual_code hZ w B z o n L v s a h0 h1 h2

theorem packetReaderStoppingFromActualSourceCodeExistsComplete_kernel_certificate {m} (w B z o n L v s a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderStoppingFromActualSourceCodeExistsCompleteSentence w B z o n L v s a)) := TheoryTransport.sentence (source_packetReaderStoppingFromActualSourceCodeExistsComplete w B z o n L v s a)

theorem native_packetReaderStoppingFromActualSourceCodeExistsComplete {m} (w B z o n L v s a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderStoppingFromActualSourceCodeExistsCompleteSentence w B z o n L v s a)) := ZFReplay.replay (packetReaderStoppingFromActualSourceCodeExistsComplete_kernel_certificate w B z o n L v s a)

def packetReaderStoppingEveryActualCarrierHasCompleteHistorySentence {m} (w B z o n : Fin m) : Source.Sentence := ((omega w).imp ((empty z).imp ((PacketReaderStateSyntax.carrier w n).imp ((PacketReaderStoppingSyntax.complete w B z o n))))).close

theorem source_packetReaderStoppingEveryActualCarrierHasCompleteHistory {m} (w B z o n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderStoppingEveryActualCarrierHasCompleteHistorySentence w B z o n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderStateSyntax.carrier w n) (Context.add (empty z) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (empty z) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (PacketReaderStateSyntax.carrier w n) := .hyp (Or.inl rfl)
  exact PacketReaderStoppingExistence.exists_complete hZ w B z o n h0 h1 h2

theorem packetReaderStoppingEveryActualCarrierHasCompleteHistory_kernel_certificate {m} (w B z o n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderStoppingEveryActualCarrierHasCompleteHistorySentence w B z o n)) := TheoryTransport.sentence (source_packetReaderStoppingEveryActualCarrierHasCompleteHistory w B z o n)

theorem native_packetReaderStoppingEveryActualCarrierHasCompleteHistory {m} (w B z o n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderStoppingEveryActualCarrierHasCompleteHistorySentence w B z o n)) := ZFReplay.replay (packetReaderStoppingEveryActualCarrierHasCompleteHistory_kernel_certificate w B z o n)

def packetReaderStoppingStoppedHistoryCannotBeStrictlyShorterSentence {m} (w B z o n r t l d k e f g : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem B w).imp ((PacketReaderStoppingSyntax.halted w B z o n r l d f).imp ((PacketReaderHistorySyntax.history w B z o n t k e g).imp ((Formula.mem l k).imp ((Formula.bot))))))).close

theorem source_packetReaderStoppingStoppedHistoryCannotBeStrictlyShorter {m} (w B z o n r t l d k e f g : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderStoppingStoppedHistoryCannotBeStrictlyShorterSentence w B z o n r t l d k e f g) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem l k) (Context.add (PacketReaderHistorySyntax.history w B z o n t k e g) (Context.add (PacketReaderStoppingSyntax.halted w B z o n r l d f) (Context.add (Formula.mem B w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (Formula.mem B w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (PacketReaderStoppingSyntax.halted w B z o n r l d f) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (PacketReaderHistorySyntax.history w B z o n t k e g) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (Formula.mem l k) := .hyp (Or.inl rfl)
  exact PacketReaderStoppingUnique.no_longer_history hZ w B z o n r t l d k e f g h0 h1 h2 h3 h4

theorem packetReaderStoppingStoppedHistoryCannotBeStrictlyShorter_kernel_certificate {m} (w B z o n r t l d k e f g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderStoppingStoppedHistoryCannotBeStrictlyShorterSentence w B z o n r t l d k e f g)) := TheoryTransport.sentence (source_packetReaderStoppingStoppedHistoryCannotBeStrictlyShorter w B z o n r t l d k e f g)

theorem native_packetReaderStoppingStoppedHistoryCannotBeStrictlyShorter {m} (w B z o n r t l d k e f g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderStoppingStoppedHistoryCannotBeStrictlyShorterSentence w B z o n r t l d k e f g)) := ZFReplay.replay (packetReaderStoppingStoppedHistoryCannotBeStrictlyShorter_kernel_certificate w B z o n r t l d k e f g)

def packetReaderStoppingStoppedLengthUniqueSentence {m} (w B z o n r t l d k e f g : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem B w).imp ((PacketReaderStoppingSyntax.halted w B z o n r l d f).imp ((PacketReaderStoppingSyntax.halted w B z o n t k e g).imp ((Formula.equal l k)))))).close

theorem source_packetReaderStoppingStoppedLengthUnique {m} (w B z o n r t l d k e f g : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderStoppingStoppedLengthUniqueSentence w B z o n r t l d k e f g) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderStoppingSyntax.halted w B z o n t k e g) (Context.add (PacketReaderStoppingSyntax.halted w B z o n r l d f) (Context.add (Formula.mem B w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (Formula.mem B w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (PacketReaderStoppingSyntax.halted w B z o n r l d f) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (PacketReaderStoppingSyntax.halted w B z o n t k e g) := .hyp (Or.inl rfl)
  exact PacketReaderStoppingUnique.lengths hZ w B z o n r t l d k e f g h0 h1 h2 h3

theorem packetReaderStoppingStoppedLengthUnique_kernel_certificate {m} (w B z o n r t l d k e f g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderStoppingStoppedLengthUniqueSentence w B z o n r t l d k e f g)) := TheoryTransport.sentence (source_packetReaderStoppingStoppedLengthUnique w B z o n r t l d k e f g)

theorem native_packetReaderStoppingStoppedLengthUnique {m} (w B z o n r t l d k e f g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderStoppingStoppedLengthUniqueSentence w B z o n r t l d k e f g)) := ZFReplay.replay (packetReaderStoppingStoppedLengthUnique_kernel_certificate w B z o n r t l d k e f g)

def packetReaderStoppingStoppedEndpointUniqueSentence {m} (w B z o n r t l d k e f g : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem B w).imp ((PacketReaderStoppingSyntax.halted w B z o n r l d f).imp ((PacketReaderStoppingSyntax.halted w B z o n t k e g).imp ((Formula.equal r t)))))).close

theorem source_packetReaderStoppingStoppedEndpointUnique {m} (w B z o n r t l d k e f g : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderStoppingStoppedEndpointUniqueSentence w B z o n r t l d k e f g) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderStoppingSyntax.halted w B z o n t k e g) (Context.add (PacketReaderStoppingSyntax.halted w B z o n r l d f) (Context.add (Formula.mem B w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (Formula.mem B w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (PacketReaderStoppingSyntax.halted w B z o n r l d f) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (PacketReaderStoppingSyntax.halted w B z o n t k e g) := .hyp (Or.inl rfl)
  exact PacketReaderStoppingUnique.endpoints hZ w B z o n r t l d k e f g h0 h1 h2 h3

theorem packetReaderStoppingStoppedEndpointUnique_kernel_certificate {m} (w B z o n r t l d k e f g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderStoppingStoppedEndpointUniqueSentence w B z o n r t l d k e f g)) := TheoryTransport.sentence (source_packetReaderStoppingStoppedEndpointUnique w B z o n r t l d k e f g)

theorem native_packetReaderStoppingStoppedEndpointUnique {m} (w B z o n r t l d k e f g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderStoppingStoppedEndpointUniqueSentence w B z o n r t l d k e f g)) := ZFReplay.replay (packetReaderStoppingStoppedEndpointUnique_kernel_certificate w B z o n r t l d k e f g)

def packetReaderStoppingStoppedDomainUniqueSentence {m} (w B z o n r t l d k e f g : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem B w).imp ((PacketReaderStoppingSyntax.halted w B z o n r l d f).imp ((PacketReaderStoppingSyntax.halted w B z o n t k e g).imp ((Formula.equal d e)))))).close

theorem source_packetReaderStoppingStoppedDomainUnique {m} (w B z o n r t l d k e f g : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderStoppingStoppedDomainUniqueSentence w B z o n r t l d k e f g) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderStoppingSyntax.halted w B z o n t k e g) (Context.add (PacketReaderStoppingSyntax.halted w B z o n r l d f) (Context.add (Formula.mem B w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (Formula.mem B w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (PacketReaderStoppingSyntax.halted w B z o n r l d f) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (PacketReaderStoppingSyntax.halted w B z o n t k e g) := .hyp (Or.inl rfl)
  exact PacketReaderStoppingUnique.domains hZ w B z o n r t l d k e f g h0 h1 h2 h3

theorem packetReaderStoppingStoppedDomainUnique_kernel_certificate {m} (w B z o n r t l d k e f g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderStoppingStoppedDomainUniqueSentence w B z o n r t l d k e f g)) := TheoryTransport.sentence (source_packetReaderStoppingStoppedDomainUnique w B z o n r t l d k e f g)

theorem native_packetReaderStoppingStoppedDomainUnique {m} (w B z o n r t l d k e f g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderStoppingStoppedDomainUniqueSentence w B z o n r t l d k e f g)) := ZFReplay.replay (packetReaderStoppingStoppedDomainUnique_kernel_certificate w B z o n r t l d k e f g)

def packetReaderStoppingStoppedGraphUniqueSentence {m} (w B z o n r t l d k e f g : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem B w).imp ((PacketReaderStoppingSyntax.halted w B z o n r l d f).imp ((PacketReaderStoppingSyntax.halted w B z o n t k e g).imp ((Formula.equal f g)))))).close

theorem source_packetReaderStoppingStoppedGraphUnique {m} (w B z o n r t l d k e f g : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderStoppingStoppedGraphUniqueSentence w B z o n r t l d k e f g) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderStoppingSyntax.halted w B z o n t k e g) (Context.add (PacketReaderStoppingSyntax.halted w B z o n r l d f) (Context.add (Formula.mem B w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (Formula.mem B w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (PacketReaderStoppingSyntax.halted w B z o n r l d f) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (PacketReaderStoppingSyntax.halted w B z o n t k e g) := .hyp (Or.inl rfl)
  exact PacketReaderStoppingGraphs.graphs hZ w B z o n r t l d k e f g h0 h1 h2 h3

theorem packetReaderStoppingStoppedGraphUnique_kernel_certificate {m} (w B z o n r t l d k e f g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderStoppingStoppedGraphUniqueSentence w B z o n r t l d k e f g)) := TheoryTransport.sentence (source_packetReaderStoppingStoppedGraphUnique w B z o n r t l d k e f g)

theorem native_packetReaderStoppingStoppedGraphUnique {m} (w B z o n r t l d k e f g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderStoppingStoppedGraphUniqueSentence w B z o n r t l d k e f g)) := ZFReplay.replay (packetReaderStoppingStoppedGraphUnique_kernel_certificate w B z o n r t l d k e f g)

def packetReaderStoppingStoppedFieldsJointUniqueSentence {m} (w B z o n r t l d k e f g : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem B w).imp ((PacketReaderStoppingSyntax.halted w B z o n r l d f).imp ((PacketReaderStoppingSyntax.halted w B z o n t k e g).imp ((PacketReaderStoppingContract.same r l d f t k e g)))))).close

theorem source_packetReaderStoppingStoppedFieldsJointUnique {m} (w B z o n r t l d k e f g : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderStoppingStoppedFieldsJointUniqueSentence w B z o n r t l d k e f g) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderStoppingSyntax.halted w B z o n t k e g) (Context.add (PacketReaderStoppingSyntax.halted w B z o n r l d f) (Context.add (Formula.mem B w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (Formula.mem B w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (PacketReaderStoppingSyntax.halted w B z o n r l d f) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (PacketReaderStoppingSyntax.halted w B z o n t k e g) := .hyp (Or.inl rfl)
  exact PacketReaderStoppingContract.fields_unique hZ w B z o n r t l d k e f g h0 h1 h2 h3

theorem packetReaderStoppingStoppedFieldsJointUnique_kernel_certificate {m} (w B z o n r t l d k e f g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderStoppingStoppedFieldsJointUniqueSentence w B z o n r t l d k e f g)) := TheoryTransport.sentence (source_packetReaderStoppingStoppedFieldsJointUnique w B z o n r t l d k e f g)

theorem native_packetReaderStoppingStoppedFieldsJointUnique {m} (w B z o n r t l d k e f g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderStoppingStoppedFieldsJointUniqueSentence w B z o n r t l d k e f g)) := ZFReplay.replay (packetReaderStoppingStoppedFieldsJointUnique_kernel_certificate w B z o n r t l d k e f g)

def packetReaderStoppingStoppedFieldsUniversalUniqueSentence {m} (w B z o n r l d f : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem B w).imp ((PacketReaderStoppingSyntax.halted w B z o n r l d f).imp ((PacketReaderStoppingContract.uniqueAt w B z o n r l d f))))).close

theorem source_packetReaderStoppingStoppedFieldsUniversalUnique {m} (w B z o n r l d f : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderStoppingStoppedFieldsUniversalUniqueSentence w B z o n r l d f) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderStoppingSyntax.halted w B z o n r l d f) (Context.add (Formula.mem B w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (Formula.mem B w) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (PacketReaderStoppingSyntax.halted w B z o n r l d f) := .hyp (Or.inl rfl)
  exact PacketReaderStoppingContract.all_unique hZ w B z o n r l d f h0 h1 h2

theorem packetReaderStoppingStoppedFieldsUniversalUnique_kernel_certificate {m} (w B z o n r l d f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderStoppingStoppedFieldsUniversalUniqueSentence w B z o n r l d f)) := TheoryTransport.sentence (source_packetReaderStoppingStoppedFieldsUniversalUnique w B z o n r l d f)

theorem native_packetReaderStoppingStoppedFieldsUniversalUnique {m} (w B z o n r l d f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderStoppingStoppedFieldsUniversalUniqueSentence w B z o n r l d f)) := ZFReplay.replay (packetReaderStoppingStoppedFieldsUniversalUnique_kernel_certificate w B z o n r l d f)

def packetReaderStoppingCompleteHistoryExistsUniqueSentence {m} (w B z o n : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem B w).imp ((empty z).imp ((PacketReaderStateSyntax.carrier w n).imp ((PacketReaderStoppingContract.uniqueComplete w B z o n)))))).close

theorem source_packetReaderStoppingCompleteHistoryExistsUnique {m} (w B z o n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderStoppingCompleteHistoryExistsUniqueSentence w B z o n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderStateSyntax.carrier w n) (Context.add (empty z) (Context.add (Formula.mem B w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (Formula.mem B w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (empty z) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (PacketReaderStateSyntax.carrier w n) := .hyp (Or.inl rfl)
  exact PacketReaderStoppingContract.exists_unique hZ w B z o n h0 h1 h2 h3

theorem packetReaderStoppingCompleteHistoryExistsUnique_kernel_certificate {m} (w B z o n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderStoppingCompleteHistoryExistsUniqueSentence w B z o n)) := TheoryTransport.sentence (source_packetReaderStoppingCompleteHistoryExistsUnique w B z o n)

theorem native_packetReaderStoppingCompleteHistoryExistsUnique {m} (w B z o n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderStoppingCompleteHistoryExistsUniqueSentence w B z o n)) := ZFReplay.replay (packetReaderStoppingCompleteHistoryExistsUnique_kernel_certificate w B z o n)

end PPAC.Migration.Internal.ObjectPacketReaderStopping
