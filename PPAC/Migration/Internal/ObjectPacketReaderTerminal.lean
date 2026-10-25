import PPAC.Migration.Internal.PacketReaderTerminalContract

/-! Actual stopping states have exactly the three original mutually exclusive EOF-pass, EOF-fail and byte-reject observations. Classified real histories exist jointly uniquely. Actual EOF reverse, full reader bridge, Basic AST, Proof and Con remain unproved -/
namespace PPAC.Migration.Internal.ObjectPacketReaderTerminal
open Source SourceAlgebra SourceLogic OmegaSyntax

def packetReaderTerminalRawObservationForbidsSuccessorSentence {m} (w B z o n L v s a : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem B w).imp ((PacketReaderStateSyntax.code w L v s a n).imp ((PacketReaderTerminalSyntax.raw w B z o L v s a).imp (((PacketReaderCodedSyntax.existsNext w B z o n).neg)))))).close

theorem source_packetReaderTerminalRawObservationForbidsSuccessor {m} (w B z o n L v s a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderTerminalRawObservationForbidsSuccessorSentence w B z o n L v s a) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderTerminalSyntax.raw w B z o L v s a) (Context.add (PacketReaderStateSyntax.code w L v s a n) (Context.add (Formula.mem B w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (Formula.mem B w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (PacketReaderStateSyntax.code w L v s a n) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (PacketReaderTerminalSyntax.raw w B z o L v s a) := .hyp (Or.inl rfl)
  exact PacketReaderTerminalRaw.no_next_of_raw hZ w B z o n L v s a h0 h1 h2 h3

theorem packetReaderTerminalRawObservationForbidsSuccessor_kernel_certificate {m} (w B z o n L v s a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderTerminalRawObservationForbidsSuccessorSentence w B z o n L v s a)) := TheoryTransport.sentence (source_packetReaderTerminalRawObservationForbidsSuccessor w B z o n L v s a)

theorem native_packetReaderTerminalRawObservationForbidsSuccessor {m} (w B z o n L v s a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderTerminalRawObservationForbidsSuccessorSentence w B z o n L v s a)) := ZFReplay.replay (packetReaderTerminalRawObservationForbidsSuccessor_kernel_certificate w B z o n L v s a)

def packetReaderTerminalNoSuccessorGivesThreeOriginalObservationsSentence {m} (w B z o n L v s a : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem B w).imp ((Formula.mem z w).imp ((Formula.mem o w).imp ((PacketReaderStateSyntax.code w L v s a n).imp (((PacketReaderCodedSyntax.existsNext w B z o n).neg).imp ((PacketReaderTerminalSyntax.raw w B z o L v s a)))))))).close

theorem source_packetReaderTerminalNoSuccessorGivesThreeOriginalObservations {m} (w B z o n L v s a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderTerminalNoSuccessorGivesThreeOriginalObservationsSentence w B z o n L v s a) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add ((PacketReaderCodedSyntax.existsNext w B z o n).neg) (Context.add (PacketReaderStateSyntax.code w L v s a n) (Context.add (Formula.mem o w) (Context.add (Formula.mem z w) (Context.add (Formula.mem B w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (Formula.mem B w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (Formula.mem z w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (Formula.mem o w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (PacketReaderStateSyntax.code w L v s a n) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ ((PacketReaderCodedSyntax.existsNext w B z o n).neg) := .hyp (Or.inl rfl)
  exact PacketReaderTerminalRaw.raw_of_no_next hZ w B z o n L v s a h0 h1 h2 h3 h4 h5

theorem packetReaderTerminalNoSuccessorGivesThreeOriginalObservations_kernel_certificate {m} (w B z o n L v s a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderTerminalNoSuccessorGivesThreeOriginalObservationsSentence w B z o n L v s a)) := TheoryTransport.sentence (source_packetReaderTerminalNoSuccessorGivesThreeOriginalObservations w B z o n L v s a)

theorem native_packetReaderTerminalNoSuccessorGivesThreeOriginalObservations {m} (w B z o n L v s a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderTerminalNoSuccessorGivesThreeOriginalObservationsSentence w B z o n L v s a)) := ZFReplay.replay (packetReaderTerminalNoSuccessorGivesThreeOriginalObservations_kernel_certificate w B z o n L v s a)

def packetReaderTerminalExactThreeWayStoppingAtEveryActualCodeSentence {m} (w B z o n L v s a : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem B w).imp ((Formula.mem z w).imp ((Formula.mem o w).imp ((PacketReaderStateSyntax.code w L v s a n).imp (((PacketReaderTerminalSyntax.raw w B z o L v s a).iff (PacketReaderCodedSyntax.existsNext w B z o n).neg))))))).close

theorem source_packetReaderTerminalExactThreeWayStoppingAtEveryActualCode {m} (w B z o n L v s a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderTerminalExactThreeWayStoppingAtEveryActualCodeSentence w B z o n L v s a) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderStateSyntax.code w L v s a n) (Context.add (Formula.mem o w) (Context.add (Formula.mem z w) (Context.add (Formula.mem B w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
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
  have h4 : Derives Δ (PacketReaderStateSyntax.code w L v s a n) := .hyp (Or.inl rfl)
  exact PacketReaderTerminalRaw.at_actual_code hZ w B z o n L v s a h0 h1 h2 h3 h4

theorem packetReaderTerminalExactThreeWayStoppingAtEveryActualCode_kernel_certificate {m} (w B z o n L v s a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderTerminalExactThreeWayStoppingAtEveryActualCodeSentence w B z o n L v s a)) := TheoryTransport.sentence (source_packetReaderTerminalExactThreeWayStoppingAtEveryActualCode w B z o n L v s a)

theorem native_packetReaderTerminalExactThreeWayStoppingAtEveryActualCode {m} (w B z o n L v s a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderTerminalExactThreeWayStoppingAtEveryActualCodeSentence w B z o n L v s a)) := ZFReplay.replay (packetReaderTerminalExactThreeWayStoppingAtEveryActualCode_kernel_certificate w B z o n L v s a)

def packetReaderTerminalEOFSuccessFailureDisjointSentence {m} (w z o L v s a : Fin m) : Source.Sentence := ((PacketReaderInputSyntax.eofSuccess w z o L v s a).imp ((PacketReaderInputSyntax.eofFailure w z o L v s a).imp ((Formula.bot)))).close

theorem source_packetReaderTerminalEOFSuccessFailureDisjoint {m} (w z o L v s a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderTerminalEOFSuccessFailureDisjointSentence w z o L v s a) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderInputSyntax.eofFailure w z o L v s a) (Context.add (PacketReaderInputSyntax.eofSuccess w z o L v s a) (Source.SetLanguage.ZF.at m))
  have h0 : Derives Δ (PacketReaderInputSyntax.eofSuccess w z o L v s a) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PacketReaderInputSyntax.eofFailure w z o L v s a) := .hyp (Or.inl rfl)
  exact PacketReaderTerminalRaw.success_failure_disjoint w z o L v s a h0 h1

theorem packetReaderTerminalEOFSuccessFailureDisjoint_kernel_certificate {m} (w z o L v s a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderTerminalEOFSuccessFailureDisjointSentence w z o L v s a)) := TheoryTransport.sentence (source_packetReaderTerminalEOFSuccessFailureDisjoint w z o L v s a)

theorem native_packetReaderTerminalEOFSuccessFailureDisjoint {m} (w z o L v s a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderTerminalEOFSuccessFailureDisjointSentence w z o L v s a)) := ZFReplay.replay (packetReaderTerminalEOFSuccessFailureDisjoint_kernel_certificate w z o L v s a)

def packetReaderTerminalEOFSuccessByteRejectDisjointSentence {m} (w B z o L v s a : Fin m) : Source.Sentence := ((omega w).imp ((PacketReaderInputSyntax.eofSuccess w z o L v s a).imp ((PacketReaderInputSyntax.blocked w B z o L s).imp ((Formula.bot))))).close

theorem source_packetReaderTerminalEOFSuccessByteRejectDisjoint {m} (w B z o L v s a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderTerminalEOFSuccessByteRejectDisjointSentence w B z o L v s a) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderInputSyntax.blocked w B z o L s) (Context.add (PacketReaderInputSyntax.eofSuccess w z o L v s a) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (PacketReaderInputSyntax.eofSuccess w z o L v s a) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (PacketReaderInputSyntax.blocked w B z o L s) := .hyp (Or.inl rfl)
  exact PacketReaderTerminalRaw.success_reject_disjoint hZ w B z o L v s a h0 h1 h2

theorem packetReaderTerminalEOFSuccessByteRejectDisjoint_kernel_certificate {m} (w B z o L v s a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderTerminalEOFSuccessByteRejectDisjointSentence w B z o L v s a)) := TheoryTransport.sentence (source_packetReaderTerminalEOFSuccessByteRejectDisjoint w B z o L v s a)

theorem native_packetReaderTerminalEOFSuccessByteRejectDisjoint {m} (w B z o L v s a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderTerminalEOFSuccessByteRejectDisjointSentence w B z o L v s a)) := ZFReplay.replay (packetReaderTerminalEOFSuccessByteRejectDisjoint_kernel_certificate w B z o L v s a)

def packetReaderTerminalEOFFailureByteRejectDisjointSentence {m} (w B z o L v s a : Fin m) : Source.Sentence := ((omega w).imp ((PacketReaderInputSyntax.eofFailure w z o L v s a).imp ((PacketReaderInputSyntax.blocked w B z o L s).imp ((Formula.bot))))).close

theorem source_packetReaderTerminalEOFFailureByteRejectDisjoint {m} (w B z o L v s a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderTerminalEOFFailureByteRejectDisjointSentence w B z o L v s a) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderInputSyntax.blocked w B z o L s) (Context.add (PacketReaderInputSyntax.eofFailure w z o L v s a) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (PacketReaderInputSyntax.eofFailure w z o L v s a) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (PacketReaderInputSyntax.blocked w B z o L s) := .hyp (Or.inl rfl)
  exact PacketReaderTerminalRaw.failure_reject_disjoint hZ w B z o L v s a h0 h1 h2

theorem packetReaderTerminalEOFFailureByteRejectDisjoint_kernel_certificate {m} (w B z o L v s a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderTerminalEOFFailureByteRejectDisjointSentence w B z o L v s a)) := TheoryTransport.sentence (source_packetReaderTerminalEOFFailureByteRejectDisjoint w B z o L v s a)

theorem native_packetReaderTerminalEOFFailureByteRejectDisjoint {m} (w B z o L v s a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderTerminalEOFFailureByteRejectDisjointSentence w B z o L v s a)) := ZFReplay.replay (packetReaderTerminalEOFFailureByteRejectDisjoint_kernel_certificate w B z o L v s a)

def packetReaderTerminalObservationHasExactCarrierAndNoSuccessorSentence {m} (w B z o n : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem B w).imp ((PacketReaderTerminalSyntax.observation w B z o n).imp (((PacketReaderStateSyntax.carrier w n).conj (PacketReaderCodedSyntax.existsNext w B z o n).neg))))).close

theorem source_packetReaderTerminalObservationHasExactCarrierAndNoSuccessor {m} (w B z o n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderTerminalObservationHasExactCarrierAndNoSuccessorSentence w B z o n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderTerminalSyntax.observation w B z o n) (Context.add (Formula.mem B w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (Formula.mem B w) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (PacketReaderTerminalSyntax.observation w B z o n) := .hyp (Or.inl rfl)
  exact PacketReaderTerminalObservation.domain hZ w B z o n h0 h1 h2

theorem packetReaderTerminalObservationHasExactCarrierAndNoSuccessor_kernel_certificate {m} (w B z o n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderTerminalObservationHasExactCarrierAndNoSuccessorSentence w B z o n)) := TheoryTransport.sentence (source_packetReaderTerminalObservationHasExactCarrierAndNoSuccessor w B z o n)

theorem native_packetReaderTerminalObservationHasExactCarrierAndNoSuccessor {m} (w B z o n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderTerminalObservationHasExactCarrierAndNoSuccessorSentence w B z o n)) := ZFReplay.replay (packetReaderTerminalObservationHasExactCarrierAndNoSuccessor_kernel_certificate w B z o n)

def packetReaderTerminalCarrierNoSuccessorHasActualObservationSentence {m} (w B z o n : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem B w).imp ((Formula.mem z w).imp ((Formula.mem o w).imp ((PacketReaderStateSyntax.carrier w n).imp (((PacketReaderCodedSyntax.existsNext w B z o n).neg).imp ((PacketReaderTerminalSyntax.observation w B z o n)))))))).close

theorem source_packetReaderTerminalCarrierNoSuccessorHasActualObservation {m} (w B z o n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderTerminalCarrierNoSuccessorHasActualObservationSentence w B z o n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add ((PacketReaderCodedSyntax.existsNext w B z o n).neg) (Context.add (PacketReaderStateSyntax.carrier w n) (Context.add (Formula.mem o w) (Context.add (Formula.mem z w) (Context.add (Formula.mem B w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (Formula.mem B w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (Formula.mem z w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (Formula.mem o w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (PacketReaderStateSyntax.carrier w n) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ ((PacketReaderCodedSyntax.existsNext w B z o n).neg) := .hyp (Or.inl rfl)
  exact PacketReaderTerminalObservation.from_carrier hZ w B z o n h0 h1 h2 h3 h4 h5

theorem packetReaderTerminalCarrierNoSuccessorHasActualObservation_kernel_certificate {m} (w B z o n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderTerminalCarrierNoSuccessorHasActualObservationSentence w B z o n)) := TheoryTransport.sentence (source_packetReaderTerminalCarrierNoSuccessorHasActualObservation w B z o n)

theorem native_packetReaderTerminalCarrierNoSuccessorHasActualObservation {m} (w B z o n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderTerminalCarrierNoSuccessorHasActualObservationSentence w B z o n)) := ZFReplay.replay (packetReaderTerminalCarrierNoSuccessorHasActualObservation_kernel_certificate w B z o n)

def packetReaderTerminalExactObservationDomainAllCandidateCodesSentence {m} (w B z o n : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem B w).imp ((Formula.mem z w).imp ((Formula.mem o w).imp (((PacketReaderTerminalSyntax.observation w B z o n).iff ((PacketReaderStateSyntax.carrier w n).conj (PacketReaderCodedSyntax.existsNext w B z o n).neg))))))).close

theorem source_packetReaderTerminalExactObservationDomainAllCandidateCodes {m} (w B z o n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderTerminalExactObservationDomainAllCandidateCodesSentence w B z o n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem o w) (Context.add (Formula.mem z w) (Context.add (Formula.mem B w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (Formula.mem B w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (Formula.mem z w) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (Formula.mem o w) := .hyp (Or.inl rfl)
  exact PacketReaderTerminalObservation.exact_domain hZ w B z o n h0 h1 h2 h3

theorem packetReaderTerminalExactObservationDomainAllCandidateCodes_kernel_certificate {m} (w B z o n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderTerminalExactObservationDomainAllCandidateCodesSentence w B z o n)) := TheoryTransport.sentence (source_packetReaderTerminalExactObservationDomainAllCandidateCodes w B z o n)

theorem native_packetReaderTerminalExactObservationDomainAllCandidateCodes {m} (w B z o n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderTerminalExactObservationDomainAllCandidateCodesSentence w B z o n)) := ZFReplay.replay (packetReaderTerminalExactObservationDomainAllCandidateCodes_kernel_certificate w B z o n)

def packetReaderTerminalObservationNormalizesAtActualStateFieldsSentence {m} (w B z o n L v s a : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem B w).imp ((Formula.mem z w).imp ((Formula.mem o w).imp ((PacketReaderStateSyntax.code w L v s a n).imp (((PacketReaderTerminalSyntax.observation w B z o n).iff (PacketReaderTerminalSyntax.raw w B z o L v s a)))))))).close

theorem source_packetReaderTerminalObservationNormalizesAtActualStateFields {m} (w B z o n L v s a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderTerminalObservationNormalizesAtActualStateFieldsSentence w B z o n L v s a) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderStateSyntax.code w L v s a n) (Context.add (Formula.mem o w) (Context.add (Formula.mem z w) (Context.add (Formula.mem B w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
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
  have h4 : Derives Δ (PacketReaderStateSyntax.code w L v s a n) := .hyp (Or.inl rfl)
  exact PacketReaderTerminalObservation.at_actual_code hZ w B z o n L v s a h0 h1 h2 h3 h4

theorem packetReaderTerminalObservationNormalizesAtActualStateFields_kernel_certificate {m} (w B z o n L v s a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderTerminalObservationNormalizesAtActualStateFieldsSentence w B z o n L v s a)) := TheoryTransport.sentence (source_packetReaderTerminalObservationNormalizesAtActualStateFields w B z o n L v s a)

theorem native_packetReaderTerminalObservationNormalizesAtActualStateFields {m} (w B z o n L v s a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderTerminalObservationNormalizesAtActualStateFieldsSentence w B z o n L v s a)) := ZFReplay.replay (packetReaderTerminalObservationNormalizesAtActualStateFields_kernel_certificate w B z o n L v s a)

def packetReaderTerminalHaltedHistoryHasActualOriginalStopCauseSentence {m} (w B z o n r l d f : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem B w).imp ((Formula.mem z w).imp ((Formula.mem o w).imp ((PacketReaderStoppingSyntax.halted w B z o n r l d f).imp ((PacketReaderTerminalSyntax.classifiedHistory w B z o n r l d f))))))).close

theorem source_packetReaderTerminalHaltedHistoryHasActualOriginalStopCause {m} (w B z o n r l d f : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderTerminalHaltedHistoryHasActualOriginalStopCauseSentence w B z o n r l d f) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderStoppingSyntax.halted w B z o n r l d f) (Context.add (Formula.mem o w) (Context.add (Formula.mem z w) (Context.add (Formula.mem B w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
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
  have h4 : Derives Δ (PacketReaderStoppingSyntax.halted w B z o n r l d f) := .hyp (Or.inl rfl)
  exact PacketReaderTerminalHistory.from_halted hZ w B z o n r l d f h0 h1 h2 h3 h4

theorem packetReaderTerminalHaltedHistoryHasActualOriginalStopCause_kernel_certificate {m} (w B z o n r l d f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderTerminalHaltedHistoryHasActualOriginalStopCauseSentence w B z o n r l d f)) := TheoryTransport.sentence (source_packetReaderTerminalHaltedHistoryHasActualOriginalStopCause w B z o n r l d f)

theorem native_packetReaderTerminalHaltedHistoryHasActualOriginalStopCause {m} (w B z o n r l d f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderTerminalHaltedHistoryHasActualOriginalStopCauseSentence w B z o n r l d f)) := ZFReplay.replay (packetReaderTerminalHaltedHistoryHasActualOriginalStopCause_kernel_certificate w B z o n r l d f)

def packetReaderTerminalClassifiedRealHistoryIsHaltedSentence {m} (w B z o n r l d f : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem B w).imp ((PacketReaderTerminalSyntax.classifiedHistory w B z o n r l d f).imp ((PacketReaderStoppingSyntax.halted w B z o n r l d f))))).close

theorem source_packetReaderTerminalClassifiedRealHistoryIsHalted {m} (w B z o n r l d f : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderTerminalClassifiedRealHistoryIsHaltedSentence w B z o n r l d f) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderTerminalSyntax.classifiedHistory w B z o n r l d f) (Context.add (Formula.mem B w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (Formula.mem B w) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (PacketReaderTerminalSyntax.classifiedHistory w B z o n r l d f) := .hyp (Or.inl rfl)
  exact PacketReaderTerminalHistory.to_halted hZ w B z o n r l d f h0 h1 h2

theorem packetReaderTerminalClassifiedRealHistoryIsHalted_kernel_certificate {m} (w B z o n r l d f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderTerminalClassifiedRealHistoryIsHaltedSentence w B z o n r l d f)) := TheoryTransport.sentence (source_packetReaderTerminalClassifiedRealHistoryIsHalted w B z o n r l d f)

theorem native_packetReaderTerminalClassifiedRealHistoryIsHalted {m} (w B z o n r l d f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderTerminalClassifiedRealHistoryIsHaltedSentence w B z o n r l d f)) := ZFReplay.replay (packetReaderTerminalClassifiedRealHistoryIsHalted_kernel_certificate w B z o n r l d f)

def packetReaderTerminalExactClassifiedHistoryEquivalenceSentence {m} (w B z o n r l d f : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem B w).imp ((Formula.mem z w).imp ((Formula.mem o w).imp (((PacketReaderTerminalSyntax.classifiedHistory w B z o n r l d f).iff (PacketReaderStoppingSyntax.halted w B z o n r l d f))))))).close

theorem source_packetReaderTerminalExactClassifiedHistoryEquivalence {m} (w B z o n r l d f : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderTerminalExactClassifiedHistoryEquivalenceSentence w B z o n r l d f) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem o w) (Context.add (Formula.mem z w) (Context.add (Formula.mem B w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (Formula.mem B w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (Formula.mem z w) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (Formula.mem o w) := .hyp (Or.inl rfl)
  exact PacketReaderTerminalHistory.exact_history hZ w B z o n r l d f h0 h1 h2 h3

theorem packetReaderTerminalExactClassifiedHistoryEquivalence_kernel_certificate {m} (w B z o n r l d f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderTerminalExactClassifiedHistoryEquivalenceSentence w B z o n r l d f)) := TheoryTransport.sentence (source_packetReaderTerminalExactClassifiedHistoryEquivalence w B z o n r l d f)

theorem native_packetReaderTerminalExactClassifiedHistoryEquivalence {m} (w B z o n r l d f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderTerminalExactClassifiedHistoryEquivalenceSentence w B z o n r l d f)) := ZFReplay.replay (packetReaderTerminalExactClassifiedHistoryEquivalence_kernel_certificate w B z o n r l d f)

def packetReaderTerminalClassifiedCompleteHistoryExistsSentence {m} (w B z o n : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem B w).imp ((empty z).imp ((Formula.mem o w).imp ((PacketReaderStateSyntax.carrier w n).imp ((PacketReaderTerminalSyntax.classifiedComplete w B z o n))))))).close

theorem source_packetReaderTerminalClassifiedCompleteHistoryExists {m} (w B z o n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderTerminalClassifiedCompleteHistoryExistsSentence w B z o n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderStateSyntax.carrier w n) (Context.add (Formula.mem o w) (Context.add (empty z) (Context.add (Formula.mem B w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (Formula.mem B w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (empty z) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (Formula.mem o w) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (PacketReaderStateSyntax.carrier w n) := .hyp (Or.inl rfl)
  exact PacketReaderTerminalHistory.exists_classified hZ w B z o n h0 h1 h2 h3 h4

theorem packetReaderTerminalClassifiedCompleteHistoryExists_kernel_certificate {m} (w B z o n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderTerminalClassifiedCompleteHistoryExistsSentence w B z o n)) := TheoryTransport.sentence (source_packetReaderTerminalClassifiedCompleteHistoryExists w B z o n)

theorem native_packetReaderTerminalClassifiedCompleteHistoryExists {m} (w B z o n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderTerminalClassifiedCompleteHistoryExistsSentence w B z o n)) := ZFReplay.replay (packetReaderTerminalClassifiedCompleteHistoryExists_kernel_certificate w B z o n)

def packetReaderTerminalClassifiedHistoriesJointlyUniqueSentence {m} (w B z o n r t l d k e f g : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem B w).imp ((PacketReaderTerminalSyntax.classifiedHistory w B z o n r l d f).imp ((PacketReaderTerminalSyntax.classifiedHistory w B z o n t k e g).imp ((PacketReaderStoppingContract.same r l d f t k e g)))))).close

theorem source_packetReaderTerminalClassifiedHistoriesJointlyUnique {m} (w B z o n r t l d k e f g : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderTerminalClassifiedHistoriesJointlyUniqueSentence w B z o n r t l d k e f g) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderTerminalSyntax.classifiedHistory w B z o n t k e g) (Context.add (PacketReaderTerminalSyntax.classifiedHistory w B z o n r l d f) (Context.add (Formula.mem B w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (Formula.mem B w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (PacketReaderTerminalSyntax.classifiedHistory w B z o n r l d f) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (PacketReaderTerminalSyntax.classifiedHistory w B z o n t k e g) := .hyp (Or.inl rfl)
  exact PacketReaderTerminalContract.fields_unique hZ w B z o n r t l d k e f g h0 h1 h2 h3

theorem packetReaderTerminalClassifiedHistoriesJointlyUnique_kernel_certificate {m} (w B z o n r t l d k e f g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderTerminalClassifiedHistoriesJointlyUniqueSentence w B z o n r t l d k e f g)) := TheoryTransport.sentence (source_packetReaderTerminalClassifiedHistoriesJointlyUnique w B z o n r t l d k e f g)

theorem native_packetReaderTerminalClassifiedHistoriesJointlyUnique {m} (w B z o n r t l d k e f g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderTerminalClassifiedHistoriesJointlyUniqueSentence w B z o n r t l d k e f g)) := ZFReplay.replay (packetReaderTerminalClassifiedHistoriesJointlyUnique_kernel_certificate w B z o n r t l d k e f g)

def packetReaderTerminalClassifiedHistoryUniversalUniquenessSentence {m} (w B z o n r l d f : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem B w).imp ((PacketReaderTerminalSyntax.classifiedHistory w B z o n r l d f).imp ((PacketReaderTerminalContract.uniqueAt w B z o n r l d f))))).close

theorem source_packetReaderTerminalClassifiedHistoryUniversalUniqueness {m} (w B z o n r l d f : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderTerminalClassifiedHistoryUniversalUniquenessSentence w B z o n r l d f) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderTerminalSyntax.classifiedHistory w B z o n r l d f) (Context.add (Formula.mem B w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (Formula.mem B w) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (PacketReaderTerminalSyntax.classifiedHistory w B z o n r l d f) := .hyp (Or.inl rfl)
  exact PacketReaderTerminalContract.all_unique hZ w B z o n r l d f h0 h1 h2

theorem packetReaderTerminalClassifiedHistoryUniversalUniqueness_kernel_certificate {m} (w B z o n r l d f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderTerminalClassifiedHistoryUniversalUniquenessSentence w B z o n r l d f)) := TheoryTransport.sentence (source_packetReaderTerminalClassifiedHistoryUniversalUniqueness w B z o n r l d f)

theorem native_packetReaderTerminalClassifiedHistoryUniversalUniqueness {m} (w B z o n r l d f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderTerminalClassifiedHistoryUniversalUniquenessSentence w B z o n r l d f)) := ZFReplay.replay (packetReaderTerminalClassifiedHistoryUniversalUniqueness_kernel_certificate w B z o n r l d f)

def packetReaderTerminalClassifiedCompleteHistoryExistsUniqueSentence {m} (w B z o n : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem B w).imp ((empty z).imp ((Formula.mem o w).imp ((PacketReaderStateSyntax.carrier w n).imp ((PacketReaderTerminalContract.uniqueClassifiedComplete w B z o n))))))).close

theorem source_packetReaderTerminalClassifiedCompleteHistoryExistsUnique {m} (w B z o n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderTerminalClassifiedCompleteHistoryExistsUniqueSentence w B z o n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderStateSyntax.carrier w n) (Context.add (Formula.mem o w) (Context.add (empty z) (Context.add (Formula.mem B w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (Formula.mem B w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (empty z) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (Formula.mem o w) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (PacketReaderStateSyntax.carrier w n) := .hyp (Or.inl rfl)
  exact PacketReaderTerminalContract.exists_unique hZ w B z o n h0 h1 h2 h3 h4

theorem packetReaderTerminalClassifiedCompleteHistoryExistsUnique_kernel_certificate {m} (w B z o n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderTerminalClassifiedCompleteHistoryExistsUniqueSentence w B z o n)) := TheoryTransport.sentence (source_packetReaderTerminalClassifiedCompleteHistoryExistsUnique w B z o n)

theorem native_packetReaderTerminalClassifiedCompleteHistoryExistsUnique {m} (w B z o n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderTerminalClassifiedCompleteHistoryExistsUniqueSentence w B z o n)) := ZFReplay.replay (packetReaderTerminalClassifiedCompleteHistoryExistsUnique_kernel_certificate w B z o n)

end PPAC.Migration.Internal.ObjectPacketReaderTerminal
