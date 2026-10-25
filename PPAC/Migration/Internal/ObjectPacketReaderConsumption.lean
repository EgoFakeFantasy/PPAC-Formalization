import PPAC.Migration.Internal.PacketReaderConsumptionStopping

/-! Actual raw and coded steps consume one original Cons cell. Every real history domain index has a unique valid input, every internal step has actual adjacent consumption witnesses, and Nil/reject boundaries forbid continuation. Complete stopping-history existence, EOF reverse, full reader bridge, Basic AST, Proof and Con remain unproved -/
namespace PPAC.Migration.Internal.ObjectPacketReaderConsumption
open Source SourceAlgebra SourceLogic OmegaSyntax

def packetReaderConsumptionRawStepConsumesActualConsSentence {m} (w B z o l v s a r y q c : Fin m) : Source.Sentence := ((PacketReaderInputSyntax.advance w B z o l v s a r y q c).imp ((PacketReaderConsumptionSyntax.tail w l r))).close

theorem source_packetReaderConsumptionRawStepConsumesActualCons {m} (w B z o l v s a r y q c : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderConsumptionRawStepConsumesActualConsSentence w B z o l v s a r y q c) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderInputSyntax.advance w B z o l v s a r y q c) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (PacketReaderInputSyntax.advance w B z o l v s a r y q c) := .hyp (Or.inl rfl)
  exact PacketReaderRawConsumption.raw_tail w B z o l v s a r y q c h0

theorem packetReaderConsumptionRawStepConsumesActualCons_kernel_certificate {m} (w B z o l v s a r y q c : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderConsumptionRawStepConsumesActualConsSentence w B z o l v s a r y q c)) := TheoryTransport.sentence (source_packetReaderConsumptionRawStepConsumesActualCons w B z o l v s a r y q c)

theorem native_packetReaderConsumptionRawStepConsumesActualCons {m} (w B z o l v s a r y q c : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderConsumptionRawStepConsumesActualConsSentence w B z o l v s a r y q c)) := ZFReplay.replay (packetReaderConsumptionRawStepConsumesActualCons_kernel_certificate w B z o l v s a r y q c)

def packetReaderConsumptionRawStepStrictInputDescentSentence {m} (w B z o l v s a r y q c : Fin m) : Source.Sentence := ((omega w).imp ((PacketReaderInputSyntax.advance w B z o l v s a r y q c).imp ((Formula.mem r l)))).close

theorem source_packetReaderConsumptionRawStepStrictInputDescent {m} (w B z o l v s a r y q c : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderConsumptionRawStepStrictInputDescentSentence w B z o l v s a r y q c) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderInputSyntax.advance w B z o l v s a r y q c) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PacketReaderInputSyntax.advance w B z o l v s a r y q c) := .hyp (Or.inl rfl)
  exact PacketReaderRawConsumption.raw_strict hZ w B z o l v s a r y q c h0 h1

theorem packetReaderConsumptionRawStepStrictInputDescent_kernel_certificate {m} (w B z o l v s a r y q c : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderConsumptionRawStepStrictInputDescentSentence w B z o l v s a r y q c)) := TheoryTransport.sentence (source_packetReaderConsumptionRawStepStrictInputDescent w B z o l v s a r y q c)

theorem native_packetReaderConsumptionRawStepStrictInputDescent {m} (w B z o l v s a r y q c : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderConsumptionRawStepStrictInputDescentSentence w B z o l v s a r y q c)) := ZFReplay.replay (packetReaderConsumptionRawStepStrictInputDescent_kernel_certificate w B z o l v s a r y q c)

def packetReaderConsumptionCarrierHasActualValidInputSentence {m} (w n : Fin m) : Source.Sentence := ((PacketReaderStateSyntax.carrier w n).imp ((PacketReaderConsumptionSyntax.existsInput w n))).close

theorem source_packetReaderConsumptionCarrierHasActualValidInput {m} (w n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderConsumptionCarrierHasActualValidInputSentence w n) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderStateSyntax.carrier w n) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (PacketReaderStateSyntax.carrier w n) := .hyp (Or.inl rfl)
  exact PacketReaderInputProjection.exists_of_carrier w n h0

theorem packetReaderConsumptionCarrierHasActualValidInput_kernel_certificate {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderConsumptionCarrierHasActualValidInputSentence w n)) := TheoryTransport.sentence (source_packetReaderConsumptionCarrierHasActualValidInput w n)

theorem native_packetReaderConsumptionCarrierHasActualValidInput {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderConsumptionCarrierHasActualValidInputSentence w n)) := ZFReplay.replay (packetReaderConsumptionCarrierHasActualValidInput_kernel_certificate w n)

def packetReaderConsumptionInputAgreesWithActualStateCodeSentence {m} (w n l v s a L : Fin m) : Source.Sentence := ((omega w).imp ((PacketReaderStateSyntax.code w l v s a n).imp ((PacketReaderConsumptionSyntax.input w n L).imp ((Formula.equal L l))))).close

theorem source_packetReaderConsumptionInputAgreesWithActualStateCode {m} (w n l v s a L : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderConsumptionInputAgreesWithActualStateCodeSentence w n l v s a L) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderConsumptionSyntax.input w n L) (Context.add (PacketReaderStateSyntax.code w l v s a n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (PacketReaderStateSyntax.code w l v s a n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (PacketReaderConsumptionSyntax.input w n L) := .hyp (Or.inl rfl)
  exact PacketReaderInputProjection.at_code hZ w n l v s a L h0 h1 h2

theorem packetReaderConsumptionInputAgreesWithActualStateCode_kernel_certificate {m} (w n l v s a L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderConsumptionInputAgreesWithActualStateCodeSentence w n l v s a L)) := TheoryTransport.sentence (source_packetReaderConsumptionInputAgreesWithActualStateCode w n l v s a L)

theorem native_packetReaderConsumptionInputAgreesWithActualStateCode {m} (w n l v s a L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderConsumptionInputAgreesWithActualStateCodeSentence w n l v s a L)) := ZFReplay.replay (packetReaderConsumptionInputAgreesWithActualStateCode_kernel_certificate w n l v s a L)

def packetReaderConsumptionActualStateInputUniqueSentence {m} (w n l L : Fin m) : Source.Sentence := ((omega w).imp ((PacketReaderConsumptionSyntax.input w n l).imp ((PacketReaderConsumptionSyntax.input w n L).imp ((Formula.equal l L))))).close

theorem source_packetReaderConsumptionActualStateInputUnique {m} (w n l L : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderConsumptionActualStateInputUniqueSentence w n l L) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderConsumptionSyntax.input w n L) (Context.add (PacketReaderConsumptionSyntax.input w n l) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (PacketReaderConsumptionSyntax.input w n l) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (PacketReaderConsumptionSyntax.input w n L) := .hyp (Or.inl rfl)
  exact PacketReaderInputProjection.unique hZ w n l L h0 h1 h2

theorem packetReaderConsumptionActualStateInputUnique_kernel_certificate {m} (w n l L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderConsumptionActualStateInputUniqueSentence w n l L)) := TheoryTransport.sentence (source_packetReaderConsumptionActualStateInputUnique w n l L)

theorem native_packetReaderConsumptionActualStateInputUnique {m} (w n l L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderConsumptionActualStateInputUniqueSentence w n l L)) := ZFReplay.replay (packetReaderConsumptionActualStateInputUnique_kernel_certificate w n l L)

def packetReaderConsumptionCodedStepConsumesActualConsSentence {m} (w B z o n r l x : Fin m) : Source.Sentence := ((omega w).imp ((PacketReaderConsumptionSyntax.input w n l).imp ((PacketReaderConsumptionSyntax.input w r x).imp ((PacketReaderCodedSyntax.step w B z o n r).imp ((PacketReaderConsumptionSyntax.tail w l x)))))).close

theorem source_packetReaderConsumptionCodedStepConsumesActualCons {m} (w B z o n r l x : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderConsumptionCodedStepConsumesActualConsSentence w B z o n r l x) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderCodedSyntax.step w B z o n r) (Context.add (PacketReaderConsumptionSyntax.input w r x) (Context.add (PacketReaderConsumptionSyntax.input w n l) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (PacketReaderConsumptionSyntax.input w n l) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (PacketReaderConsumptionSyntax.input w r x) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (PacketReaderCodedSyntax.step w B z o n r) := .hyp (Or.inl rfl)
  exact PacketReaderCodedConsumption.at_inputs hZ w B z o n r l x h0 h1 h2 h3

theorem packetReaderConsumptionCodedStepConsumesActualCons_kernel_certificate {m} (w B z o n r l x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderConsumptionCodedStepConsumesActualConsSentence w B z o n r l x)) := TheoryTransport.sentence (source_packetReaderConsumptionCodedStepConsumesActualCons w B z o n r l x)

theorem native_packetReaderConsumptionCodedStepConsumesActualCons {m} (w B z o n r l x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderConsumptionCodedStepConsumesActualConsSentence w B z o n r l x)) := ZFReplay.replay (packetReaderConsumptionCodedStepConsumesActualCons_kernel_certificate w B z o n r l x)

def packetReaderConsumptionCodedStepStrictInputDescentSentence {m} (w B z o n r l x : Fin m) : Source.Sentence := ((omega w).imp ((PacketReaderConsumptionSyntax.input w n l).imp ((PacketReaderConsumptionSyntax.input w r x).imp ((PacketReaderCodedSyntax.step w B z o n r).imp ((Formula.mem x l)))))).close

theorem source_packetReaderConsumptionCodedStepStrictInputDescent {m} (w B z o n r l x : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderConsumptionCodedStepStrictInputDescentSentence w B z o n r l x) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderCodedSyntax.step w B z o n r) (Context.add (PacketReaderConsumptionSyntax.input w r x) (Context.add (PacketReaderConsumptionSyntax.input w n l) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (PacketReaderConsumptionSyntax.input w n l) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (PacketReaderConsumptionSyntax.input w r x) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (PacketReaderCodedSyntax.step w B z o n r) := .hyp (Or.inl rfl)
  exact PacketReaderCodedConsumption.strict hZ w B z o n r l x h0 h1 h2 h3

theorem packetReaderConsumptionCodedStepStrictInputDescent_kernel_certificate {m} (w B z o n r l x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderConsumptionCodedStepStrictInputDescentSentence w B z o n r l x)) := TheoryTransport.sentence (source_packetReaderConsumptionCodedStepStrictInputDescent w B z o n r l x)

theorem native_packetReaderConsumptionCodedStepStrictInputDescent {m} (w B z o n r l x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderConsumptionCodedStepStrictInputDescentSentence w B z o n r l x)) := ZFReplay.replay (packetReaderConsumptionCodedStepStrictInputDescent_kernel_certificate w B z o n r l x)

def packetReaderConsumptionEveryActualHistoryEdgeHasStateCarrierSentence {m} (w B z o n r l d f i N : Fin m) : Source.Sentence := ((omega w).imp ((PacketReaderHistorySyntax.history w B z o n r l d f).imp ((GraphSyntax.edge f i N).imp ((PacketReaderStateSyntax.carrier w N))))).close

theorem source_packetReaderConsumptionEveryActualHistoryEdgeHasStateCarrier {m} (w B z o n r l d f i N : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderConsumptionEveryActualHistoryEdgeHasStateCarrierSentence w B z o n r l d f i N) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (GraphSyntax.edge f i N) (Context.add (PacketReaderHistorySyntax.history w B z o n r l d f) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (PacketReaderHistorySyntax.history w B z o n r l d f) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (GraphSyntax.edge f i N) := .hyp (Or.inl rfl)
  exact PacketReaderHistoryStates.at_edge hZ w B z o n r l d f i N h0 h1 h2

theorem packetReaderConsumptionEveryActualHistoryEdgeHasStateCarrier_kernel_certificate {m} (w B z o n r l d f i N : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderConsumptionEveryActualHistoryEdgeHasStateCarrierSentence w B z o n r l d f i N)) := TheoryTransport.sentence (source_packetReaderConsumptionEveryActualHistoryEdgeHasStateCarrier w B z o n r l d f i N)

theorem native_packetReaderConsumptionEveryActualHistoryEdgeHasStateCarrier {m} (w B z o n r l d f i N : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderConsumptionEveryActualHistoryEdgeHasStateCarrierSentence w B z o n r l d f i N)) := ZFReplay.replay (packetReaderConsumptionEveryActualHistoryEdgeHasStateCarrier_kernel_certificate w B z o n r l d f i N)

def packetReaderConsumptionActualDomainIndexHasUniqueValidInputFiberSentence {m} (w B z o n r l d f i : Fin m) : Source.Sentence := ((omega w).imp ((PacketReaderHistorySyntax.history w B z o n r l d f).imp ((Formula.mem i d).imp ((PacketReaderHistoryInput.fiberAt w f i))))).close

theorem source_packetReaderConsumptionActualDomainIndexHasUniqueValidInputFiber {m} (w B z o n r l d f i : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderConsumptionActualDomainIndexHasUniqueValidInputFiberSentence w B z o n r l d f i) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem i d) (Context.add (PacketReaderHistorySyntax.history w B z o n r l d f) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (PacketReaderHistorySyntax.history w B z o n r l d f) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (Formula.mem i d) := .hyp (Or.inl rfl)
  exact PacketReaderHistoryInput.exists_unique_at hZ w B z o n r l d f i h0 h1 h2

theorem packetReaderConsumptionActualDomainIndexHasUniqueValidInputFiber_kernel_certificate {m} (w B z o n r l d f i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderConsumptionActualDomainIndexHasUniqueValidInputFiberSentence w B z o n r l d f i)) := TheoryTransport.sentence (source_packetReaderConsumptionActualDomainIndexHasUniqueValidInputFiber w B z o n r l d f i)

theorem native_packetReaderConsumptionActualDomainIndexHasUniqueValidInputFiber {m} (w B z o n r l d f i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderConsumptionActualDomainIndexHasUniqueValidInputFiberSentence w B z o n r l d f i)) := ZFReplay.replay (packetReaderConsumptionActualDomainIndexHasUniqueValidInputFiber_kernel_certificate w B z o n r l d f i)

def packetReaderConsumptionInputProjectionExactAtActualEdgeSentence {m} (w f d i n L : Fin m) : Source.Sentence := ((SequenceSyntax.sequence f d w).imp ((GraphSyntax.edge f i n).imp (((PacketReaderConsumptionSyntax.inputAt w f i L).iff (PacketReaderConsumptionSyntax.input w n L))))).close

theorem source_packetReaderConsumptionInputProjectionExactAtActualEdge {m} (w f d i n L : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderConsumptionInputProjectionExactAtActualEdgeSentence w f d i n L) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (GraphSyntax.edge f i n) (Context.add (SequenceSyntax.sequence f d w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (SequenceSyntax.sequence f d w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (GraphSyntax.edge f i n) := .hyp (Or.inl rfl)
  exact PacketReaderHistoryInput.at_edge hZ w f d i n L h0 h1

theorem packetReaderConsumptionInputProjectionExactAtActualEdge_kernel_certificate {m} (w f d i n L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderConsumptionInputProjectionExactAtActualEdgeSentence w f d i n L)) := TheoryTransport.sentence (source_packetReaderConsumptionInputProjectionExactAtActualEdge w f d i n L)

theorem native_packetReaderConsumptionInputProjectionExactAtActualEdge {m} (w f d i n L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderConsumptionInputProjectionExactAtActualEdgeSentence w f d i n L)) := ZFReplay.replay (packetReaderConsumptionInputProjectionExactAtActualEdge_kernel_certificate w f d i n L)

def packetReaderConsumptionActualAdjacentInputsConsumeConsSentence {m} (w B z o n r l d f i j L K : Fin m) : Source.Sentence := ((omega w).imp ((PacketReaderHistorySyntax.history w B z o n r l d f).imp ((Formula.mem i l).imp ((successor j i).imp ((PacketReaderConsumptionSyntax.inputAt w f i L).imp ((PacketReaderConsumptionSyntax.inputAt w f j K).imp ((PacketReaderConsumptionSyntax.tail w L K)))))))).close

theorem source_packetReaderConsumptionActualAdjacentInputsConsumeCons {m} (w B z o n r l d f i j L K : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderConsumptionActualAdjacentInputsConsumeConsSentence w B z o n r l d f i j L K) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderConsumptionSyntax.inputAt w f j K) (Context.add (PacketReaderConsumptionSyntax.inputAt w f i L) (Context.add (successor j i) (Context.add (Formula.mem i l) (Context.add (PacketReaderHistorySyntax.history w B z o n r l d f) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (PacketReaderHistorySyntax.history w B z o n r l d f) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (Formula.mem i l) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (successor j i) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (PacketReaderConsumptionSyntax.inputAt w f i L) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (PacketReaderConsumptionSyntax.inputAt w f j K) := .hyp (Or.inl rfl)
  exact PacketReaderHistoryConsumption.adjacent hZ w B z o n r l d f i j L K h0 h1 h2 h3 h4 h5

theorem packetReaderConsumptionActualAdjacentInputsConsumeCons_kernel_certificate {m} (w B z o n r l d f i j L K : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderConsumptionActualAdjacentInputsConsumeConsSentence w B z o n r l d f i j L K)) := TheoryTransport.sentence (source_packetReaderConsumptionActualAdjacentInputsConsumeCons w B z o n r l d f i j L K)

theorem native_packetReaderConsumptionActualAdjacentInputsConsumeCons {m} (w B z o n r l d f i j L K : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderConsumptionActualAdjacentInputsConsumeConsSentence w B z o n r l d f i j L K)) := ZFReplay.replay (packetReaderConsumptionActualAdjacentInputsConsumeCons_kernel_certificate w B z o n r l d f i j L K)

def packetReaderConsumptionActualAdjacentInputsStrictlyDescendSentence {m} (w B z o n r l d f i j L K : Fin m) : Source.Sentence := ((omega w).imp ((PacketReaderHistorySyntax.history w B z o n r l d f).imp ((Formula.mem i l).imp ((successor j i).imp ((PacketReaderConsumptionSyntax.inputAt w f i L).imp ((PacketReaderConsumptionSyntax.inputAt w f j K).imp ((Formula.mem K L)))))))).close

theorem source_packetReaderConsumptionActualAdjacentInputsStrictlyDescend {m} (w B z o n r l d f i j L K : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderConsumptionActualAdjacentInputsStrictlyDescendSentence w B z o n r l d f i j L K) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderConsumptionSyntax.inputAt w f j K) (Context.add (PacketReaderConsumptionSyntax.inputAt w f i L) (Context.add (successor j i) (Context.add (Formula.mem i l) (Context.add (PacketReaderHistorySyntax.history w B z o n r l d f) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (PacketReaderHistorySyntax.history w B z o n r l d f) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (Formula.mem i l) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (successor j i) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (PacketReaderConsumptionSyntax.inputAt w f i L) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (PacketReaderConsumptionSyntax.inputAt w f j K) := .hyp (Or.inl rfl)
  exact PacketReaderHistoryConsumption.adjacent_strict hZ w B z o n r l d f i j L K h0 h1 h2 h3 h4 h5

theorem packetReaderConsumptionActualAdjacentInputsStrictlyDescend_kernel_certificate {m} (w B z o n r l d f i j L K : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderConsumptionActualAdjacentInputsStrictlyDescendSentence w B z o n r l d f i j L K)) := TheoryTransport.sentence (source_packetReaderConsumptionActualAdjacentInputsStrictlyDescend w B z o n r l d f i j L K)

theorem native_packetReaderConsumptionActualAdjacentInputsStrictlyDescend {m} (w B z o n r l d f i j L K : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderConsumptionActualAdjacentInputsStrictlyDescendSentence w B z o n r l d f i j L K)) := ZFReplay.replay (packetReaderConsumptionActualAdjacentInputsStrictlyDescend_kernel_certificate w B z o n r l d f i j L K)

def packetReaderConsumptionEveryInternalStepHasActualConsumptionWitnessesSentence {m} (w B z o n r l d f i : Fin m) : Source.Sentence := ((omega w).imp ((PacketReaderHistorySyntax.history w B z o n r l d f).imp ((Formula.mem i l).imp ((PacketReaderHistoryConsumption.consumesAt w f i))))).close

theorem source_packetReaderConsumptionEveryInternalStepHasActualConsumptionWitnesses {m} (w B z o n r l d f i : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderConsumptionEveryInternalStepHasActualConsumptionWitnessesSentence w B z o n r l d f i) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem i l) (Context.add (PacketReaderHistorySyntax.history w B z o n r l d f) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (PacketReaderHistorySyntax.history w B z o n r l d f) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (Formula.mem i l) := .hyp (Or.inl rfl)
  exact PacketReaderHistoryConsumption.every_step hZ w B z o n r l d f i h0 h1 h2

theorem packetReaderConsumptionEveryInternalStepHasActualConsumptionWitnesses_kernel_certificate {m} (w B z o n r l d f i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderConsumptionEveryInternalStepHasActualConsumptionWitnessesSentence w B z o n r l d f i)) := TheoryTransport.sentence (source_packetReaderConsumptionEveryInternalStepHasActualConsumptionWitnesses w B z o n r l d f i)

theorem native_packetReaderConsumptionEveryInternalStepHasActualConsumptionWitnesses {m} (w B z o n r l d f i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderConsumptionEveryInternalStepHasActualConsumptionWitnessesSentence w B z o n r l d f i)) := ZFReplay.replay (packetReaderConsumptionEveryInternalStepHasActualConsumptionWitnesses_kernel_certificate w B z o n r l d f i)

def packetReaderConsumptionAllInternalStepConsumptionSentence {m} (w B z o n r l d f : Fin m) : Source.Sentence := ((omega w).imp ((PacketReaderHistorySyntax.history w B z o n r l d f).imp ((PacketReaderHistoryConsumption.allSteps w f l)))).close

theorem source_packetReaderConsumptionAllInternalStepConsumption {m} (w B z o n r l d f : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderConsumptionAllInternalStepConsumptionSentence w B z o n r l d f) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderHistorySyntax.history w B z o n r l d f) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PacketReaderHistorySyntax.history w B z o n r l d f) := .hyp (Or.inl rfl)
  exact PacketReaderHistoryConsumption.all_steps hZ w B z o n r l d f h0 h1

theorem packetReaderConsumptionAllInternalStepConsumption_kernel_certificate {m} (w B z o n r l d f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderConsumptionAllInternalStepConsumptionSentence w B z o n r l d f)) := TheoryTransport.sentence (source_packetReaderConsumptionAllInternalStepConsumption w B z o n r l d f)

theorem native_packetReaderConsumptionAllInternalStepConsumption {m} (w B z o n r l d f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderConsumptionAllInternalStepConsumptionSentence w B z o n r l d f)) := ZFReplay.replay (packetReaderConsumptionAllInternalStepConsumption_kernel_certificate w B z o n r l d f)

def packetReaderConsumptionNilInputForbidsNextCodedStepSentence {m} (w B z o n r L : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem B w).imp ((PacketReaderConsumptionSyntax.input w n L).imp ((StructuralListSyntax.nilCode w L).imp (((PacketReaderCodedSyntax.step w B z o n r).neg)))))).close

theorem source_packetReaderConsumptionNilInputForbidsNextCodedStep {m} (w B z o n r L : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderConsumptionNilInputForbidsNextCodedStepSentence w B z o n r L) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralListSyntax.nilCode w L) (Context.add (PacketReaderConsumptionSyntax.input w n L) (Context.add (Formula.mem B w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (Formula.mem B w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (PacketReaderConsumptionSyntax.input w n L) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (StructuralListSyntax.nilCode w L) := .hyp (Or.inl rfl)
  exact PacketReaderConsumptionStopping.nil_at_input hZ w B z o n r L h0 h1 h2 h3

theorem packetReaderConsumptionNilInputForbidsNextCodedStep_kernel_certificate {m} (w B z o n r L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderConsumptionNilInputForbidsNextCodedStepSentence w B z o n r L)) := TheoryTransport.sentence (source_packetReaderConsumptionNilInputForbidsNextCodedStep w B z o n r L)

theorem native_packetReaderConsumptionNilInputForbidsNextCodedStep {m} (w B z o n r L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderConsumptionNilInputForbidsNextCodedStepSentence w B z o n r L)) := ZFReplay.replay (packetReaderConsumptionNilInputForbidsNextCodedStep_kernel_certificate w B z o n r L)

def packetReaderConsumptionOriginalByteRejectForbidsNextCodedStepSentence {m} (w B z o n r L v s a : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem B w).imp ((PacketReaderStateSyntax.code w L v s a n).imp ((PacketReaderInputSyntax.blocked w B z o L s).imp (((PacketReaderCodedSyntax.step w B z o n r).neg)))))).close

theorem source_packetReaderConsumptionOriginalByteRejectForbidsNextCodedStep {m} (w B z o n r L v s a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderConsumptionOriginalByteRejectForbidsNextCodedStepSentence w B z o n r L v s a) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderInputSyntax.blocked w B z o L s) (Context.add (PacketReaderStateSyntax.code w L v s a n) (Context.add (Formula.mem B w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (Formula.mem B w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (PacketReaderStateSyntax.code w L v s a n) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (PacketReaderInputSyntax.blocked w B z o L s) := .hyp (Or.inl rfl)
  exact PacketReaderConsumptionStopping.blocked_at_code hZ w B z o n r L v s a h0 h1 h2 h3

theorem packetReaderConsumptionOriginalByteRejectForbidsNextCodedStep_kernel_certificate {m} (w B z o n r L v s a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderConsumptionOriginalByteRejectForbidsNextCodedStepSentence w B z o n r L v s a)) := TheoryTransport.sentence (source_packetReaderConsumptionOriginalByteRejectForbidsNextCodedStep w B z o n r L v s a)

theorem native_packetReaderConsumptionOriginalByteRejectForbidsNextCodedStep {m} (w B z o n r L v s a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderConsumptionOriginalByteRejectForbidsNextCodedStepSentence w B z o n r L v s a)) := ZFReplay.replay (packetReaderConsumptionOriginalByteRejectForbidsNextCodedStep_kernel_certificate w B z o n r L v s a)

def packetReaderConsumptionNilInputOccursOnlyAtLastHistoryIndexSentence {m} (w B z o n r l d f i L : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem B w).imp ((PacketReaderHistorySyntax.history w B z o n r l d f).imp ((Formula.mem i d).imp ((PacketReaderConsumptionSyntax.inputAt w f i L).imp ((StructuralListSyntax.nilCode w L).imp ((Formula.equal i l)))))))).close

theorem source_packetReaderConsumptionNilInputOccursOnlyAtLastHistoryIndex {m} (w B z o n r l d f i L : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderConsumptionNilInputOccursOnlyAtLastHistoryIndexSentence w B z o n r l d f i L) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralListSyntax.nilCode w L) (Context.add (PacketReaderConsumptionSyntax.inputAt w f i L) (Context.add (Formula.mem i d) (Context.add (PacketReaderHistorySyntax.history w B z o n r l d f) (Context.add (Formula.mem B w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
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
  have h2 : Derives Δ (PacketReaderHistorySyntax.history w B z o n r l d f) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (Formula.mem i d) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (PacketReaderConsumptionSyntax.inputAt w f i L) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (StructuralListSyntax.nilCode w L) := .hyp (Or.inl rfl)
  exact PacketReaderConsumptionStopping.nil_index_is_last hZ w B z o n r l d f i L h0 h1 h2 h3 h4 h5

theorem packetReaderConsumptionNilInputOccursOnlyAtLastHistoryIndex_kernel_certificate {m} (w B z o n r l d f i L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderConsumptionNilInputOccursOnlyAtLastHistoryIndexSentence w B z o n r l d f i L)) := TheoryTransport.sentence (source_packetReaderConsumptionNilInputOccursOnlyAtLastHistoryIndex w B z o n r l d f i L)

theorem native_packetReaderConsumptionNilInputOccursOnlyAtLastHistoryIndex {m} (w B z o n r l d f i L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderConsumptionNilInputOccursOnlyAtLastHistoryIndexSentence w B z o n r l d f i L)) := ZFReplay.replay (packetReaderConsumptionNilInputOccursOnlyAtLastHistoryIndex_kernel_certificate w B z o n r l d f i L)

def packetReaderConsumptionActualProjectedInputIsNaturalSentence {m} (w f i L : Fin m) : Source.Sentence := ((PacketReaderConsumptionSyntax.inputAt w f i L).imp ((Formula.mem L w))).close

theorem source_packetReaderConsumptionActualProjectedInputIsNatural {m} (w f i L : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderConsumptionActualProjectedInputIsNaturalSentence w f i L) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderConsumptionSyntax.inputAt w f i L) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (PacketReaderConsumptionSyntax.inputAt w f i L) := .hyp (Or.inl rfl)
  exact StructuralListValidity.range w L (PacketReaderHistoryInput.valid_at w f i L h0)

theorem packetReaderConsumptionActualProjectedInputIsNatural_kernel_certificate {m} (w f i L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderConsumptionActualProjectedInputIsNaturalSentence w f i L)) := TheoryTransport.sentence (source_packetReaderConsumptionActualProjectedInputIsNatural w f i L)

theorem native_packetReaderConsumptionActualProjectedInputIsNatural {m} (w f i L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderConsumptionActualProjectedInputIsNaturalSentence w f i L)) := ZFReplay.replay (packetReaderConsumptionActualProjectedInputIsNatural_kernel_certificate w f i L)

end PPAC.Migration.Internal.ObjectPacketReaderConsumption
