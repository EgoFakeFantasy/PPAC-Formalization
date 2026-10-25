import PPAC.Migration.Internal.PacketReaderLengthBounds

/-! Actual remaining lengths, internal conservation, and whole-history bounds. Stopping-history existence, EOF reverse, full reader bridge, Basic AST, Proof and Con remain unproved -/
namespace PPAC.Migration.Internal.ObjectPacketReaderLength
open Source SourceAlgebra SourceLogic OmegaSyntax

def packetReaderLengthActualRemainingLengthNaturalSentence {m} (w f i a : Fin m) : Source.Sentence := ((PacketReaderLengthSyntax.lengthAt w f i a).imp ((Formula.mem a w))).close

theorem source_packetReaderLengthActualRemainingLengthNatural {m} (w f i a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderLengthActualRemainingLengthNaturalSentence w f i a) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderLengthSyntax.lengthAt w f i a) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (PacketReaderLengthSyntax.lengthAt w f i a) := .hyp (Or.inl rfl)
  exact PacketReaderLengthAt.natural w f i a h0

theorem packetReaderLengthActualRemainingLengthNatural_kernel_certificate {m} (w f i a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderLengthActualRemainingLengthNaturalSentence w f i a)) := TheoryTransport.sentence (source_packetReaderLengthActualRemainingLengthNatural w f i a)

theorem native_packetReaderLengthActualRemainingLengthNatural {m} (w f i a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderLengthActualRemainingLengthNaturalSentence w f i a)) := ZFReplay.replay (packetReaderLengthActualRemainingLengthNatural_kernel_certificate w f i a)

def packetReaderLengthActualLengthIndexInHistoryDomainSentence {m} (w f d i a : Fin m) : Source.Sentence := ((SequenceSyntax.sequence f d w).imp ((PacketReaderLengthSyntax.lengthAt w f i a).imp ((Formula.mem i d)))).close

theorem source_packetReaderLengthActualLengthIndexInHistoryDomain {m} (w f d i a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderLengthActualLengthIndexInHistoryDomainSentence w f d i a) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderLengthSyntax.lengthAt w f i a) (Context.add (SequenceSyntax.sequence f d w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (SequenceSyntax.sequence f d w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PacketReaderLengthSyntax.lengthAt w f i a) := .hyp (Or.inl rfl)
  exact PacketReaderLengthAt.domain hZ w f d i a h0 h1

theorem packetReaderLengthActualLengthIndexInHistoryDomain_kernel_certificate {m} (w f d i a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderLengthActualLengthIndexInHistoryDomainSentence w f d i a)) := TheoryTransport.sentence (source_packetReaderLengthActualLengthIndexInHistoryDomain w f d i a)

theorem native_packetReaderLengthActualLengthIndexInHistoryDomain {m} (w f d i a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderLengthActualLengthIndexInHistoryDomainSentence w f d i a)) := ZFReplay.replay (packetReaderLengthActualLengthIndexInHistoryDomain_kernel_certificate w f d i a)

def packetReaderLengthEveryActualHistoryIndexHasLengthSentence {m} (w B z o n r l d f i : Fin m) : Source.Sentence := ((omega w).imp ((PacketReaderHistorySyntax.history w B z o n r l d f).imp ((Formula.mem i d).imp ((PacketReaderLengthSyntax.existsLengthAt w f i))))).close

theorem source_packetReaderLengthEveryActualHistoryIndexHasLength {m} (w B z o n r l d f i : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderLengthEveryActualHistoryIndexHasLengthSentence w B z o n r l d f i) := by
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
  exact PacketReaderLengthAt.exists_at hZ w B z o n r l d f i h0 h1 h2

theorem packetReaderLengthEveryActualHistoryIndexHasLength_kernel_certificate {m} (w B z o n r l d f i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderLengthEveryActualHistoryIndexHasLengthSentence w B z o n r l d f i)) := TheoryTransport.sentence (source_packetReaderLengthEveryActualHistoryIndexHasLength w B z o n r l d f i)

theorem native_packetReaderLengthEveryActualHistoryIndexHasLength {m} (w B z o n r l d f i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderLengthEveryActualHistoryIndexHasLengthSentence w B z o n r l d f i)) := ZFReplay.replay (packetReaderLengthEveryActualHistoryIndexHasLength_kernel_certificate w B z o n r l d f i)

def packetReaderLengthActualRemainingLengthUniqueSentence {m} (w f d i a b : Fin m) : Source.Sentence := ((omega w).imp ((SequenceSyntax.sequence f d w).imp ((PacketReaderLengthSyntax.lengthAt w f i a).imp ((PacketReaderLengthSyntax.lengthAt w f i b).imp ((Formula.equal a b)))))).close

theorem source_packetReaderLengthActualRemainingLengthUnique {m} (w f d i a b : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderLengthActualRemainingLengthUniqueSentence w f d i a b) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderLengthSyntax.lengthAt w f i b) (Context.add (PacketReaderLengthSyntax.lengthAt w f i a) (Context.add (SequenceSyntax.sequence f d w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SequenceSyntax.sequence f d w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (PacketReaderLengthSyntax.lengthAt w f i a) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (PacketReaderLengthSyntax.lengthAt w f i b) := .hyp (Or.inl rfl)
  exact PacketReaderLengthAt.unique hZ w f d i a b h0 h1 h2 h3

theorem packetReaderLengthActualRemainingLengthUnique_kernel_certificate {m} (w f d i a b : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderLengthActualRemainingLengthUniqueSentence w f d i a b)) := TheoryTransport.sentence (source_packetReaderLengthActualRemainingLengthUnique w f d i a b)

theorem native_packetReaderLengthActualRemainingLengthUnique {m} (w f d i a b : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderLengthActualRemainingLengthUniqueSentence w f d i a b)) := ZFReplay.replay (packetReaderLengthActualRemainingLengthUnique_kernel_certificate w f d i a b)

def packetReaderLengthActualConsConsumesOneLengthUnitSentence {m} (w L K a b : Fin m) : Source.Sentence := ((omega w).imp ((PacketReaderConsumptionSyntax.tail w L K).imp ((StructuralListLengthSyntax.hasLength w L a).imp ((StructuralListLengthSyntax.hasLength w K b).imp ((successor a b)))))).close

theorem source_packetReaderLengthActualConsConsumesOneLengthUnit {m} (w L K a b : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderLengthActualConsConsumesOneLengthUnitSentence w L K a b) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralListLengthSyntax.hasLength w K b) (Context.add (StructuralListLengthSyntax.hasLength w L a) (Context.add (PacketReaderConsumptionSyntax.tail w L K) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (PacketReaderConsumptionSyntax.tail w L K) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (StructuralListLengthSyntax.hasLength w L a) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (StructuralListLengthSyntax.hasLength w K b) := .hyp (Or.inl rfl)
  exact PacketReaderTailLength.successor_length hZ w L K a b h0 h1 h2 h3

theorem packetReaderLengthActualConsConsumesOneLengthUnit_kernel_certificate {m} (w L K a b : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderLengthActualConsConsumesOneLengthUnitSentence w L K a b)) := TheoryTransport.sentence (source_packetReaderLengthActualConsConsumesOneLengthUnit w L K a b)

theorem native_packetReaderLengthActualConsConsumesOneLengthUnit {m} (w L K a b : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderLengthActualConsConsumesOneLengthUnitSentence w L K a b)) := ZFReplay.replay (packetReaderLengthActualConsConsumesOneLengthUnit_kernel_certificate w L K a b)

def packetReaderLengthInternalSuccessorConservationTransferSentence {m} (w i j a b N : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem i w).imp ((Formula.mem b w).imp ((successor j i).imp ((successor a b).imp ((NaturalAdditionSyntax.sum w i a N).imp ((NaturalAdditionSyntax.sum w j b N)))))))).close

theorem source_packetReaderLengthInternalSuccessorConservationTransfer {m} (w i j a b N : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderLengthInternalSuccessorConservationTransferSentence w i j a b N) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (NaturalAdditionSyntax.sum w i a N) (Context.add (successor a b) (Context.add (successor j i) (Context.add (Formula.mem b w) (Context.add (Formula.mem i w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (Formula.mem i w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (Formula.mem b w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (successor j i) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (successor a b) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (NaturalAdditionSyntax.sum w i a N) := .hyp (Or.inl rfl)
  exact PacketReaderLengthArithmetic.transfer hZ w i j a b N h0 h1 h2 h3 h4 h5

theorem packetReaderLengthInternalSuccessorConservationTransfer_kernel_certificate {m} (w i j a b N : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderLengthInternalSuccessorConservationTransferSentence w i j a b N)) := TheoryTransport.sentence (source_packetReaderLengthInternalSuccessorConservationTransfer w i j a b N)

theorem native_packetReaderLengthInternalSuccessorConservationTransfer {m} (w i j a b N : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderLengthInternalSuccessorConservationTransferSentence w i j a b N)) := ZFReplay.replay (packetReaderLengthInternalSuccessorConservationTransfer_kernel_certificate w i j a b N)

def packetReaderLengthActualSeedConservationSentence {m} (w B z o n r l d f L N i : Fin m) : Source.Sentence := ((omega w).imp ((PacketReaderHistorySyntax.history w B z o n r l d f).imp ((PacketReaderConsumptionSyntax.input w n L).imp ((StructuralListLengthSyntax.hasLength w L N).imp ((empty i).imp ((PacketReaderLengthSyntax.balance w f N i))))))).close

theorem source_packetReaderLengthActualSeedConservation {m} (w B z o n r l d f L N i : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderLengthActualSeedConservationSentence w B z o n r l d f L N i) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (empty i) (Context.add (StructuralListLengthSyntax.hasLength w L N) (Context.add (PacketReaderConsumptionSyntax.input w n L) (Context.add (PacketReaderHistorySyntax.history w B z o n r l d f) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (PacketReaderHistorySyntax.history w B z o n r l d f) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (PacketReaderConsumptionSyntax.input w n L) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (StructuralListLengthSyntax.hasLength w L N) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (empty i) := .hyp (Or.inl rfl)
  exact PacketReaderLengthPoint.zero_point hZ w B z o n r l d f L N i h0 h1 h2 h3 h4

theorem packetReaderLengthActualSeedConservation_kernel_certificate {m} (w B z o n r l d f L N i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderLengthActualSeedConservationSentence w B z o n r l d f L N i)) := TheoryTransport.sentence (source_packetReaderLengthActualSeedConservation w B z o n r l d f L N i)

theorem native_packetReaderLengthActualSeedConservation {m} (w B z o n r l d f L N i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderLengthActualSeedConservationSentence w B z o n r l d f L N i)) := ZFReplay.replay (packetReaderLengthActualSeedConservation_kernel_certificate w B z o n r l d f L N i)

def packetReaderLengthActualAdjacentLengthsAreSuccessorsSentence {m} (w B z o n r l d f i j a b : Fin m) : Source.Sentence := ((omega w).imp ((PacketReaderHistorySyntax.history w B z o n r l d f).imp ((Formula.mem i l).imp ((successor j i).imp ((PacketReaderLengthSyntax.lengthAt w f i a).imp ((PacketReaderLengthSyntax.lengthAt w f j b).imp ((successor a b)))))))).close

theorem source_packetReaderLengthActualAdjacentLengthsAreSuccessors {m} (w B z o n r l d f i j a b : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderLengthActualAdjacentLengthsAreSuccessorsSentence w B z o n r l d f i j a b) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderLengthSyntax.lengthAt w f j b) (Context.add (PacketReaderLengthSyntax.lengthAt w f i a) (Context.add (successor j i) (Context.add (Formula.mem i l) (Context.add (PacketReaderHistorySyntax.history w B z o n r l d f) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
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
  have h4 : Derives Δ (PacketReaderLengthSyntax.lengthAt w f i a) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (PacketReaderLengthSyntax.lengthAt w f j b) := .hyp (Or.inl rfl)
  exact PacketReaderLengthPoint.adjacent_lengths hZ w B z o n r l d f i j a b h0 h1 h2 h3 h4 h5

theorem packetReaderLengthActualAdjacentLengthsAreSuccessors_kernel_certificate {m} (w B z o n r l d f i j a b : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderLengthActualAdjacentLengthsAreSuccessorsSentence w B z o n r l d f i j a b)) := TheoryTransport.sentence (source_packetReaderLengthActualAdjacentLengthsAreSuccessors w B z o n r l d f i j a b)

theorem native_packetReaderLengthActualAdjacentLengthsAreSuccessors {m} (w B z o n r l d f i j a b : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderLengthActualAdjacentLengthsAreSuccessorsSentence w B z o n r l d f i j a b)) := ZFReplay.replay (packetReaderLengthActualAdjacentLengthsAreSuccessors_kernel_certificate w B z o n r l d f i j a b)

def packetReaderLengthConservationSuccessorPointSentence {m} (w B z o n r l d f N i j : Fin m) : Source.Sentence := ((omega w).imp ((PacketReaderHistorySyntax.history w B z o n r l d f).imp ((PacketReaderLengthSyntax.balance w f N i).imp ((successor j i).imp ((PacketReaderLengthSyntax.balance w f N j)))))).close

theorem source_packetReaderLengthConservationSuccessorPoint {m} (w B z o n r l d f N i j : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderLengthConservationSuccessorPointSentence w B z o n r l d f N i j) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor j i) (Context.add (PacketReaderLengthSyntax.balance w f N i) (Context.add (PacketReaderHistorySyntax.history w B z o n r l d f) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (PacketReaderHistorySyntax.history w B z o n r l d f) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (PacketReaderLengthSyntax.balance w f N i) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (successor j i) := .hyp (Or.inl rfl)
  exact PacketReaderLengthPoint.successor_point hZ w B z o n r l d f N i j h0 h1 h2 h3

theorem packetReaderLengthConservationSuccessorPoint_kernel_certificate {m} (w B z o n r l d f N i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderLengthConservationSuccessorPointSentence w B z o n r l d f N i j)) := TheoryTransport.sentence (source_packetReaderLengthConservationSuccessorPoint w B z o n r l d f N i j)

theorem native_packetReaderLengthConservationSuccessorPoint {m} (w B z o n r l d f N i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderLengthConservationSuccessorPointSentence w B z o n r l d f N i j)) := ZFReplay.replay (packetReaderLengthConservationSuccessorPoint_kernel_certificate w B z o n r l d f N i j)

def packetReaderLengthAllInternalIndicesConservationSentence {m} (w B z o n r l d f L N : Fin m) : Source.Sentence := ((omega w).imp ((PacketReaderHistorySyntax.history w B z o n r l d f).imp ((PacketReaderConsumptionSyntax.input w n L).imp ((StructuralListLengthSyntax.hasLength w L N).imp ((PacketReaderLengthSyntax.allBalance w f N)))))).close

theorem source_packetReaderLengthAllInternalIndicesConservation {m} (w B z o n r l d f L N : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderLengthAllInternalIndicesConservationSentence w B z o n r l d f L N) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralListLengthSyntax.hasLength w L N) (Context.add (PacketReaderConsumptionSyntax.input w n L) (Context.add (PacketReaderHistorySyntax.history w B z o n r l d f) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (PacketReaderHistorySyntax.history w B z o n r l d f) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (PacketReaderConsumptionSyntax.input w n L) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (StructuralListLengthSyntax.hasLength w L N) := .hyp (Or.inl rfl)
  exact PacketReaderLengthInduction.all_balance hZ w B z o n r l d f L N h0 h1 h2 h3

theorem packetReaderLengthAllInternalIndicesConservation_kernel_certificate {m} (w B z o n r l d f L N : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderLengthAllInternalIndicesConservationSentence w B z o n r l d f L N)) := TheoryTransport.sentence (source_packetReaderLengthAllInternalIndicesConservation w B z o n r l d f L N)

theorem native_packetReaderLengthAllInternalIndicesConservation {m} (w B z o n r l d f L N : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderLengthAllInternalIndicesConservationSentence w B z o n r l d f L N)) := ZFReplay.replay (packetReaderLengthAllInternalIndicesConservation_kernel_certificate w B z o n r l d f L N)

def packetReaderLengthActualHistoryIndexBoundSentence {m} (w B z o n r l d f L N i : Fin m) : Source.Sentence := ((omega w).imp ((PacketReaderHistorySyntax.history w B z o n r l d f).imp ((PacketReaderConsumptionSyntax.input w n L).imp ((StructuralListLengthSyntax.hasLength w L N).imp ((Formula.mem i d).imp ((NaturalAdditionBounds.below i N))))))).close

theorem source_packetReaderLengthActualHistoryIndexBound {m} (w B z o n r l d f L N i : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderLengthActualHistoryIndexBoundSentence w B z o n r l d f L N i) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem i d) (Context.add (StructuralListLengthSyntax.hasLength w L N) (Context.add (PacketReaderConsumptionSyntax.input w n L) (Context.add (PacketReaderHistorySyntax.history w B z o n r l d f) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (PacketReaderHistorySyntax.history w B z o n r l d f) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (PacketReaderConsumptionSyntax.input w n L) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (StructuralListLengthSyntax.hasLength w L N) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (Formula.mem i d) := .hyp (Or.inl rfl)
  exact PacketReaderLengthBounds.index_bound hZ w B z o n r l d f L N i h0 h1 h2 h3 h4

theorem packetReaderLengthActualHistoryIndexBound_kernel_certificate {m} (w B z o n r l d f L N i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderLengthActualHistoryIndexBoundSentence w B z o n r l d f L N i)) := TheoryTransport.sentence (source_packetReaderLengthActualHistoryIndexBound w B z o n r l d f L N i)

theorem native_packetReaderLengthActualHistoryIndexBound {m} (w B z o n r l d f L N i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderLengthActualHistoryIndexBoundSentence w B z o n r l d f L N i)) := ZFReplay.replay (packetReaderLengthActualHistoryIndexBound_kernel_certificate w B z o n r l d f L N i)

def packetReaderLengthWholeHistoryLengthBoundSentence {m} (w B z o n r l d f L N : Fin m) : Source.Sentence := ((omega w).imp ((PacketReaderHistorySyntax.history w B z o n r l d f).imp ((PacketReaderConsumptionSyntax.input w n L).imp ((StructuralListLengthSyntax.hasLength w L N).imp ((NaturalAdditionBounds.below l N)))))).close

theorem source_packetReaderLengthWholeHistoryLengthBound {m} (w B z o n r l d f L N : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderLengthWholeHistoryLengthBoundSentence w B z o n r l d f L N) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralListLengthSyntax.hasLength w L N) (Context.add (PacketReaderConsumptionSyntax.input w n L) (Context.add (PacketReaderHistorySyntax.history w B z o n r l d f) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (PacketReaderHistorySyntax.history w B z o n r l d f) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (PacketReaderConsumptionSyntax.input w n L) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (StructuralListLengthSyntax.hasLength w L N) := .hyp (Or.inl rfl)
  exact PacketReaderLengthBounds.history_bound hZ w B z o n r l d f L N h0 h1 h2 h3

theorem packetReaderLengthWholeHistoryLengthBound_kernel_certificate {m} (w B z o n r l d f L N : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderLengthWholeHistoryLengthBoundSentence w B z o n r l d f L N)) := TheoryTransport.sentence (source_packetReaderLengthWholeHistoryLengthBound w B z o n r l d f L N)

theorem native_packetReaderLengthWholeHistoryLengthBound {m} (w B z o n r l d f L N : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderLengthWholeHistoryLengthBoundSentence w B z o n r l d f L N)) := ZFReplay.replay (packetReaderLengthWholeHistoryLengthBound_kernel_certificate w B z o n r l d f L N)

def packetReaderLengthNoTooLongAcceptedHistorySentence {m} (w B z o n r l d f L N : Fin m) : Source.Sentence := ((omega w).imp ((PacketReaderHistorySyntax.history w B z o n r l d f).imp ((PacketReaderConsumptionSyntax.input w n L).imp ((StructuralListLengthSyntax.hasLength w L N).imp (((Formula.mem N l).neg)))))).close

theorem source_packetReaderLengthNoTooLongAcceptedHistory {m} (w B z o n r l d f L N : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderLengthNoTooLongAcceptedHistorySentence w B z o n r l d f L N) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralListLengthSyntax.hasLength w L N) (Context.add (PacketReaderConsumptionSyntax.input w n L) (Context.add (PacketReaderHistorySyntax.history w B z o n r l d f) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (PacketReaderHistorySyntax.history w B z o n r l d f) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (PacketReaderConsumptionSyntax.input w n L) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (StructuralListLengthSyntax.hasLength w L N) := .hyp (Or.inl rfl)
  exact PacketReaderLengthBounds.no_too_long_history hZ w B z o n r l d f L N h0 h1 h2 h3

theorem packetReaderLengthNoTooLongAcceptedHistory_kernel_certificate {m} (w B z o n r l d f L N : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderLengthNoTooLongAcceptedHistorySentence w B z o n r l d f L N)) := TheoryTransport.sentence (source_packetReaderLengthNoTooLongAcceptedHistory w B z o n r l d f L N)

theorem native_packetReaderLengthNoTooLongAcceptedHistory {m} (w B z o n r l d f L N : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderLengthNoTooLongAcceptedHistorySentence w B z o n r l d f L N)) := ZFReplay.replay (packetReaderLengthNoTooLongAcceptedHistory_kernel_certificate w B z o n r l d f L N)

end PPAC.Migration.Internal.ObjectPacketReaderLength
