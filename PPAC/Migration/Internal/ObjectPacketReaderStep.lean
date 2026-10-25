import PPAC.Migration.Internal.PacketReaderStepExistence

/-! Raw reader local step: original low-byte guard, unbounded arithmetic, actual Cons accumulation, state preservation, determinism and exact successor domain. Complete runs, EOF reversal, Basic AST, Proof and Con remain unproved -/
namespace PPAC.Migration.Internal.ObjectPacketReaderStep
open Source SourceAlgebra SourceLogic OmegaSyntax

def packetReaderRawGuardPartitionSentence {m} (w B z o b s : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem B w).imp ((Formula.mem b w).imp ((((PacketReaderStepSyntax.finish B z o b s).disj (PacketReaderStepSyntax.reject B z o b s)).disj (PacketReaderStepSyntax.more B b)))))).close

theorem source_packetReaderRawGuardPartition {m} (w B z o b s : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderRawGuardPartitionSentence w B z o b s) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem b w) (Context.add (Formula.mem B w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (Formula.mem B w) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (Formula.mem b w) := .hyp (Or.inl rfl)
  exact PacketReaderGuards.partition hZ w B z o b s h0 h1 h2

theorem packetReaderRawGuardPartition_kernel_certificate {m} (w B z o b s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderRawGuardPartitionSentence w B z o b s)) := TheoryTransport.sentence (source_packetReaderRawGuardPartition w B z o b s)

theorem native_packetReaderRawGuardPartition {m} (w B z o b s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderRawGuardPartitionSentence w B z o b s)) := ZFReplay.replay (packetReaderRawGuardPartition_kernel_certificate w B z o b s)

def packetReaderTerminalRejectionNoStepSentence {m} (w B z o b x v s a r y q c : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem B w).imp ((PacketReaderStepSyntax.reject B z o b s).imp (((PacketReaderStepSyntax.step w B z o b x v s a r y q c).neg))))).close

theorem source_packetReaderTerminalRejectionNoStep {m} (w B z o b x v s a r y q c : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderTerminalRejectionNoStepSentence w B z o b x v s a r y q c) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderStepSyntax.reject B z o b s) (Context.add (Formula.mem B w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (Formula.mem B w) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (PacketReaderStepSyntax.reject B z o b s) := .hyp (Or.inl rfl)
  exact PacketReaderGuards.reject_no_step hZ w B z o b x v s a r y q c h0 h1 h2

theorem packetReaderTerminalRejectionNoStep_kernel_certificate {m} (w B z o b x v s a r y q c : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderTerminalRejectionNoStepSentence w B z o b x v s a r y q c)) := TheoryTransport.sentence (source_packetReaderTerminalRejectionNoStep w B z o b x v s a r y q c)

theorem native_packetReaderTerminalRejectionNoStep {m} (w B z o b x v s a r y q c : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderTerminalRejectionNoStepSentence w B z o b x v s a r y q c)) := ZFReplay.replay (packetReaderTerminalRejectionNoStep_kernel_certificate w B z o b x v s a r y q c)

def packetReaderEofExactGuardPartitionSentence {m} (z o v s : Fin m) : Source.Sentence := (((PacketReaderStepSyntax.eof z o v s).disj (PacketReaderStepSyntax.eof z o v s).neg)).close

theorem source_packetReaderEofExactGuardPartition {m} (z o v s : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderEofExactGuardPartitionSentence z o v s) := by
  apply close_derives
  let Δ : Context m := Source.SetLanguage.ZF.at m
  exact PacketReaderGuards.eof_partition z o v s

theorem packetReaderEofExactGuardPartition_kernel_certificate {m} (z o v s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderEofExactGuardPartitionSentence z o v s)) := TheoryTransport.sentence (source_packetReaderEofExactGuardPartition z o v s)

theorem native_packetReaderEofExactGuardPartition {m} (z o v s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderEofExactGuardPartitionSentence z o v s)) := ZFReplay.replay (packetReaderEofExactGuardPartition_kernel_certificate z o v s)

def packetReaderUnboundedValueUpdateExistsSentence {m} (w b v s : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem b w).imp ((Formula.mem v w).imp ((Formula.mem s w).imp ((.ex ((Formula.mem (Fin.last m) w.castSucc).conj (PacketAffineSyntax.equation w.castSucc b.castSucc v.castSucc s.castSucc (Fin.last m))))))))).close

theorem source_packetReaderUnboundedValueUpdateExists {m} (w b v s : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderUnboundedValueUpdateExistsSentence w b v s) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem s w) (Context.add (Formula.mem v w) (Context.add (Formula.mem b w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (Formula.mem b w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (Formula.mem v w) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (Formula.mem s w) := .hyp (Or.inl rfl)
  exact PacketReaderArithmetic.exists_equation hZ w b v s h0 h1 h2 h3

theorem packetReaderUnboundedValueUpdateExists_kernel_certificate {m} (w b v s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderUnboundedValueUpdateExistsSentence w b v s)) := TheoryTransport.sentence (source_packetReaderUnboundedValueUpdateExists w b v s)

theorem native_packetReaderUnboundedValueUpdateExists {m} (w b v s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderUnboundedValueUpdateExistsSentence w b v s)) := ZFReplay.replay (packetReaderUnboundedValueUpdateExists_kernel_certificate w b v s)

def packetReaderUnboundedValueUpdateRangeSentence {m} (w b v s y : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem v w).imp ((PacketAffineSyntax.equation w b v s y).imp ((Formula.mem y w))))).close

theorem source_packetReaderUnboundedValueUpdateRange {m} (w b v s y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderUnboundedValueUpdateRangeSentence w b v s y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketAffineSyntax.equation w b v s y) (Context.add (Formula.mem v w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (Formula.mem v w) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (PacketAffineSyntax.equation w b v s y) := .hyp (Or.inl rfl)
  exact PacketReaderArithmetic.equation_range hZ w b v s y h0 h1 h2

theorem packetReaderUnboundedValueUpdateRange_kernel_certificate {m} (w b v s y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderUnboundedValueUpdateRangeSentence w b v s y)) := TheoryTransport.sentence (source_packetReaderUnboundedValueUpdateRange w b v s y)

theorem native_packetReaderUnboundedValueUpdateRange {m} (w b v s y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderUnboundedValueUpdateRangeSentence w b v s y)) := ZFReplay.replay (packetReaderUnboundedValueUpdateRange_kernel_certificate w b v s y)

def packetReaderContinuationExactNaturalDomainSentence {m} (w B b v s y q : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem B w).imp ((Formula.mem v w).imp ((PacketReaderStepSyntax.continuation w B b v s y q).imp (((PacketReaderStepSyntax.more B b).conj ((Formula.mem y w).conj (.mem q w)))))))).close

theorem source_packetReaderContinuationExactNaturalDomain {m} (w B b v s y q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderContinuationExactNaturalDomainSentence w B b v s y q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderStepSyntax.continuation w B b v s y q) (Context.add (Formula.mem v w) (Context.add (Formula.mem B w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (Formula.mem B w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (Formula.mem v w) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (PacketReaderStepSyntax.continuation w B b v s y q) := .hyp (Or.inl rfl)
  exact PacketReaderContinuation.domain hZ w B b v s y q h0 h1 h2 h3

theorem packetReaderContinuationExactNaturalDomain_kernel_certificate {m} (w B b v s y q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderContinuationExactNaturalDomainSentence w B b v s y q)) := TheoryTransport.sentence (source_packetReaderContinuationExactNaturalDomain w B b v s y q)

theorem native_packetReaderContinuationExactNaturalDomain {m} (w B b v s y q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderContinuationExactNaturalDomainSentence w B b v s y q)) := ZFReplay.replay (packetReaderContinuationExactNaturalDomain_kernel_certificate w B b v s y q)

def packetReaderContinuationJointUniqueSentence {m} (w B b v s y q t u : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem B w).imp ((Formula.mem s w).imp ((PacketReaderStepSyntax.continuation w B b v s y q).imp ((PacketReaderStepSyntax.continuation w B b v s t u).imp (((Formula.equal y t).conj (.equal q u)))))))).close

theorem source_packetReaderContinuationJointUnique {m} (w B b v s y q t u : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderContinuationJointUniqueSentence w B b v s y q t u) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderStepSyntax.continuation w B b v s t u) (Context.add (PacketReaderStepSyntax.continuation w B b v s y q) (Context.add (Formula.mem s w) (Context.add (Formula.mem B w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (Formula.mem B w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (Formula.mem s w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (PacketReaderStepSyntax.continuation w B b v s y q) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (PacketReaderStepSyntax.continuation w B b v s t u) := .hyp (Or.inl rfl)
  exact PacketReaderContinuation.unique hZ w B b v s y q t u h0 h1 h2 h3 h4

theorem packetReaderContinuationJointUnique_kernel_certificate {m} (w B b v s y q t u : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderContinuationJointUniqueSentence w B b v s y q t u)) := TheoryTransport.sentence (source_packetReaderContinuationJointUnique w B b v s y q t u)

theorem native_packetReaderContinuationJointUnique {m} (w B b v s y q t u : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderContinuationJointUniqueSentence w B b v s y q t u)) := ZFReplay.replay (packetReaderContinuationJointUnique_kernel_certificate w B b v s y q t u)

def packetReaderContinuationActualExistsSentence {m} (w B b v s : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem B w).imp ((Formula.mem b w).imp ((Formula.mem v w).imp ((Formula.mem s w).imp ((PacketReaderStepSyntax.more B b).imp ((PacketReaderContinuation.existsResult w B b v s)))))))).close

theorem source_packetReaderContinuationActualExists {m} (w B b v s : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderContinuationActualExistsSentence w B b v s) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderStepSyntax.more B b) (Context.add (Formula.mem s w) (Context.add (Formula.mem v w) (Context.add (Formula.mem b w) (Context.add (Formula.mem B w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
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
  have h2 : Derives Δ (Formula.mem b w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (Formula.mem v w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (Formula.mem s w) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (PacketReaderStepSyntax.more B b) := .hyp (Or.inl rfl)
  exact PacketReaderContinuation.exists_update hZ w B b v s h0 h1 h2 h3 h4 h5

theorem packetReaderContinuationActualExists_kernel_certificate {m} (w B b v s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderContinuationActualExistsSentence w B b v s)) := TheoryTransport.sentence (source_packetReaderContinuationActualExists w B b v s)

theorem native_packetReaderContinuationActualExists {m} (w B b v s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderContinuationActualExistsSentence w B b v s)) := ZFReplay.replay (packetReaderContinuationActualExists_kernel_certificate w B b v s)

def packetReaderEmissionActualConsExistsSentence {m} (w b v s a : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem b w).imp ((Formula.mem v w).imp ((Formula.mem s w).imp ((StructuralListTraceSyntax.valid w a).imp ((PacketReaderEmission.existsResult w b v s a))))))).close

theorem source_packetReaderEmissionActualConsExists {m} (w b v s a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderEmissionActualConsExistsSentence w b v s a) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralListTraceSyntax.valid w a) (Context.add (Formula.mem s w) (Context.add (Formula.mem v w) (Context.add (Formula.mem b w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (Formula.mem b w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (Formula.mem v w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (Formula.mem s w) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (StructuralListTraceSyntax.valid w a) := .hyp (Or.inl rfl)
  exact PacketReaderEmission.exists_emission hZ w b v s a h0 h1 h2 h3 h4

theorem packetReaderEmissionActualConsExists_kernel_certificate {m} (w b v s a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderEmissionActualConsExistsSentence w b v s a)) := TheoryTransport.sentence (source_packetReaderEmissionActualConsExists w b v s a)

theorem native_packetReaderEmissionActualConsExists {m} (w b v s a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderEmissionActualConsExistsSentence w b v s a)) := ZFReplay.replay (packetReaderEmissionActualConsExists_kernel_certificate w b v s a)

def packetReaderEmissionActualConsUniqueSentence {m} (w b v s a c d : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem b w).imp ((Formula.mem v w).imp ((Formula.mem s w).imp ((Formula.mem a w).imp ((PacketReaderStepSyntax.emission w b v s a c).imp ((PacketReaderStepSyntax.emission w b v s a d).imp ((Formula.equal c d))))))))).close

theorem source_packetReaderEmissionActualConsUnique {m} (w b v s a c d : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderEmissionActualConsUniqueSentence w b v s a c d) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderStepSyntax.emission w b v s a d) (Context.add (PacketReaderStepSyntax.emission w b v s a c) (Context.add (Formula.mem a w) (Context.add (Formula.mem s w) (Context.add (Formula.mem v w) (Context.add (Formula.mem b w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))
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
  have h1 : Derives Δ (Formula.mem b w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h2 : Derives Δ (Formula.mem v w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h3 : Derives Δ (Formula.mem s w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : Derives Δ (Formula.mem a w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h5 : Derives Δ (PacketReaderStepSyntax.emission w b v s a c) := .hyp (Or.inr (Or.inl rfl))
  have h6 : Derives Δ (PacketReaderStepSyntax.emission w b v s a d) := .hyp (Or.inl rfl)
  exact PacketReaderEmission.unique hZ w b v s a c d h0 h1 h2 h3 h4 h5 h6

theorem packetReaderEmissionActualConsUnique_kernel_certificate {m} (w b v s a c d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderEmissionActualConsUniqueSentence w b v s a c d)) := TheoryTransport.sentence (source_packetReaderEmissionActualConsUnique w b v s a c d)

theorem native_packetReaderEmissionActualConsUnique {m} (w b v s a c d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderEmissionActualConsUniqueSentence w b v s a c d)) := ZFReplay.replay (packetReaderEmissionActualConsUnique_kernel_certificate w b v s a c d)

def packetReaderEmissionValidAccumulatorSentence {m} (w b v s a c : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem v w).imp ((StructuralListTraceSyntax.valid w a).imp ((PacketReaderStepSyntax.emission w b v s a c).imp ((StructuralListTraceSyntax.valid w c)))))).close

theorem source_packetReaderEmissionValidAccumulator {m} (w b v s a c : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderEmissionValidAccumulatorSentence w b v s a c) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderStepSyntax.emission w b v s a c) (Context.add (StructuralListTraceSyntax.valid w a) (Context.add (Formula.mem v w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (Formula.mem v w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (StructuralListTraceSyntax.valid w a) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (PacketReaderStepSyntax.emission w b v s a c) := .hyp (Or.inl rfl)
  exact PacketReaderEmission.domain hZ w b v s a c h0 h1 h2 h3

theorem packetReaderEmissionValidAccumulator_kernel_certificate {m} (w b v s a c : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderEmissionValidAccumulatorSentence w b v s a c)) := TheoryTransport.sentence (source_packetReaderEmissionValidAccumulator w b v s a c)

theorem native_packetReaderEmissionValidAccumulator {m} (w b v s a c : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderEmissionValidAccumulatorSentence w b v s a c)) := ZFReplay.replay (packetReaderEmissionValidAccumulator_kernel_certificate w b v s a c)

def packetReaderLocalStepStatePreservedSentence {m} (w B z o b x v s a r y q c : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem B w).imp ((Formula.mem z w).imp ((Formula.mem o w).imp ((PacketReaderStepSyntax.state w x v s a).imp ((PacketReaderStepSyntax.step w B z o b x v s a r y q c).imp ((PacketReaderStepSyntax.state w r y q c)))))))).close

theorem source_packetReaderLocalStepStatePreserved {m} (w B z o b x v s a r y q c : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderLocalStepStatePreservedSentence w B z o b x v s a r y q c) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderStepSyntax.step w B z o b x v s a r y q c) (Context.add (PacketReaderStepSyntax.state w x v s a) (Context.add (Formula.mem o w) (Context.add (Formula.mem z w) (Context.add (Formula.mem B w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
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
  have h4 : Derives Δ (PacketReaderStepSyntax.state w x v s a) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (PacketReaderStepSyntax.step w B z o b x v s a r y q c) := .hyp (Or.inl rfl)
  exact PacketReaderStep.domain hZ w B z o b x v s a r y q c h0 h1 h2 h3 h4 h5

theorem packetReaderLocalStepStatePreserved_kernel_certificate {m} (w B z o b x v s a r y q c : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderLocalStepStatePreservedSentence w B z o b x v s a r y q c)) := TheoryTransport.sentence (source_packetReaderLocalStepStatePreserved w B z o b x v s a r y q c)

theorem native_packetReaderLocalStepStatePreserved {m} (w B z o b x v s a r y q c : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderLocalStepStatePreservedSentence w B z o b x v s a r y q c)) := ZFReplay.replay (packetReaderLocalStepStatePreserved_kernel_certificate w B z o b x v s a r y q c)

def packetReaderLocalStepJointUniqueSentence {m} (w B z o b x v s a r y q c t j k d : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem B w).imp ((Formula.mem b w).imp ((PacketReaderStepSyntax.state w x v s a).imp ((PacketReaderStepSyntax.step w B z o b x v s a r y q c).imp ((PacketReaderStepSyntax.step w B z o b x v s a t j k d).imp ((PacketReaderStep.same r y q c t j k d)))))))).close

theorem source_packetReaderLocalStepJointUnique {m} (w B z o b x v s a r y q c t j k d : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderLocalStepJointUniqueSentence w B z o b x v s a r y q c t j k d) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderStepSyntax.step w B z o b x v s a t j k d) (Context.add (PacketReaderStepSyntax.step w B z o b x v s a r y q c) (Context.add (PacketReaderStepSyntax.state w x v s a) (Context.add (Formula.mem b w) (Context.add (Formula.mem B w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
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
  have h2 : Derives Δ (Formula.mem b w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (PacketReaderStepSyntax.state w x v s a) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (PacketReaderStepSyntax.step w B z o b x v s a r y q c) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (PacketReaderStepSyntax.step w B z o b x v s a t j k d) := .hyp (Or.inl rfl)
  exact PacketReaderStep.unique hZ w B z o b x v s a r y q c t j k d h0 h1 h2 h3 h4 h5

theorem packetReaderLocalStepJointUnique_kernel_certificate {m} (w B z o b x v s a r y q c t j k d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderLocalStepJointUniqueSentence w B z o b x v s a r y q c t j k d)) := TheoryTransport.sentence (source_packetReaderLocalStepJointUnique w B z o b x v s a r y q c t j k d)

theorem native_packetReaderLocalStepJointUnique {m} (w B z o b x v s a r y q c t j k d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderLocalStepJointUniqueSentence w B z o b x v s a r y q c t j k d)) := ZFReplay.replay (packetReaderLocalStepJointUnique_kernel_certificate w B z o b x v s a r y q c t j k d)

def packetReaderLocalStepExactSuccessorDomainSentence {m} (w B z o b x v s a : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem B w).imp ((Formula.mem z w).imp ((Formula.mem o w).imp ((Formula.mem b w).imp ((PacketReaderStepSyntax.state w x v s a).imp (((PacketReaderStepExistence.existsResult w B z o b x v s a).iff (PacketReaderStepSyntax.reject B z o b s).neg)))))))).close

theorem source_packetReaderLocalStepExactSuccessorDomain {m} (w B z o b x v s a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderLocalStepExactSuccessorDomainSentence w B z o b x v s a) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderStepSyntax.state w x v s a) (Context.add (Formula.mem b w) (Context.add (Formula.mem o w) (Context.add (Formula.mem z w) (Context.add (Formula.mem B w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
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
  have h4 : Derives Δ (Formula.mem b w) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (PacketReaderStepSyntax.state w x v s a) := .hyp (Or.inl rfl)
  exact PacketReaderStepExistence.domain_iff hZ w B z o b x v s a h0 h1 h2 h3 h4 h5

theorem packetReaderLocalStepExactSuccessorDomain_kernel_certificate {m} (w B z o b x v s a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderLocalStepExactSuccessorDomainSentence w B z o b x v s a)) := TheoryTransport.sentence (source_packetReaderLocalStepExactSuccessorDomain w B z o b x v s a)

theorem native_packetReaderLocalStepExactSuccessorDomain {m} (w B z o b x v s a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderLocalStepExactSuccessorDomainSentence w B z o b x v s a)) := ZFReplay.replay (packetReaderLocalStepExactSuccessorDomain_kernel_certificate w B z o b x v s a)

def packetReaderOriginalLiteralLocalSuccessorDomainSentence {m} (w B z o b x v s a : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 128 B).imp ((SyntaxNumeralSyntax.numeral 0 z).imp ((SyntaxNumeralSyntax.numeral 1 o).imp ((Formula.mem b w).imp ((PacketReaderStepSyntax.state w x v s a).imp (((PacketReaderStepExistence.existsResult w B z o b x v s a).iff (PacketReaderStepSyntax.reject B z o b s).neg)))))))).close

theorem source_packetReaderOriginalLiteralLocalSuccessorDomain {m} (w B z o b x v s a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderOriginalLiteralLocalSuccessorDomainSentence w B z o b x v s a) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderStepSyntax.state w x v s a) (Context.add (Formula.mem b w) (Context.add (SyntaxNumeralSyntax.numeral 1 o) (Context.add (SyntaxNumeralSyntax.numeral 0 z) (Context.add (SyntaxNumeralSyntax.numeral 128 B) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 128 B) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral 0 z) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (SyntaxNumeralSyntax.numeral 1 o) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (Formula.mem b w) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (PacketReaderStepSyntax.state w x v s a) := .hyp (Or.inl rfl)
  exact PacketReaderStepExistence.domain_iff hZ w B z o b x v s a h0 (SyntaxNumerals.range hZ 128 w B h0 h1) (SyntaxNumerals.range hZ 0 w z h0 h2) (SyntaxNumerals.range hZ 1 w o h0 h3) h4 h5

theorem packetReaderOriginalLiteralLocalSuccessorDomain_kernel_certificate {m} (w B z o b x v s a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderOriginalLiteralLocalSuccessorDomainSentence w B z o b x v s a)) := TheoryTransport.sentence (source_packetReaderOriginalLiteralLocalSuccessorDomain w B z o b x v s a)

theorem native_packetReaderOriginalLiteralLocalSuccessorDomain {m} (w B z o b x v s a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderOriginalLiteralLocalSuccessorDomainSentence w B z o b x v s a)) := ZFReplay.replay (packetReaderOriginalLiteralLocalSuccessorDomain_kernel_certificate w B z o b x v s a)

end PPAC.Migration.Internal.ObjectPacketReaderStep
