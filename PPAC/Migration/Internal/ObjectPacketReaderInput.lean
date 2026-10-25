import PPAC.Migration.Internal.PacketReaderInputOutcomes

/-! Complete raw reader input binding, exact single-step graph and four-way dispatch are object derived. Whole runs, actual EOF reverse, Basic AST, Proof and Con remain unproved -/
namespace PPAC.Migration.Internal.ObjectPacketReaderInput
open Source SourceAlgebra SourceLogic OmegaSyntax

def packetReaderInputActualConsFieldsUniqueSentence {m} (w l b x d t : Fin m) : Source.Sentence := ((omega w).imp ((PacketReaderInputSyntax.headRest w l b x).imp ((PacketReaderInputSyntax.headRest w l d t).imp (((Formula.equal b d).conj (.equal x t)))))).close

theorem source_packetReaderInputActualConsFieldsUnique {m} (w l b x d t : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderInputActualConsFieldsUniqueSentence w l b x d t) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderInputSyntax.headRest w l d t) (Context.add (PacketReaderInputSyntax.headRest w l b x) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (PacketReaderInputSyntax.headRest w l b x) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (PacketReaderInputSyntax.headRest w l d t) := .hyp (Or.inl rfl)
  exact PacketReaderInputFields.unique hZ w l b x d t h0 h1 h2

theorem packetReaderInputActualConsFieldsUnique_kernel_certificate {m} (w l b x d t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderInputActualConsFieldsUniqueSentence w l b x d t)) := TheoryTransport.sentence (source_packetReaderInputActualConsFieldsUnique w l b x d t)

theorem native_packetReaderInputActualConsFieldsUnique {m} (w l b x d t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderInputActualConsFieldsUniqueSentence w l b x d t)) := ZFReplay.replay (packetReaderInputActualConsFieldsUnique_kernel_certificate w l b x d t)

def packetReaderInputFullValidNilConsDecompositionSentence {m} (w l : Fin m) : Source.Sentence := ((omega w).imp ((StructuralListTraceSyntax.valid w l).imp (((StructuralListSyntax.nilCode w l).disj (PacketReaderInputSyntax.hasHead w l))))).close

theorem source_packetReaderInputFullValidNilConsDecomposition {m} (w l : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderInputFullValidNilConsDecompositionSentence w l) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralListTraceSyntax.valid w l) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (StructuralListTraceSyntax.valid w l) := .hyp (Or.inl rfl)
  exact PacketReaderInputFields.decomposition hZ w l h0 h1

theorem packetReaderInputFullValidNilConsDecomposition_kernel_certificate {m} (w l : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderInputFullValidNilConsDecompositionSentence w l)) := TheoryTransport.sentence (source_packetReaderInputFullValidNilConsDecomposition w l)

theorem native_packetReaderInputFullValidNilConsDecomposition {m} (w l : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderInputFullValidNilConsDecompositionSentence w l)) := ZFReplay.replay (packetReaderInputFullValidNilConsDecomposition_kernel_certificate w l)

def packetReaderInputActualConsStepExactSentence {m} (w B z o l v s a r y q c b x : Fin m) : Source.Sentence := ((omega w).imp ((PacketReaderInputSyntax.headRest w l b x).imp (((PacketReaderInputSyntax.advance w B z o l v s a r y q c).iff ((PacketReaderStepSyntax.state w l v s a).conj (PacketReaderStepSyntax.step w B z o b x v s a r y q c)))))).close

theorem source_packetReaderInputActualConsStepExact {m} (w B z o l v s a r y q c b x : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderInputActualConsStepExactSentence w B z o l v s a r y q c b x) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderInputSyntax.headRest w l b x) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PacketReaderInputSyntax.headRest w l b x) := .hyp (Or.inl rfl)
  exact PacketReaderInputNormalize.at_cons hZ w B z o l v s a r y q c b x h0 h1

theorem packetReaderInputActualConsStepExact_kernel_certificate {m} (w B z o l v s a r y q c b x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderInputActualConsStepExactSentence w B z o l v s a r y q c b x)) := TheoryTransport.sentence (source_packetReaderInputActualConsStepExact w B z o l v s a r y q c b x)

theorem native_packetReaderInputActualConsStepExact {m} (w B z o l v s a r y q c b x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderInputActualConsStepExactSentence w B z o l v s a r y q c b x)) := ZFReplay.replay (packetReaderInputActualConsStepExact_kernel_certificate w B z o l v s a r y q c b x)

def packetReaderInputActualConsRejectExactSentence {m} (w B z o l s b x : Fin m) : Source.Sentence := ((omega w).imp ((PacketReaderInputSyntax.headRest w l b x).imp (((PacketReaderInputSyntax.blocked w B z o l s).iff (PacketReaderStepSyntax.reject B z o b s))))).close

theorem source_packetReaderInputActualConsRejectExact {m} (w B z o l s b x : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderInputActualConsRejectExactSentence w B z o l s b x) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderInputSyntax.headRest w l b x) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PacketReaderInputSyntax.headRest w l b x) := .hyp (Or.inl rfl)
  exact PacketReaderInputNormalize.blocked_at_cons hZ w B z o l s b x h0 h1

theorem packetReaderInputActualConsRejectExact_kernel_certificate {m} (w B z o l s b x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderInputActualConsRejectExactSentence w B z o l s b x)) := TheoryTransport.sentence (source_packetReaderInputActualConsRejectExact w B z o l s b x)

theorem native_packetReaderInputActualConsRejectExact {m} (w B z o l s b x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderInputActualConsRejectExactSentence w B z o l s b x)) := ZFReplay.replay (packetReaderInputActualConsRejectExact_kernel_certificate w B z o l s b x)

def packetReaderInputNilNoAdvanceSentence {m} (w B z o l v s a r y q c : Fin m) : Source.Sentence := ((omega w).imp ((StructuralListSyntax.nilCode w l).imp (((PacketReaderInputSyntax.advance w B z o l v s a r y q c).neg)))).close

theorem source_packetReaderInputNilNoAdvance {m} (w B z o l v s a r y q c : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderInputNilNoAdvanceSentence w B z o l v s a r y q c) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralListSyntax.nilCode w l) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (StructuralListSyntax.nilCode w l) := .hyp (Or.inl rfl)
  exact PacketReaderInputNormalize.nil_no_advance hZ w B z o l v s a r y q c h0 h1

theorem packetReaderInputNilNoAdvance_kernel_certificate {m} (w B z o l v s a r y q c : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderInputNilNoAdvanceSentence w B z o l v s a r y q c)) := TheoryTransport.sentence (source_packetReaderInputNilNoAdvance w B z o l v s a r y q c)

theorem native_packetReaderInputNilNoAdvance {m} (w B z o l v s a r y q c : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderInputNilNoAdvanceSentence w B z o l v s a r y q c)) := ZFReplay.replay (packetReaderInputNilNoAdvance_kernel_certificate w B z o l v s a r y q c)

def packetReaderInputNilNoByteRejectSentence {m} (w B z o l s : Fin m) : Source.Sentence := ((omega w).imp ((StructuralListSyntax.nilCode w l).imp (((PacketReaderInputSyntax.blocked w B z o l s).neg)))).close

theorem source_packetReaderInputNilNoByteReject {m} (w B z o l s : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderInputNilNoByteRejectSentence w B z o l s) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralListSyntax.nilCode w l) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (StructuralListSyntax.nilCode w l) := .hyp (Or.inl rfl)
  exact PacketReaderInputNormalize.nil_no_blocked hZ w B z o l s h0 h1

theorem packetReaderInputNilNoByteReject_kernel_certificate {m} (w B z o l s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderInputNilNoByteRejectSentence w B z o l s)) := TheoryTransport.sentence (source_packetReaderInputNilNoByteReject w B z o l s)

theorem native_packetReaderInputNilNoByteReject {m} (w B z o l s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderInputNilNoByteRejectSentence w B z o l s)) := ZFReplay.replay (packetReaderInputNilNoByteReject_kernel_certificate w B z o l s)

def packetReaderInputCompleteStatePreservedSentence {m} (w B z o l v s a r y q c : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem B w).imp ((Formula.mem z w).imp ((Formula.mem o w).imp ((PacketReaderInputSyntax.advance w B z o l v s a r y q c).imp ((PacketReaderStepSyntax.state w r y q c))))))).close

theorem source_packetReaderInputCompleteStatePreserved {m} (w B z o l v s a r y q c : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderInputCompleteStatePreservedSentence w B z o l v s a r y q c) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderInputSyntax.advance w B z o l v s a r y q c) (Context.add (Formula.mem o w) (Context.add (Formula.mem z w) (Context.add (Formula.mem B w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
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
  have h4 : Derives Δ (PacketReaderInputSyntax.advance w B z o l v s a r y q c) := .hyp (Or.inl rfl)
  exact PacketReaderInputStep.domain hZ w B z o l v s a r y q c h0 h1 h2 h3 h4

theorem packetReaderInputCompleteStatePreserved_kernel_certificate {m} (w B z o l v s a r y q c : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderInputCompleteStatePreservedSentence w B z o l v s a r y q c)) := TheoryTransport.sentence (source_packetReaderInputCompleteStatePreserved w B z o l v s a r y q c)

theorem native_packetReaderInputCompleteStatePreserved {m} (w B z o l v s a r y q c : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderInputCompleteStatePreservedSentence w B z o l v s a r y q c)) := ZFReplay.replay (packetReaderInputCompleteStatePreserved_kernel_certificate w B z o l v s a r y q c)

def packetReaderInputCompleteStepJointUniqueSentence {m} (w B z o l v s a r y q c t j k d : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem B w).imp ((PacketReaderInputSyntax.advance w B z o l v s a r y q c).imp ((PacketReaderInputSyntax.advance w B z o l v s a t j k d).imp ((PacketReaderStep.same r y q c t j k d)))))).close

theorem source_packetReaderInputCompleteStepJointUnique {m} (w B z o l v s a r y q c t j k d : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderInputCompleteStepJointUniqueSentence w B z o l v s a r y q c t j k d) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderInputSyntax.advance w B z o l v s a t j k d) (Context.add (PacketReaderInputSyntax.advance w B z o l v s a r y q c) (Context.add (Formula.mem B w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (Formula.mem B w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (PacketReaderInputSyntax.advance w B z o l v s a r y q c) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (PacketReaderInputSyntax.advance w B z o l v s a t j k d) := .hyp (Or.inl rfl)
  exact PacketReaderInputStep.unique hZ w B z o l v s a r y q c t j k d h0 h1 h2 h3

theorem packetReaderInputCompleteStepJointUnique_kernel_certificate {m} (w B z o l v s a r y q c t j k d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderInputCompleteStepJointUniqueSentence w B z o l v s a r y q c t j k d)) := TheoryTransport.sentence (source_packetReaderInputCompleteStepJointUnique w B z o l v s a r y q c t j k d)

theorem native_packetReaderInputCompleteStepJointUnique {m} (w B z o l v s a r y q c t j k d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderInputCompleteStepJointUniqueSentence w B z o l v s a r y q c t j k d)) := ZFReplay.replay (packetReaderInputCompleteStepJointUnique_kernel_certificate w B z o l v s a r y q c t j k d)

def packetReaderInputInvalidStateRejectedSentence {m} (w B z o l v s a r y q c : Fin m) : Source.Sentence := (((PacketReaderStepSyntax.state w l v s a).neg).imp (((PacketReaderInputSyntax.advance w B z o l v s a r y q c).neg))).close

theorem source_packetReaderInputInvalidStateRejected {m} (w B z o l v s a r y q c : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderInputInvalidStateRejectedSentence w B z o l v s a r y q c) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add ((PacketReaderStepSyntax.state w l v s a).neg) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ ((PacketReaderStepSyntax.state w l v s a).neg) := .hyp (Or.inl rfl)
  exact PacketReaderInputStep.invalid_state_no_advance w B z o l v s a r y q c h0

theorem packetReaderInputInvalidStateRejected_kernel_certificate {m} (w B z o l v s a r y q c : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderInputInvalidStateRejectedSentence w B z o l v s a r y q c)) := TheoryTransport.sentence (source_packetReaderInputInvalidStateRejected w B z o l v s a r y q c)

theorem native_packetReaderInputInvalidStateRejected {m} (w B z o l v s a r y q c : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderInputInvalidStateRejectedSentence w B z o l v s a r y q c)) := ZFReplay.replay (packetReaderInputInvalidStateRejected_kernel_certificate w B z o l v s a r y q c)

def packetReaderInputCompleteExactSuccessorDomainSentence {m} (w B z o l v s a : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem B w).imp ((Formula.mem z w).imp ((Formula.mem o w).imp (((PacketReaderInputSyntax.existsResult w B z o l v s a).iff (PacketReaderInputExistence.admissible w B z o l v s a))))))).close

theorem source_packetReaderInputCompleteExactSuccessorDomain {m} (w B z o l v s a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderInputCompleteExactSuccessorDomainSentence w B z o l v s a) := by
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
  exact PacketReaderInputExistence.domain_iff hZ w B z o l v s a h0 h1 h2 h3

theorem packetReaderInputCompleteExactSuccessorDomain_kernel_certificate {m} (w B z o l v s a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderInputCompleteExactSuccessorDomainSentence w B z o l v s a)) := TheoryTransport.sentence (source_packetReaderInputCompleteExactSuccessorDomain w B z o l v s a)

theorem native_packetReaderInputCompleteExactSuccessorDomain {m} (w B z o l v s a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderInputCompleteExactSuccessorDomainSentence w B z o l v s a)) := ZFReplay.replay (packetReaderInputCompleteExactSuccessorDomain_kernel_certificate w B z o l v s a)

def packetReaderInputFourWayExactStateDomainSentence {m} (w B z o l v s a : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem B w).imp ((Formula.mem z w).imp ((Formula.mem o w).imp (((PacketReaderInputOutcomes.outcome w B z o l v s a).iff (PacketReaderStepSyntax.state w l v s a))))))).close

theorem source_packetReaderInputFourWayExactStateDomain {m} (w B z o l v s a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderInputFourWayExactStateDomainSentence w B z o l v s a) := by
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
  exact PacketReaderInputOutcomes.outcome_iff hZ w B z o l v s a h0 h1 h2 h3

theorem packetReaderInputFourWayExactStateDomain_kernel_certificate {m} (w B z o l v s a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderInputFourWayExactStateDomainSentence w B z o l v s a)) := TheoryTransport.sentence (source_packetReaderInputFourWayExactStateDomain w B z o l v s a)

theorem native_packetReaderInputFourWayExactStateDomain {m} (w B z o l v s a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderInputFourWayExactStateDomainSentence w B z o l v s a)) := ZFReplay.replay (packetReaderInputFourWayExactStateDomain_kernel_certificate w B z o l v s a)

def packetReaderInputNilNoSuccessorSentence {m} (w B z o l v s a : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem B w).imp ((StructuralListSyntax.nilCode w l).imp (((PacketReaderInputSyntax.existsResult w B z o l v s a).neg))))).close

theorem source_packetReaderInputNilNoSuccessor {m} (w B z o l v s a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderInputNilNoSuccessorSentence w B z o l v s a) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralListSyntax.nilCode w l) (Context.add (Formula.mem B w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (Formula.mem B w) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (StructuralListSyntax.nilCode w l) := .hyp (Or.inl rfl)
  exact PacketReaderInputOutcomes.nil_no_result hZ w B z o l v s a h0 h1 h2

theorem packetReaderInputNilNoSuccessor_kernel_certificate {m} (w B z o l v s a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderInputNilNoSuccessorSentence w B z o l v s a)) := TheoryTransport.sentence (source_packetReaderInputNilNoSuccessor w B z o l v s a)

theorem native_packetReaderInputNilNoSuccessor {m} (w B z o l v s a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderInputNilNoSuccessorSentence w B z o l v s a)) := ZFReplay.replay (packetReaderInputNilNoSuccessor_kernel_certificate w B z o l v s a)

def packetReaderInputByteRejectNoSuccessorSentence {m} (w B z o l v s a : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem B w).imp ((PacketReaderInputSyntax.blocked w B z o l s).imp (((PacketReaderInputSyntax.existsResult w B z o l v s a).neg))))).close

theorem source_packetReaderInputByteRejectNoSuccessor {m} (w B z o l v s a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderInputByteRejectNoSuccessorSentence w B z o l v s a) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderInputSyntax.blocked w B z o l s) (Context.add (Formula.mem B w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (Formula.mem B w) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (PacketReaderInputSyntax.blocked w B z o l s) := .hyp (Or.inl rfl)
  exact PacketReaderInputOutcomes.blocked_no_result hZ w B z o l v s a h0 h1 h2

theorem packetReaderInputByteRejectNoSuccessor_kernel_certificate {m} (w B z o l v s a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderInputByteRejectNoSuccessorSentence w B z o l v s a)) := TheoryTransport.sentence (source_packetReaderInputByteRejectNoSuccessor w B z o l v s a)

theorem native_packetReaderInputByteRejectNoSuccessor {m} (w B z o l v s a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderInputByteRejectNoSuccessorSentence w B z o l v s a)) := ZFReplay.replay (packetReaderInputByteRejectNoSuccessor_kernel_certificate w B z o l v s a)

def packetReaderInputEofObservationsDisjointSentence {m} (w z o l v s a : Fin m) : Source.Sentence := ((PacketReaderInputSyntax.eofSuccess w z o l v s a).imp ((PacketReaderInputSyntax.eofFailure w z o l v s a).imp ((Formula.bot)))).close

theorem source_packetReaderInputEofObservationsDisjoint {m} (w z o l v s a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderInputEofObservationsDisjointSentence w z o l v s a) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderInputSyntax.eofFailure w z o l v s a) (Context.add (PacketReaderInputSyntax.eofSuccess w z o l v s a) (Source.SetLanguage.ZF.at m))
  have h0 : Derives Δ (PacketReaderInputSyntax.eofSuccess w z o l v s a) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PacketReaderInputSyntax.eofFailure w z o l v s a) := .hyp (Or.inl rfl)
  exact PacketReaderInputOutcomes.eof_incompatible w z o l v s a h0 h1

theorem packetReaderInputEofObservationsDisjoint_kernel_certificate {m} (w z o l v s a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderInputEofObservationsDisjointSentence w z o l v s a)) := TheoryTransport.sentence (source_packetReaderInputEofObservationsDisjoint w z o l v s a)

theorem native_packetReaderInputEofObservationsDisjoint {m} (w z o l v s a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderInputEofObservationsDisjointSentence w z o l v s a)) := ZFReplay.replay (packetReaderInputEofObservationsDisjoint_kernel_certificate w z o l v s a)

def packetReaderInputOriginalLiteralExactSuccessorDomainSentence {m} (w B z o l v s a : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 128 B).imp ((SyntaxNumeralSyntax.numeral 0 z).imp ((SyntaxNumeralSyntax.numeral 1 o).imp (((PacketReaderInputSyntax.existsResult w B z o l v s a).iff (PacketReaderInputExistence.admissible w B z o l v s a))))))).close

theorem source_packetReaderInputOriginalLiteralExactSuccessorDomain {m} (w B z o l v s a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderInputOriginalLiteralExactSuccessorDomainSentence w B z o l v s a) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNumeralSyntax.numeral 1 o) (Context.add (SyntaxNumeralSyntax.numeral 0 z) (Context.add (SyntaxNumeralSyntax.numeral 128 B) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 128 B) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral 0 z) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxNumeralSyntax.numeral 1 o) := .hyp (Or.inl rfl)
  exact PacketReaderInputExistence.domain_iff hZ w B z o l v s a h0 (SyntaxNumerals.range hZ 128 w B h0 h1) (SyntaxNumerals.range hZ 0 w z h0 h2) (SyntaxNumerals.range hZ 1 w o h0 h3)

theorem packetReaderInputOriginalLiteralExactSuccessorDomain_kernel_certificate {m} (w B z o l v s a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderInputOriginalLiteralExactSuccessorDomainSentence w B z o l v s a)) := TheoryTransport.sentence (source_packetReaderInputOriginalLiteralExactSuccessorDomain w B z o l v s a)

theorem native_packetReaderInputOriginalLiteralExactSuccessorDomain {m} (w B z o l v s a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderInputOriginalLiteralExactSuccessorDomainSentence w B z o l v s a)) := ZFReplay.replay (packetReaderInputOriginalLiteralExactSuccessorDomain_kernel_certificate w B z o l v s a)

def packetReaderInputOriginalLiteralFourWayDispatchSentence {m} (w B z o l v s a : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 128 B).imp ((SyntaxNumeralSyntax.numeral 0 z).imp ((SyntaxNumeralSyntax.numeral 1 o).imp (((PacketReaderInputOutcomes.outcome w B z o l v s a).iff (PacketReaderStepSyntax.state w l v s a))))))).close

theorem source_packetReaderInputOriginalLiteralFourWayDispatch {m} (w B z o l v s a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderInputOriginalLiteralFourWayDispatchSentence w B z o l v s a) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNumeralSyntax.numeral 1 o) (Context.add (SyntaxNumeralSyntax.numeral 0 z) (Context.add (SyntaxNumeralSyntax.numeral 128 B) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 128 B) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral 0 z) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxNumeralSyntax.numeral 1 o) := .hyp (Or.inl rfl)
  exact PacketReaderInputOutcomes.outcome_iff hZ w B z o l v s a h0 (SyntaxNumerals.range hZ 128 w B h0 h1) (SyntaxNumerals.range hZ 0 w z h0 h2) (SyntaxNumerals.range hZ 1 w o h0 h3)

theorem packetReaderInputOriginalLiteralFourWayDispatch_kernel_certificate {m} (w B z o l v s a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderInputOriginalLiteralFourWayDispatchSentence w B z o l v s a)) := TheoryTransport.sentence (source_packetReaderInputOriginalLiteralFourWayDispatch w B z o l v s a)

theorem native_packetReaderInputOriginalLiteralFourWayDispatch {m} (w B z o l v s a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderInputOriginalLiteralFourWayDispatchSentence w B z o l v s a)) := ZFReplay.replay (packetReaderInputOriginalLiteralFourWayDispatch_kernel_certificate w B z o l v s a)

end PPAC.Migration.Internal.ObjectPacketReaderInput
