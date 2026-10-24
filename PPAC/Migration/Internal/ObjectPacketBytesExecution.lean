import PPAC.Migration.Internal.PacketBytesExecution

/-! Independent actual byte execution has exactly the independent byte-list and natural-tail domain, with all internal joint induction hypotheses discharged. Original byte-program/varint bridge, full Basic AST bridge, Proof and Con remain unproved -/
namespace PPAC.Migration.Internal.ObjectPacketBytesExecution
open Source SourceAlgebra SourceLogic OmegaSyntax

def packetBytesExecutionActualCellDataSentence {m} (w h u a : Fin m) : Source.Sentence := ((omega w).imp ((PacketAffineAcceptedSyntax.accepted true w h u a).imp ((PacketBytesExecutionAffine.cellData w h u a)))).close

theorem source_packetBytesExecutionActualCellData {m} (w h u a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetBytesExecutionActualCellDataSentence w h u a) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketAffineAcceptedSyntax.accepted true w h u a) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PacketAffineAcceptedSyntax.accepted true w h u a) := .hyp (Or.inl rfl)
  exact PacketBytesExecutionAffine.data hZ w h u a h0 h1

theorem packetBytesExecutionActualCellData_kernel_certificate {m} (w h u a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetBytesExecutionActualCellDataSentence w h u a)) := TheoryTransport.sentence (source_packetBytesExecutionActualCellData w h u a)

theorem native_packetBytesExecutionActualCellData {m} (w h u a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetBytesExecutionActualCellDataSentence w h u a)) := ZFReplay.replay (packetBytesExecutionActualCellData_kernel_certificate w h u a)

def packetBytesExecutionActualCellTotalSentence {m} (w h u : Fin m) : Source.Sentence := ((omega w).imp ((PacketByteInputSyntax.byte h).imp ((Formula.mem u w).imp ((PacketBytesExecutionAffine.existsCell w h u))))).close

theorem source_packetBytesExecutionActualCellTotal {m} (w h u : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetBytesExecutionActualCellTotalSentence w h u) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem u w) (Context.add (PacketByteInputSyntax.byte h) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (PacketByteInputSyntax.byte h) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (Formula.mem u w) := .hyp (Or.inl rfl)
  exact PacketBytesExecutionAffine.exists_cell hZ w h u h0 h1 h2

theorem packetBytesExecutionActualCellTotal_kernel_certificate {m} (w h u : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetBytesExecutionActualCellTotalSentence w h u)) := TheoryTransport.sentence (source_packetBytesExecutionActualCellTotal w h u)

theorem native_packetBytesExecutionActualCellTotal {m} (w h u : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetBytesExecutionActualCellTotalSentence w h u)) := ZFReplay.replay (packetBytesExecutionActualCellTotal_kernel_certificate w h u)

def packetBytesExecutionActualCellUniqueSentence {m} (w h u a b : Fin m) : Source.Sentence := ((omega w).imp ((PacketAffineAcceptedSyntax.accepted true w h u a).imp ((PacketAffineAcceptedSyntax.accepted true w h u b).imp ((Formula.equal a b))))).close

theorem source_packetBytesExecutionActualCellUnique {m} (w h u a b : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetBytesExecutionActualCellUniqueSentence w h u a b) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketAffineAcceptedSyntax.accepted true w h u b) (Context.add (PacketAffineAcceptedSyntax.accepted true w h u a) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (PacketAffineAcceptedSyntax.accepted true w h u a) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (PacketAffineAcceptedSyntax.accepted true w h u b) := .hyp (Or.inl rfl)
  exact PacketBytesExecutionAffine.unique_cell hZ w h u a b h0 h1 h2

theorem packetBytesExecutionActualCellUnique_kernel_certificate {m} (w h u a b : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetBytesExecutionActualCellUniqueSentence w h u a b)) := TheoryTransport.sentence (source_packetBytesExecutionActualCellUnique w h u a b)

theorem native_packetBytesExecutionActualCellUnique {m} (w h u a b : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetBytesExecutionActualCellUniqueSentence w h u a b)) := ZFReplay.replay (packetBytesExecutionActualCellUnique_kernel_certificate w h u a b)

def packetBytesExecutionStrictInputTailPropertySentence {m} (w n h x : Fin m) : Source.Sentence := ((omega w).imp ((PacketBytesExecutionSyntax.earlier w n).imp ((StructuralListSyntax.consCode w h x n).imp ((PacketByteInputSyntax.byte h).imp ((PacketByteInputSyntax.byteList w x).imp ((PacketBytesExecutionSyntax.property w x))))))).close

theorem source_packetBytesExecutionStrictInputTailProperty {m} (w n h x : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetBytesExecutionStrictInputTailPropertySentence w n h x) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketByteInputSyntax.byteList w x) (Context.add (PacketByteInputSyntax.byte h) (Context.add (StructuralListSyntax.consCode w h x n) (Context.add (PacketBytesExecutionSyntax.earlier w n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (PacketBytesExecutionSyntax.earlier w n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (StructuralListSyntax.consCode w h x n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (PacketByteInputSyntax.byte h) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (PacketByteInputSyntax.byteList w x) := .hyp (Or.inl rfl)
  exact PacketBytesExecutionDescent.input_tail_property hZ w n h x h0 h1 h2 h3 h4

theorem packetBytesExecutionStrictInputTailProperty_kernel_certificate {m} (w n h x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetBytesExecutionStrictInputTailPropertySentence w n h x)) := TheoryTransport.sentence (source_packetBytesExecutionStrictInputTailProperty w n h x)

theorem native_packetBytesExecutionStrictInputTailProperty {m} (w n h x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetBytesExecutionStrictInputTailPropertySentence w n h x)) := ZFReplay.replay (packetBytesExecutionStrictInputTailProperty_kernel_certificate w n h x)

def packetBytesExecutionStrictAcceptedTailPropertySentence {m} (w n t a h x u : Fin m) : Source.Sentence := ((omega w).imp ((PacketBytesExecutionSyntax.earlier w n).imp ((StructuralListSyntax.consCode w h x n).imp ((PacketBytesTraceSyntax.bytes w x t u).imp ((PacketAffineAcceptedSyntax.accepted true w h u a).imp ((PacketBytesExecutionSyntax.property w x))))))).close

theorem source_packetBytesExecutionStrictAcceptedTailProperty {m} (w n t a h x u : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetBytesExecutionStrictAcceptedTailPropertySentence w n t a h x u) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketAffineAcceptedSyntax.accepted true w h u a) (Context.add (PacketBytesTraceSyntax.bytes w x t u) (Context.add (StructuralListSyntax.consCode w h x n) (Context.add (PacketBytesExecutionSyntax.earlier w n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (PacketBytesExecutionSyntax.earlier w n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (StructuralListSyntax.consCode w h x n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (PacketBytesTraceSyntax.bytes w x t u) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (PacketAffineAcceptedSyntax.accepted true w h u a) := .hyp (Or.inl rfl)
  exact PacketBytesExecutionDescent.accepted_tail_property hZ w n t a h x u h0 h1 h2 h3 h4

theorem packetBytesExecutionStrictAcceptedTailProperty_kernel_certificate {m} (w n t a h x u : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetBytesExecutionStrictAcceptedTailPropertySentence w n t a h x u)) := TheoryTransport.sentence (source_packetBytesExecutionStrictAcceptedTailProperty w n t a h x u)

theorem native_packetBytesExecutionStrictAcceptedTailProperty {m} (w n t a h x u : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetBytesExecutionStrictAcceptedTailPropertySentence w n t a h x u)) := ZFReplay.replay (packetBytesExecutionStrictAcceptedTailProperty_kernel_certificate w n t a h x u)

def packetBytesExecutionTotalJointStepSentence {m} (w n : Fin m) : Source.Sentence := ((omega w).imp ((PacketBytesExecutionSyntax.earlier w n).imp ((PacketBytesExecutionSyntax.total w n)))).close

theorem source_packetBytesExecutionTotalJointStep {m} (w n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetBytesExecutionTotalJointStepSentence w n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketBytesExecutionSyntax.earlier w n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PacketBytesExecutionSyntax.earlier w n) := .hyp (Or.inl rfl)
  exact PacketBytesExecutionTotal.total_property hZ w n h0 h1

theorem packetBytesExecutionTotalJointStep_kernel_certificate {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetBytesExecutionTotalJointStepSentence w n)) := TheoryTransport.sentence (source_packetBytesExecutionTotalJointStep w n)

theorem native_packetBytesExecutionTotalJointStep {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetBytesExecutionTotalJointStepSentence w n)) := ZFReplay.replay (packetBytesExecutionTotalJointStep_kernel_certificate w n)

def packetBytesExecutionDomainJointStepSentence {m} (w n : Fin m) : Source.Sentence := ((omega w).imp ((PacketBytesExecutionSyntax.earlier w n).imp ((PacketBytesExecutionSyntax.domain w n)))).close

theorem source_packetBytesExecutionDomainJointStep {m} (w n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetBytesExecutionDomainJointStepSentence w n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketBytesExecutionSyntax.earlier w n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PacketBytesExecutionSyntax.earlier w n) := .hyp (Or.inl rfl)
  exact PacketBytesExecutionDomain.domain_property hZ w n h0 h1

theorem packetBytesExecutionDomainJointStep_kernel_certificate {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetBytesExecutionDomainJointStepSentence w n)) := TheoryTransport.sentence (source_packetBytesExecutionDomainJointStep w n)

theorem native_packetBytesExecutionDomainJointStep {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetBytesExecutionDomainJointStepSentence w n)) := ZFReplay.replay (packetBytesExecutionDomainJointStep_kernel_certificate w n)

def packetBytesExecutionUniqueJointStepSentence {m} (w n : Fin m) : Source.Sentence := ((omega w).imp ((PacketBytesExecutionSyntax.earlier w n).imp ((PacketBytesExecutionSyntax.unique w n)))).close

theorem source_packetBytesExecutionUniqueJointStep {m} (w n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetBytesExecutionUniqueJointStepSentence w n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketBytesExecutionSyntax.earlier w n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PacketBytesExecutionSyntax.earlier w n) := .hyp (Or.inl rfl)
  exact PacketBytesExecutionUnique.unique_property hZ w n h0 h1

theorem packetBytesExecutionUniqueJointStep_kernel_certificate {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetBytesExecutionUniqueJointStepSentence w n)) := TheoryTransport.sentence (source_packetBytesExecutionUniqueJointStep w n)

theorem native_packetBytesExecutionUniqueJointStep {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetBytesExecutionUniqueJointStepSentence w n)) := ZFReplay.replay (packetBytesExecutionUniqueJointStep_kernel_certificate w n)

def packetBytesExecutionAllJointPropertiesSentence {m} (w : Fin m) : Source.Sentence := ((omega w).imp ((.all ((Formula.mem (Fin.last m) w.castSucc).imp (PacketBytesExecutionSyntax.property w.castSucc (Fin.last m)))))).close

theorem source_packetBytesExecutionAllJointProperties {m} (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetBytesExecutionAllJointPropertiesSentence w) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact PacketBytesExecutionInduction.all_properties hZ w h0

theorem packetBytesExecutionAllJointProperties_kernel_certificate {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetBytesExecutionAllJointPropertiesSentence w)) := TheoryTransport.sentence (source_packetBytesExecutionAllJointProperties w)

theorem native_packetBytesExecutionAllJointProperties {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetBytesExecutionAllJointPropertiesSentence w)) := ZFReplay.replay (packetBytesExecutionAllJointProperties_kernel_certificate w)

def packetBytesExecutionOutputExistsSentence {m} (w n t : Fin m) : Source.Sentence := ((omega w).imp ((PacketByteInputSyntax.byteList w n).imp ((Formula.mem t w).imp ((PacketBytesExecutionSyntax.existsOutput w n t))))).close

theorem source_packetBytesExecutionOutputExists {m} (w n t : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetBytesExecutionOutputExistsSentence w n t) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem t w) (Context.add (PacketByteInputSyntax.byteList w n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (PacketByteInputSyntax.byteList w n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (Formula.mem t w) := .hyp (Or.inl rfl)
  exact PacketBytesExecutionInduction.exists_output hZ w n t h0 h1 h2

theorem packetBytesExecutionOutputExists_kernel_certificate {m} (w n t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetBytesExecutionOutputExistsSentence w n t)) := TheoryTransport.sentence (source_packetBytesExecutionOutputExists w n t)

theorem native_packetBytesExecutionOutputExists {m} (w n t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetBytesExecutionOutputExistsSentence w n t)) := ZFReplay.replay (packetBytesExecutionOutputExists_kernel_certificate w n t)

def packetBytesExecutionActualInputDomainSentence {m} (w n t a : Fin m) : Source.Sentence := ((omega w).imp ((PacketBytesTraceSyntax.bytes w n t a).imp ((PacketByteInputSyntax.byteList w n)))).close

theorem source_packetBytesExecutionActualInputDomain {m} (w n t a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetBytesExecutionActualInputDomainSentence w n t a) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketBytesTraceSyntax.bytes w n t a) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PacketBytesTraceSyntax.bytes w n t a) := .hyp (Or.inl rfl)
  exact PacketBytesExecutionInduction.input_domain hZ w n t a h0 h1

theorem packetBytesExecutionActualInputDomain_kernel_certificate {m} (w n t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetBytesExecutionActualInputDomainSentence w n t a)) := TheoryTransport.sentence (source_packetBytesExecutionActualInputDomain w n t a)

theorem native_packetBytesExecutionActualInputDomain {m} (w n t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetBytesExecutionActualInputDomainSentence w n t a)) := ZFReplay.replay (packetBytesExecutionActualInputDomain_kernel_certificate w n t a)

def packetBytesExecutionOutputUniqueSentence {m} (w n t a b : Fin m) : Source.Sentence := ((omega w).imp ((PacketBytesTraceSyntax.bytes w n t a).imp ((PacketBytesTraceSyntax.bytes w n t b).imp ((Formula.equal a b))))).close

theorem source_packetBytesExecutionOutputUnique {m} (w n t a b : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetBytesExecutionOutputUniqueSentence w n t a b) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketBytesTraceSyntax.bytes w n t b) (Context.add (PacketBytesTraceSyntax.bytes w n t a) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (PacketBytesTraceSyntax.bytes w n t a) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (PacketBytesTraceSyntax.bytes w n t b) := .hyp (Or.inl rfl)
  exact PacketBytesExecutionInduction.output_unique hZ w n t a b h0 h1 h2

theorem packetBytesExecutionOutputUnique_kernel_certificate {m} (w n t a b : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetBytesExecutionOutputUniqueSentence w n t a b)) := TheoryTransport.sentence (source_packetBytesExecutionOutputUnique w n t a b)

theorem native_packetBytesExecutionOutputUnique {m} (w n t a b : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetBytesExecutionOutputUniqueSentence w n t a b)) := ZFReplay.replay (packetBytesExecutionOutputUnique_kernel_certificate w n t a b)

def packetBytesExecutionExistsDomainIffSentence {m} (w n t : Fin m) : Source.Sentence := ((omega w).imp (((PacketBytesExecutionSyntax.existsOutput w n t).iff ((PacketByteInputSyntax.byteList w n).conj (.mem t w))))).close

theorem source_packetBytesExecutionExistsDomainIff {m} (w n t : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetBytesExecutionExistsDomainIffSentence w n t) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact PacketBytesExecution.exists_iff hZ w n t h0

theorem packetBytesExecutionExistsDomainIff_kernel_certificate {m} (w n t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetBytesExecutionExistsDomainIffSentence w n t)) := TheoryTransport.sentence (source_packetBytesExecutionExistsDomainIff w n t)

theorem native_packetBytesExecutionExistsDomainIff {m} (w n t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetBytesExecutionExistsDomainIffSentence w n t)) := ZFReplay.replay (packetBytesExecutionExistsDomainIff_kernel_certificate w n t)

def packetBytesExecutionUniqueFiberIffSentence {m} (w n t : Fin m) : Source.Sentence := ((omega w).imp (((PacketBytesExecutionFiberSyntax.fiber w n t).iff ((PacketByteInputSyntax.byteList w n).conj (.mem t w))))).close

theorem source_packetBytesExecutionUniqueFiberIff {m} (w n t : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetBytesExecutionUniqueFiberIffSentence w n t) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact PacketBytesExecution.fiber_iff hZ w n t h0

theorem packetBytesExecutionUniqueFiberIff_kernel_certificate {m} (w n t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetBytesExecutionUniqueFiberIffSentence w n t)) := TheoryTransport.sentence (source_packetBytesExecutionUniqueFiberIff w n t)

theorem native_packetBytesExecutionUniqueFiberIff {m} (w n t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetBytesExecutionUniqueFiberIffSentence w n t)) := ZFReplay.replay (packetBytesExecutionUniqueFiberIff_kernel_certificate w n t)

def packetBytesExecutionAllInternalFiberDomainSentence {m} (w : Fin m) : Source.Sentence := ((omega w).imp ((PacketBytesExecutionFiberSyntax.allLaw w))).close

theorem source_packetBytesExecutionAllInternalFiberDomain {m} (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetBytesExecutionAllInternalFiberDomainSentence w) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact PacketBytesExecution.all_law hZ w h0

theorem packetBytesExecutionAllInternalFiberDomain_kernel_certificate {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetBytesExecutionAllInternalFiberDomainSentence w)) := TheoryTransport.sentence (source_packetBytesExecutionAllInternalFiberDomain w)

theorem native_packetBytesExecutionAllInternalFiberDomain {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetBytesExecutionAllInternalFiberDomainSentence w)) := ZFReplay.replay (packetBytesExecutionAllInternalFiberDomain_kernel_certificate w)

def packetBytesExecutionInvalidInputRejectedSentence {m} (w n t a : Fin m) : Source.Sentence := ((omega w).imp (((PacketByteInputSyntax.byteList w n).neg).imp (((PacketBytesTraceSyntax.bytes w n t a).neg)))).close

theorem source_packetBytesExecutionInvalidInputRejected {m} (w n t a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetBytesExecutionInvalidInputRejectedSentence w n t a) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add ((PacketByteInputSyntax.byteList w n).neg) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ ((PacketByteInputSyntax.byteList w n).neg) := .hyp (Or.inl rfl)
  exact PacketBytesExecution.reject_input hZ w n t a h0 h1

theorem packetBytesExecutionInvalidInputRejected_kernel_certificate {m} (w n t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetBytesExecutionInvalidInputRejectedSentence w n t a)) := TheoryTransport.sentence (source_packetBytesExecutionInvalidInputRejected w n t a)

theorem native_packetBytesExecutionInvalidInputRejected {m} (w n t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetBytesExecutionInvalidInputRejectedSentence w n t a)) := ZFReplay.replay (packetBytesExecutionInvalidInputRejected_kernel_certificate w n t a)

end PPAC.Migration.Internal.ObjectPacketBytesExecution
