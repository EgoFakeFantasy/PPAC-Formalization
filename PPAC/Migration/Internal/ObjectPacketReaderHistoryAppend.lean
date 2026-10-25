import PPAC.Migration.Internal.PacketReaderHistoryUnique

/-! Actual history extension preserves all old rows and adds the real final coded step. Original omega induction discharges fixed-matrix agreement on every internal natural index, giving all common values and equal-length endpoints unique. Complete runs, input consumption, EOF reverse, Basic AST, Proof and Con remain unproved -/
namespace PPAC.Migration.Internal.ObjectPacketReaderHistoryAppend
open Source SourceAlgebra SourceLogic OmegaSyntax

def packetReaderHistoryAppendEveryOldRowPreservedSentence {m} (w B z o f g i : Fin m) : Source.Sentence := ((GraphPointwiseSyntax.edgeIncluded f g).imp ((PacketReaderHistorySyntax.row w B z o f i).imp ((PacketReaderHistorySyntax.row w B z o g i)))).close

theorem source_packetReaderHistoryAppendEveryOldRowPreserved {m} (w B z o f g i : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderHistoryAppendEveryOldRowPreservedSentence w B z o f g i) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderHistorySyntax.row w B z o f i) (Context.add (GraphPointwiseSyntax.edgeIncluded f g) (Source.SetLanguage.ZF.at m))
  have h0 : Derives Δ (GraphPointwiseSyntax.edgeIncluded f g) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PacketReaderHistorySyntax.row w B z o f i) := .hyp (Or.inl rfl)
  exact PacketReaderHistoryRowMap.row_map w B z o f g i h0 h1

theorem packetReaderHistoryAppendEveryOldRowPreserved_kernel_certificate {m} (w B z o f g i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderHistoryAppendEveryOldRowPreservedSentence w B z o f g i)) := TheoryTransport.sentence (source_packetReaderHistoryAppendEveryOldRowPreserved w B z o f g i)

theorem native_packetReaderHistoryAppendEveryOldRowPreserved {m} (w B z o f g i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderHistoryAppendEveryOldRowPreservedSentence w B z o f g i)) := ZFReplay.replay (packetReaderHistoryAppendEveryOldRowPreserved_kernel_certificate w B z o f g i)

def packetReaderHistoryAppendAllOldAndNewRowsPreservedSentence {m} (w B z o l d f g : Fin m) : Source.Sentence := ((successor d l).imp ((PacketReaderHistorySyntax.links w B z o l f).imp ((GraphPointwiseSyntax.edgeIncluded f g).imp ((PacketReaderHistorySyntax.row w B z o g l).imp ((PacketReaderHistorySyntax.links w B z o d g)))))).close

theorem source_packetReaderHistoryAppendAllOldAndNewRowsPreserved {m} (w B z o l d f g : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderHistoryAppendAllOldAndNewRowsPreservedSentence w B z o l d f g) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderHistorySyntax.row w B z o g l) (Context.add (GraphPointwiseSyntax.edgeIncluded f g) (Context.add (PacketReaderHistorySyntax.links w B z o l f) (Context.add (successor d l) (Source.SetLanguage.ZF.at m))))
  have h0 : Derives Δ (successor d l) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (PacketReaderHistorySyntax.links w B z o l f) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (GraphPointwiseSyntax.edgeIncluded f g) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (PacketReaderHistorySyntax.row w B z o g l) := .hyp (Or.inl rfl)
  exact PacketReaderHistoryRowMap.append_links w B z o l d f g h0 h1 h2 h3

theorem packetReaderHistoryAppendAllOldAndNewRowsPreserved_kernel_certificate {m} (w B z o l d f g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderHistoryAppendAllOldAndNewRowsPreservedSentence w B z o l d f g)) := TheoryTransport.sentence (source_packetReaderHistoryAppendAllOldAndNewRowsPreserved w B z o l d f g)

theorem native_packetReaderHistoryAppendAllOldAndNewRowsPreserved {m} (w B z o l d f g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderHistoryAppendAllOldAndNewRowsPreservedSentence w B z o l d f g)) := ZFReplay.replay (packetReaderHistoryAppendAllOldAndNewRowsPreserved_kernel_certificate w B z o l d f g)

def packetReaderHistoryAppendEveryActualAppendIsLongerHistorySentence {m} (w B z o n r s l d e f g : Fin m) : Source.Sentence := ((omega w).imp ((PacketReaderHistorySyntax.history w B z o n r l d f).imp ((PacketReaderCodedSyntax.step w B z o r s).imp ((successor e d).imp ((SequenceSyntax.append g e f d s w).imp ((PacketReaderHistorySyntax.history w B z o n s d e g))))))).close

theorem source_packetReaderHistoryAppendEveryActualAppendIsLongerHistory {m} (w B z o n r s l d e f g : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderHistoryAppendEveryActualAppendIsLongerHistorySentence w B z o n r s l d e f g) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SequenceSyntax.append g e f d s w) (Context.add (successor e d) (Context.add (PacketReaderCodedSyntax.step w B z o r s) (Context.add (PacketReaderHistorySyntax.history w B z o n r l d f) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (PacketReaderHistorySyntax.history w B z o n r l d f) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (PacketReaderCodedSyntax.step w B z o r s) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (successor e d) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (SequenceSyntax.append g e f d s w) := .hyp (Or.inl rfl)
  exact PacketReaderHistoryAppend.from_append hZ w B z o n r s l d e f g h0 h1 h2 h3 h4

theorem packetReaderHistoryAppendEveryActualAppendIsLongerHistory_kernel_certificate {m} (w B z o n r s l d e f g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderHistoryAppendEveryActualAppendIsLongerHistorySentence w B z o n r s l d e f g)) := TheoryTransport.sentence (source_packetReaderHistoryAppendEveryActualAppendIsLongerHistory w B z o n r s l d e f g)

theorem native_packetReaderHistoryAppendEveryActualAppendIsLongerHistory {m} (w B z o n r s l d e f g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderHistoryAppendEveryActualAppendIsLongerHistorySentence w B z o n r s l d e f g)) := ZFReplay.replay (packetReaderHistoryAppendEveryActualAppendIsLongerHistory_kernel_certificate w B z o n r s l d e f g)

def packetReaderHistoryAppendActualExactExtensionExistsSentence {m} (w B z o n r s l d e f : Fin m) : Source.Sentence := ((omega w).imp ((PacketReaderHistorySyntax.history w B z o n r l d f).imp ((PacketReaderCodedSyntax.step w B z o r s).imp ((successor e d).imp ((PacketReaderHistoryAppend.extension w B z o n s d e f)))))).close

theorem source_packetReaderHistoryAppendActualExactExtensionExists {m} (w B z o n r s l d e f : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderHistoryAppendActualExactExtensionExistsSentence w B z o n r s l d e f) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor e d) (Context.add (PacketReaderCodedSyntax.step w B z o r s) (Context.add (PacketReaderHistorySyntax.history w B z o n r l d f) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (PacketReaderHistorySyntax.history w B z o n r l d f) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (PacketReaderCodedSyntax.step w B z o r s) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (successor e d) := .hyp (Or.inl rfl)
  exact PacketReaderHistoryAppend.exists_extension hZ w B z o n r s l d e f h0 h1 h2 h3

theorem packetReaderHistoryAppendActualExactExtensionExists_kernel_certificate {m} (w B z o n r s l d e f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderHistoryAppendActualExactExtensionExistsSentence w B z o n r s l d e f)) := TheoryTransport.sentence (source_packetReaderHistoryAppendActualExactExtensionExists w B z o n r s l d e f)

theorem native_packetReaderHistoryAppendActualExactExtensionExists {m} (w B z o n r s l d e f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderHistoryAppendActualExactExtensionExistsSentence w B z o n r s l d e f)) := ZFReplay.replay (packetReaderHistoryAppendActualExactExtensionExists_kernel_certificate w B z o n r s l d e f)

def packetReaderHistoryAppendBothActualRowWitnessBlocksComparedSentence {m} (w B z o f g d e i j a b : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem B w).imp ((SequenceSyntax.sequence f d w).imp ((SequenceSyntax.sequence g e w).imp ((PacketReaderHistoryAgreementSyntax.agree f g i).imp ((successor j i).imp ((PacketReaderHistorySyntax.row w B z o f i).imp ((PacketReaderHistorySyntax.row w B z o g i).imp ((GraphSyntax.edge f j a).imp ((GraphSyntax.edge g j b).imp ((Formula.equal a b)))))))))))).close

theorem source_packetReaderHistoryAppendBothActualRowWitnessBlocksCompared {m} (w B z o f g d e i j a b : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderHistoryAppendBothActualRowWitnessBlocksComparedSentence w B z o f g d e i j a b) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (GraphSyntax.edge g j b) (Context.add (GraphSyntax.edge f j a) (Context.add (PacketReaderHistorySyntax.row w B z o g i) (Context.add (PacketReaderHistorySyntax.row w B z o f i) (Context.add (successor j i) (Context.add (PacketReaderHistoryAgreementSyntax.agree f g i) (Context.add (SequenceSyntax.sequence g e w) (Context.add (SequenceSyntax.sequence f d w) (Context.add (Formula.mem B w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))
  have h1 : Derives Δ (Formula.mem B w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))
  have h2 : Derives Δ (SequenceSyntax.sequence f d w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  have h3 : Derives Δ (SequenceSyntax.sequence g e w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h4 : Derives Δ (PacketReaderHistoryAgreementSyntax.agree f g i) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h5 : Derives Δ (successor j i) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h6 : Derives Δ (PacketReaderHistorySyntax.row w B z o f i) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h7 : Derives Δ (PacketReaderHistorySyntax.row w B z o g i) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h8 : Derives Δ (GraphSyntax.edge f j a) := .hyp (Or.inr (Or.inl rfl))
  have h9 : Derives Δ (GraphSyntax.edge g j b) := .hyp (Or.inl rfl)
  exact PacketReaderHistoryAgreementRows.outputs_unique hZ w B z o f g d e i j a b h0 h1 h2 h3 h4 h5 h6 h7 h8 h9

theorem packetReaderHistoryAppendBothActualRowWitnessBlocksCompared_kernel_certificate {m} (w B z o f g d e i j a b : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderHistoryAppendBothActualRowWitnessBlocksComparedSentence w B z o f g d e i j a b)) := TheoryTransport.sentence (source_packetReaderHistoryAppendBothActualRowWitnessBlocksCompared w B z o f g d e i j a b)

theorem native_packetReaderHistoryAppendBothActualRowWitnessBlocksCompared {m} (w B z o f g d e i j a b : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderHistoryAppendBothActualRowWitnessBlocksComparedSentence w B z o f g d e i j a b)) := ZFReplay.replay (packetReaderHistoryAppendBothActualRowWitnessBlocksCompared_kernel_certificate w B z o f g d e i j a b)

def packetReaderHistoryAppendEmptyIndexAgreementSentence {m} (w B z o n r t l d k e f g i : Fin m) : Source.Sentence := ((PacketReaderHistorySyntax.history w B z o n r l d f).imp ((PacketReaderHistorySyntax.history w B z o n t k e g).imp ((empty i).imp ((PacketReaderHistoryAgreementSyntax.agree f g i))))).close

theorem source_packetReaderHistoryAppendEmptyIndexAgreement {m} (w B z o n r t l d k e f g i : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderHistoryAppendEmptyIndexAgreementSentence w B z o n r t l d k e f g i) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (empty i) (Context.add (PacketReaderHistorySyntax.history w B z o n t k e g) (Context.add (PacketReaderHistorySyntax.history w B z o n r l d f) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (PacketReaderHistorySyntax.history w B z o n r l d f) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (PacketReaderHistorySyntax.history w B z o n t k e g) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (empty i) := .hyp (Or.inl rfl)
  exact PacketReaderHistoryAgreementPoint.zero_point hZ w B z o n r t l d k e f g i h0 h1 h2

theorem packetReaderHistoryAppendEmptyIndexAgreement_kernel_certificate {m} (w B z o n r t l d k e f g i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderHistoryAppendEmptyIndexAgreementSentence w B z o n r t l d k e f g i)) := TheoryTransport.sentence (source_packetReaderHistoryAppendEmptyIndexAgreement w B z o n r t l d k e f g i)

theorem native_packetReaderHistoryAppendEmptyIndexAgreement {m} (w B z o n r t l d k e f g i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderHistoryAppendEmptyIndexAgreementSentence w B z o n r t l d k e f g i)) := ZFReplay.replay (packetReaderHistoryAppendEmptyIndexAgreement_kernel_certificate w B z o n r t l d k e f g i)

def packetReaderHistoryAppendRealSuccessorAgreementSentence {m} (w B z o n r t l d k e f g i j : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem B w).imp ((PacketReaderHistorySyntax.history w B z o n r l d f).imp ((PacketReaderHistorySyntax.history w B z o n t k e g).imp ((PacketReaderHistoryAgreementSyntax.agree f g i).imp ((successor j i).imp ((PacketReaderHistoryAgreementSyntax.agree f g j)))))))).close

theorem source_packetReaderHistoryAppendRealSuccessorAgreement {m} (w B z o n r t l d k e f g i j : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderHistoryAppendRealSuccessorAgreementSentence w B z o n r t l d k e f g i j) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor j i) (Context.add (PacketReaderHistoryAgreementSyntax.agree f g i) (Context.add (PacketReaderHistorySyntax.history w B z o n t k e g) (Context.add (PacketReaderHistorySyntax.history w B z o n r l d f) (Context.add (Formula.mem B w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
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
  have h3 : Derives Δ (PacketReaderHistorySyntax.history w B z o n t k e g) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (PacketReaderHistoryAgreementSyntax.agree f g i) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (successor j i) := .hyp (Or.inl rfl)
  exact PacketReaderHistoryAgreementPoint.successor_point hZ w B z o n r t l d k e f g i j h0 h1 h2 h3 h4 h5

theorem packetReaderHistoryAppendRealSuccessorAgreement_kernel_certificate {m} (w B z o n r t l d k e f g i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderHistoryAppendRealSuccessorAgreementSentence w B z o n r t l d k e f g i j)) := TheoryTransport.sentence (source_packetReaderHistoryAppendRealSuccessorAgreement w B z o n r t l d k e f g i j)

theorem native_packetReaderHistoryAppendRealSuccessorAgreement {m} (w B z o n r t l d k e f g i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderHistoryAppendRealSuccessorAgreementSentence w B z o n r t l d k e f g i j)) := ZFReplay.replay (packetReaderHistoryAppendRealSuccessorAgreement_kernel_certificate w B z o n r t l d k e f g i j)

def packetReaderHistoryAppendOriginalOmegaMatrixBaseSentence {m} (w B z o n r t l d k e f g : Fin m) : Source.Sentence := ((PacketReaderHistorySyntax.history w B z o n r l d f).imp ((PacketReaderHistorySyntax.history w B z o n t k e g).imp ((OmegaInductionSyntax.base PacketReaderHistoryAgreementSyntax.matrix (Source.SetLanguage.args2 f g))))).close

theorem source_packetReaderHistoryAppendOriginalOmegaMatrixBase {m} (w B z o n r t l d k e f g : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderHistoryAppendOriginalOmegaMatrixBaseSentence w B z o n r t l d k e f g) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderHistorySyntax.history w B z o n t k e g) (Context.add (PacketReaderHistorySyntax.history w B z o n r l d f) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (PacketReaderHistorySyntax.history w B z o n r l d f) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PacketReaderHistorySyntax.history w B z o n t k e g) := .hyp (Or.inl rfl)
  exact PacketReaderHistoryAgreementInduction.base hZ w B z o n r t l d k e f g h0 h1

theorem packetReaderHistoryAppendOriginalOmegaMatrixBase_kernel_certificate {m} (w B z o n r t l d k e f g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderHistoryAppendOriginalOmegaMatrixBaseSentence w B z o n r t l d k e f g)) := TheoryTransport.sentence (source_packetReaderHistoryAppendOriginalOmegaMatrixBase w B z o n r t l d k e f g)

theorem native_packetReaderHistoryAppendOriginalOmegaMatrixBase {m} (w B z o n r t l d k e f g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderHistoryAppendOriginalOmegaMatrixBaseSentence w B z o n r t l d k e f g)) := ZFReplay.replay (packetReaderHistoryAppendOriginalOmegaMatrixBase_kernel_certificate w B z o n r t l d k e f g)

def packetReaderHistoryAppendOriginalOmegaMatrixStepSentence {m} (w B z o n r t l d k e f g : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem B w).imp ((PacketReaderHistorySyntax.history w B z o n r l d f).imp ((PacketReaderHistorySyntax.history w B z o n t k e g).imp ((OmegaInductionSyntax.step PacketReaderHistoryAgreementSyntax.matrix (Source.SetLanguage.args2 f g) w)))))).close

theorem source_packetReaderHistoryAppendOriginalOmegaMatrixStep {m} (w B z o n r t l d k e f g : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderHistoryAppendOriginalOmegaMatrixStepSentence w B z o n r t l d k e f g) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderHistorySyntax.history w B z o n t k e g) (Context.add (PacketReaderHistorySyntax.history w B z o n r l d f) (Context.add (Formula.mem B w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (Formula.mem B w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (PacketReaderHistorySyntax.history w B z o n r l d f) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (PacketReaderHistorySyntax.history w B z o n t k e g) := .hyp (Or.inl rfl)
  exact PacketReaderHistoryAgreementInduction.step hZ w B z o n r t l d k e f g h0 h1 h2 h3

theorem packetReaderHistoryAppendOriginalOmegaMatrixStep_kernel_certificate {m} (w B z o n r t l d k e f g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderHistoryAppendOriginalOmegaMatrixStepSentence w B z o n r t l d k e f g)) := TheoryTransport.sentence (source_packetReaderHistoryAppendOriginalOmegaMatrixStep w B z o n r t l d k e f g)

theorem native_packetReaderHistoryAppendOriginalOmegaMatrixStep {m} (w B z o n r t l d k e f g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderHistoryAppendOriginalOmegaMatrixStepSentence w B z o n r t l d k e f g)) := ZFReplay.replay (packetReaderHistoryAppendOriginalOmegaMatrixStep_kernel_certificate w B z o n r t l d k e f g)

def packetReaderHistoryAppendAllInternalIndexAgreementIHDischargedSentence {m} (w B z o n r t l d k e f g : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem B w).imp ((PacketReaderHistorySyntax.history w B z o n r l d f).imp ((PacketReaderHistorySyntax.history w B z o n t k e g).imp ((PacketReaderHistoryAgreementSyntax.allAgreement w f g)))))).close

theorem source_packetReaderHistoryAppendAllInternalIndexAgreementIHDischarged {m} (w B z o n r t l d k e f g : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderHistoryAppendAllInternalIndexAgreementIHDischargedSentence w B z o n r t l d k e f g) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderHistorySyntax.history w B z o n t k e g) (Context.add (PacketReaderHistorySyntax.history w B z o n r l d f) (Context.add (Formula.mem B w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (Formula.mem B w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (PacketReaderHistorySyntax.history w B z o n r l d f) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (PacketReaderHistorySyntax.history w B z o n t k e g) := .hyp (Or.inl rfl)
  exact PacketReaderHistoryAgreementInduction.all_agreement hZ w B z o n r t l d k e f g h0 h1 h2 h3

theorem packetReaderHistoryAppendAllInternalIndexAgreementIHDischarged_kernel_certificate {m} (w B z o n r t l d k e f g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderHistoryAppendAllInternalIndexAgreementIHDischargedSentence w B z o n r t l d k e f g)) := TheoryTransport.sentence (source_packetReaderHistoryAppendAllInternalIndexAgreementIHDischarged w B z o n r t l d k e f g)

theorem native_packetReaderHistoryAppendAllInternalIndexAgreementIHDischarged {m} (w B z o n r t l d k e f g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderHistoryAppendAllInternalIndexAgreementIHDischargedSentence w B z o n r t l d k e f g)) := ZFReplay.replay (packetReaderHistoryAppendAllInternalIndexAgreementIHDischarged_kernel_certificate w B z o n r t l d k e f g)

def packetReaderHistoryAppendEveryActualNaturalIndexAgreesSentence {m} (w B z o n r t l d k e f g i : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem B w).imp ((PacketReaderHistorySyntax.history w B z o n r l d f).imp ((PacketReaderHistorySyntax.history w B z o n t k e g).imp ((Formula.mem i w).imp ((PacketReaderHistoryAgreementSyntax.agree f g i))))))).close

theorem source_packetReaderHistoryAppendEveryActualNaturalIndexAgrees {m} (w B z o n r t l d k e f g i : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderHistoryAppendEveryActualNaturalIndexAgreesSentence w B z o n r t l d k e f g i) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem i w) (Context.add (PacketReaderHistorySyntax.history w B z o n t k e g) (Context.add (PacketReaderHistorySyntax.history w B z o n r l d f) (Context.add (Formula.mem B w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (Formula.mem B w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (PacketReaderHistorySyntax.history w B z o n r l d f) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (PacketReaderHistorySyntax.history w B z o n t k e g) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (Formula.mem i w) := .hyp (Or.inl rfl)
  exact PacketReaderHistoryUnique.at_index hZ w B z o n r t l d k e f g i h0 h1 h2 h3 h4

theorem packetReaderHistoryAppendEveryActualNaturalIndexAgrees_kernel_certificate {m} (w B z o n r t l d k e f g i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderHistoryAppendEveryActualNaturalIndexAgreesSentence w B z o n r t l d k e f g i)) := TheoryTransport.sentence (source_packetReaderHistoryAppendEveryActualNaturalIndexAgrees w B z o n r t l d k e f g i)

theorem native_packetReaderHistoryAppendEveryActualNaturalIndexAgrees {m} (w B z o n r t l d k e f g i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderHistoryAppendEveryActualNaturalIndexAgreesSentence w B z o n r t l d k e f g i)) := ZFReplay.replay (packetReaderHistoryAppendEveryActualNaturalIndexAgrees_kernel_certificate w B z o n r t l d k e f g i)

def packetReaderHistoryAppendAnyActualCommonEdgesHaveSameValueSentence {m} (w B z o n r t l d k e f g i a b : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem B w).imp ((PacketReaderHistorySyntax.history w B z o n r l d f).imp ((PacketReaderHistorySyntax.history w B z o n t k e g).imp ((GraphSyntax.edge f i a).imp ((GraphSyntax.edge g i b).imp ((Formula.equal a b)))))))).close

theorem source_packetReaderHistoryAppendAnyActualCommonEdgesHaveSameValue {m} (w B z o n r t l d k e f g i a b : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderHistoryAppendAnyActualCommonEdgesHaveSameValueSentence w B z o n r t l d k e f g i a b) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (GraphSyntax.edge g i b) (Context.add (GraphSyntax.edge f i a) (Context.add (PacketReaderHistorySyntax.history w B z o n t k e g) (Context.add (PacketReaderHistorySyntax.history w B z o n r l d f) (Context.add (Formula.mem B w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
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
  have h3 : Derives Δ (PacketReaderHistorySyntax.history w B z o n t k e g) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (GraphSyntax.edge f i a) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (GraphSyntax.edge g i b) := .hyp (Or.inl rfl)
  exact PacketReaderHistoryUnique.common_values hZ w B z o n r t l d k e f g i a b h0 h1 h2 h3 h4 h5

theorem packetReaderHistoryAppendAnyActualCommonEdgesHaveSameValue_kernel_certificate {m} (w B z o n r t l d k e f g i a b : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderHistoryAppendAnyActualCommonEdgesHaveSameValueSentence w B z o n r t l d k e f g i a b)) := TheoryTransport.sentence (source_packetReaderHistoryAppendAnyActualCommonEdgesHaveSameValue w B z o n r t l d k e f g i a b)

theorem native_packetReaderHistoryAppendAnyActualCommonEdgesHaveSameValue {m} (w B z o n r t l d k e f g i a b : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderHistoryAppendAnyActualCommonEdgesHaveSameValueSentence w B z o n r t l d k e f g i a b)) := ZFReplay.replay (packetReaderHistoryAppendAnyActualCommonEdgesHaveSameValue_kernel_certificate w B z o n r t l d k e f g i a b)

def packetReaderHistoryAppendSameInternalLengthEndpointsUniqueSentence {m} (w B z o n r t l d e f g : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem B w).imp ((PacketReaderHistorySyntax.history w B z o n r l d f).imp ((PacketReaderHistorySyntax.history w B z o n t l e g).imp ((Formula.equal r t)))))).close

theorem source_packetReaderHistoryAppendSameInternalLengthEndpointsUnique {m} (w B z o n r t l d e f g : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderHistoryAppendSameInternalLengthEndpointsUniqueSentence w B z o n r t l d e f g) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderHistorySyntax.history w B z o n t l e g) (Context.add (PacketReaderHistorySyntax.history w B z o n r l d f) (Context.add (Formula.mem B w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (Formula.mem B w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (PacketReaderHistorySyntax.history w B z o n r l d f) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (PacketReaderHistorySyntax.history w B z o n t l e g) := .hyp (Or.inl rfl)
  exact PacketReaderHistoryUnique.endpoints hZ w B z o n r t l d e f g h0 h1 h2 h3

theorem packetReaderHistoryAppendSameInternalLengthEndpointsUnique_kernel_certificate {m} (w B z o n r t l d e f g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderHistoryAppendSameInternalLengthEndpointsUniqueSentence w B z o n r t l d e f g)) := TheoryTransport.sentence (source_packetReaderHistoryAppendSameInternalLengthEndpointsUnique w B z o n r t l d e f g)

theorem native_packetReaderHistoryAppendSameInternalLengthEndpointsUnique {m} (w B z o n r t l d e f g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderHistoryAppendSameInternalLengthEndpointsUniqueSentence w B z o n r t l d e f g)) := ZFReplay.replay (packetReaderHistoryAppendSameInternalLengthEndpointsUnique_kernel_certificate w B z o n r t l d e f g)

def packetReaderHistoryAppendOriginalLiteralAllIndexAgreementSentence {m} (w B z o n r t l d k e f g : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 128 B).imp ((PacketReaderHistorySyntax.history w B z o n r l d f).imp ((PacketReaderHistorySyntax.history w B z o n t k e g).imp ((PacketReaderHistoryAgreementSyntax.allAgreement w f g)))))).close

theorem source_packetReaderHistoryAppendOriginalLiteralAllIndexAgreement {m} (w B z o n r t l d k e f g : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderHistoryAppendOriginalLiteralAllIndexAgreementSentence w B z o n r t l d k e f g) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderHistorySyntax.history w B z o n t k e g) (Context.add (PacketReaderHistorySyntax.history w B z o n r l d f) (Context.add (SyntaxNumeralSyntax.numeral 128 B) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 128 B) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (PacketReaderHistorySyntax.history w B z o n r l d f) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (PacketReaderHistorySyntax.history w B z o n t k e g) := .hyp (Or.inl rfl)
  exact PacketReaderHistoryAgreementInduction.all_agreement hZ w B z o n r t l d k e f g h0 (SyntaxNumerals.range hZ 128 w B h0 h1) h2 h3

theorem packetReaderHistoryAppendOriginalLiteralAllIndexAgreement_kernel_certificate {m} (w B z o n r t l d k e f g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderHistoryAppendOriginalLiteralAllIndexAgreementSentence w B z o n r t l d k e f g)) := TheoryTransport.sentence (source_packetReaderHistoryAppendOriginalLiteralAllIndexAgreement w B z o n r t l d k e f g)

theorem native_packetReaderHistoryAppendOriginalLiteralAllIndexAgreement {m} (w B z o n r t l d k e f g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderHistoryAppendOriginalLiteralAllIndexAgreementSentence w B z o n r t l d k e f g)) := ZFReplay.replay (packetReaderHistoryAppendOriginalLiteralAllIndexAgreement_kernel_certificate w B z o n r t l d k e f g)

def packetReaderHistoryAppendRawStateCodesConstructActualExtensionSentence {m} (w B z o n r s l d e f L V S A x y q c : Fin m) : Source.Sentence := ((omega w).imp ((PacketReaderHistorySyntax.history w B z o n r l d f).imp ((PacketReaderStateSyntax.code w L V S A r).imp ((PacketReaderStateSyntax.code w x y q c s).imp ((PacketReaderInputSyntax.advance w B z o L V S A x y q c).imp ((successor e d).imp ((PacketReaderHistoryAppend.extension w B z o n s d e f)))))))).close

theorem source_packetReaderHistoryAppendRawStateCodesConstructActualExtension {m} (w B z o n r s l d e f L V S A x y q c : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderHistoryAppendRawStateCodesConstructActualExtensionSentence w B z o n r s l d e f L V S A x y q c) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor e d) (Context.add (PacketReaderInputSyntax.advance w B z o L V S A x y q c) (Context.add (PacketReaderStateSyntax.code w x y q c s) (Context.add (PacketReaderStateSyntax.code w L V S A r) (Context.add (PacketReaderHistorySyntax.history w B z o n r l d f) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
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
  have h2 : Derives Δ (PacketReaderStateSyntax.code w L V S A r) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (PacketReaderStateSyntax.code w x y q c s) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (PacketReaderInputSyntax.advance w B z o L V S A x y q c) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (successor e d) := .hyp (Or.inl rfl)
  exact PacketReaderHistoryAppend.exists_extension hZ w B z o n r s l d e f h0 h1 (PacketReaderCodedSyntax.intro_step w B z o r s L V S A x y q c h2 h3 h4) h5

theorem packetReaderHistoryAppendRawStateCodesConstructActualExtension_kernel_certificate {m} (w B z o n r s l d e f L V S A x y q c : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderHistoryAppendRawStateCodesConstructActualExtensionSentence w B z o n r s l d e f L V S A x y q c)) := TheoryTransport.sentence (source_packetReaderHistoryAppendRawStateCodesConstructActualExtension w B z o n r s l d e f L V S A x y q c)

theorem native_packetReaderHistoryAppendRawStateCodesConstructActualExtension {m} (w B z o n r s l d e f L V S A x y q c : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderHistoryAppendRawStateCodesConstructActualExtensionSentence w B z o n r s l d e f L V S A x y q c)) := ZFReplay.replay (packetReaderHistoryAppendRawStateCodesConstructActualExtension_kernel_certificate w B z o n r s l d e f L V S A x y q c)

end PPAC.Migration.Internal.ObjectPacketReaderHistoryAppend
