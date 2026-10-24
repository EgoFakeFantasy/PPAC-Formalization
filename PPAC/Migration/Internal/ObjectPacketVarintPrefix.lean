import PPAC.Migration.Internal.PacketVarintPrefixConstruct

/-! Independent zero-seeded canonical LEB128 dual graphs, terminal/nonzero continuation closure and exact-tail byte prefix constructors. Reverse recurrence, all-internal canonical correctness, original varint/readTokens bridge, Basic AST, Proof and Con remain unproved -/
namespace PPAC.Migration.Internal.ObjectPacketVarintPrefix
open Source SourceAlgebra SourceLogic OmegaSyntax

def packetVarintTerminalCellConstructedSentence {m} (w B x h z : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem B w).imp ((StructuralListSyntax.nilCode w x).imp ((empty z).imp ((Formula.mem h B).imp ((PacketVarintCellSyntax.cell w B x h z h))))))).close

theorem source_packetVarintTerminalCellConstructed {m} (w B x h z : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetVarintTerminalCellConstructedSentence w B x h z) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem h B) (Context.add (empty z) (Context.add (StructuralListSyntax.nilCode w x) (Context.add (Formula.mem B w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (Formula.mem B w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (StructuralListSyntax.nilCode w x) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (empty z) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (Formula.mem h B) := .hyp (Or.inl rfl)
  exact PacketVarintCell.terminal_cell hZ w B x h z h0 h1 h2 h3 h4

theorem packetVarintTerminalCellConstructed_kernel_certificate {m} (w B x h z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetVarintTerminalCellConstructedSentence w B x h z)) := TheoryTransport.sentence (source_packetVarintTerminalCellConstructed w B x h z)

theorem native_packetVarintTerminalCellConstructed {m} (w B x h z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetVarintTerminalCellConstructedSentence w B x h z)) := ZFReplay.replay (packetVarintTerminalCellConstructed_kernel_certificate w B x h z)

def packetVarintNonzeroContinuationCellConstructedSentence {m} (w B x h u v d : Fin m) : Source.Sentence := ((omega w).imp (((empty u).neg).imp ((PacketAffineSyntax.affine w B d u v).imp ((NaturalAdditionSyntax.sum w d B h).imp ((PacketVarintCellSyntax.cell w B x h u v)))))).close

theorem source_packetVarintNonzeroContinuationCellConstructed {m} (w B x h u v d : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetVarintNonzeroContinuationCellConstructedSentence w B x h u v d) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (NaturalAdditionSyntax.sum w d B h) (Context.add (PacketAffineSyntax.affine w B d u v) (Context.add ((empty u).neg) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ ((empty u).neg) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (PacketAffineSyntax.affine w B d u v) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (NaturalAdditionSyntax.sum w d B h) := .hyp (Or.inl rfl)
  exact PacketVarintCell.continuation_cell hZ w B x h u v d h0 h1 h2 h3

theorem packetVarintNonzeroContinuationCellConstructed_kernel_certificate {m} (w B x h u v d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetVarintNonzeroContinuationCellConstructedSentence w B x h u v d)) := TheoryTransport.sentence (source_packetVarintNonzeroContinuationCellConstructed w B x h u v d)

theorem native_packetVarintNonzeroContinuationCellConstructed {m} (w B x h u v d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetVarintNonzeroContinuationCellConstructedSentence w B x h u v d)) := ZFReplay.replay (packetVarintNonzeroContinuationCellConstructed_kernel_certificate w B x h u v d)

def packetVarintContinuationRequiresNonzeroValueSentence {m} (w B h u v : Fin m) : Source.Sentence := ((PacketVarintCellSyntax.continuation w B h u v).imp (((empty u).neg))).close

theorem source_packetVarintContinuationRequiresNonzeroValue {m} (w B h u v : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetVarintContinuationRequiresNonzeroValueSentence w B h u v) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (PacketVarintCellSyntax.continuation w B h u v) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (PacketVarintCellSyntax.continuation w B h u v) := .hyp (Or.inl rfl)
  exact PacketVarintCellLaws.continuation_nonzero w B h u v h0

theorem packetVarintContinuationRequiresNonzeroValue_kernel_certificate {m} (w B h u v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetVarintContinuationRequiresNonzeroValueSentence w B h u v)) := TheoryTransport.sentence (source_packetVarintContinuationRequiresNonzeroValue w B h u v)

theorem native_packetVarintContinuationRequiresNonzeroValue {m} (w B h u v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetVarintContinuationRequiresNonzeroValueSentence w B h u v)) := ZFReplay.replay (packetVarintContinuationRequiresNonzeroValue_kernel_certificate w B h u v)

def packetVarintTerminalContinuationDisjointSentence {m} (w B x h u v : Fin m) : Source.Sentence := ((PacketVarintCellSyntax.terminal w B x h u v).imp ((PacketVarintCellSyntax.continuation w B h u v).imp ((Formula.bot)))).close

theorem source_packetVarintTerminalContinuationDisjoint {m} (w B x h u v : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetVarintTerminalContinuationDisjointSentence w B x h u v) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketVarintCellSyntax.continuation w B h u v) (Context.add (PacketVarintCellSyntax.terminal w B x h u v) (Source.SetLanguage.ZF.at m))
  have h0 : Derives Δ (PacketVarintCellSyntax.terminal w B x h u v) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PacketVarintCellSyntax.continuation w B h u v) := .hyp (Or.inl rfl)
  exact PacketVarintCellLaws.terminal_continuation_disjoint w B x h u v h0 h1

theorem packetVarintTerminalContinuationDisjoint_kernel_certificate {m} (w B x h u v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetVarintTerminalContinuationDisjointSentence w B x h u v)) := TheoryTransport.sentence (source_packetVarintTerminalContinuationDisjoint w B x h u v)

theorem native_packetVarintTerminalContinuationDisjoint {m} (w B x h u v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetVarintTerminalContinuationDisjointSentence w B x h u v)) := ZFReplay.replay (packetVarintTerminalContinuationDisjoint_kernel_certificate w B x h u v)

def packetVarintZeroPriorForcesActualTerminalSentence {m} (w B x h u v : Fin m) : Source.Sentence := ((empty u).imp ((PacketVarintCellSyntax.cell w B x h u v).imp ((PacketVarintCellSyntax.terminal w B x h u v)))).close

theorem source_packetVarintZeroPriorForcesActualTerminal {m} (w B x h u v : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetVarintZeroPriorForcesActualTerminalSentence w B x h u v) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketVarintCellSyntax.cell w B x h u v) (Context.add (empty u) (Source.SetLanguage.ZF.at m))
  have h0 : Derives Δ (empty u) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PacketVarintCellSyntax.cell w B x h u v) := .hyp (Or.inl rfl)
  exact PacketVarintCellLaws.zero_forces_terminal w B x h u v h0 h1

theorem packetVarintZeroPriorForcesActualTerminal_kernel_certificate {m} (w B x h u v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetVarintZeroPriorForcesActualTerminalSentence w B x h u v)) := TheoryTransport.sentence (source_packetVarintZeroPriorForcesActualTerminal w B x h u v)

theorem native_packetVarintZeroPriorForcesActualTerminal {m} (w B x h u v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetVarintZeroPriorForcesActualTerminalSentence w B x h u v)) := ZFReplay.replay (packetVarintZeroPriorForcesActualTerminal_kernel_certificate w B x h u v)

def packetVarintNonemptyListForcesActualContinuationSentence {m} (w B x h u v : Fin m) : Source.Sentence := (((StructuralListSyntax.nilCode w x).neg).imp ((PacketVarintCellSyntax.cell w B x h u v).imp ((PacketVarintCellSyntax.continuation w B h u v)))).close

theorem source_packetVarintNonemptyListForcesActualContinuation {m} (w B x h u v : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetVarintNonemptyListForcesActualContinuationSentence w B x h u v) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketVarintCellSyntax.cell w B x h u v) (Context.add ((StructuralListSyntax.nilCode w x).neg) (Source.SetLanguage.ZF.at m))
  have h0 : Derives Δ ((StructuralListSyntax.nilCode w x).neg) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PacketVarintCellSyntax.cell w B x h u v) := .hyp (Or.inl rfl)
  exact PacketVarintCellLaws.nonempty_previous_forces_continuation w B x h u v h0 h1

theorem packetVarintNonemptyListForcesActualContinuation_kernel_certificate {m} (w B x h u v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetVarintNonemptyListForcesActualContinuationSentence w B x h u v)) := TheoryTransport.sentence (source_packetVarintNonemptyListForcesActualContinuation w B x h u v)

theorem native_packetVarintNonemptyListForcesActualContinuation {m} (w B x h u v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetVarintNonemptyListForcesActualContinuationSentence w B x h u v)) := ZFReplay.replay (packetVarintNonemptyListForcesActualContinuation_kernel_certificate w B x h u v)

def packetVarintEveryActualCellByteBoundSentence {m} (w B C x h u v : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 128 B).imp ((SyntaxNumeralSyntax.numeral 256 C).imp ((PacketVarintCellSyntax.cell w B x h u v).imp ((Formula.mem h C)))))).close

theorem source_packetVarintEveryActualCellByteBound {m} (w B C x h u v : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetVarintEveryActualCellByteBoundSentence w B C x h u v) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketVarintCellSyntax.cell w B x h u v) (Context.add (SyntaxNumeralSyntax.numeral 256 C) (Context.add (SyntaxNumeralSyntax.numeral 128 B) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 128 B) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral 256 C) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (PacketVarintCellSyntax.cell w B x h u v) := .hyp (Or.inl rfl)
  exact PacketVarintCellLaws.cell_byte_bound hZ w B C x h u v h0 h1 h2 h3

theorem packetVarintEveryActualCellByteBound_kernel_certificate {m} (w B C x h u v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetVarintEveryActualCellByteBoundSentence w B C x h u v)) := TheoryTransport.sentence (source_packetVarintEveryActualCellByteBound w B C x h u v)

theorem native_packetVarintEveryActualCellByteBound {m} (w B C x h u v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetVarintEveryActualCellByteBoundSentence w B C x h u v)) := ZFReplay.replay (packetVarintEveryActualCellByteBound_kernel_certificate w B C x h u v)

def packetVarintBothOriginalGraphsRowTransportSentence {m} (w B f g F G i : Fin m) : Source.Sentence := ((GraphPointwiseSyntax.edgeIncluded f F).imp ((GraphPointwiseSyntax.edgeIncluded g G).imp ((PacketVarintRowSyntax.row w B f g i).imp ((PacketVarintRowSyntax.row w B F G i))))).close

theorem source_packetVarintBothOriginalGraphsRowTransport {m} (w B f g F G i : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetVarintBothOriginalGraphsRowTransportSentence w B f g F G i) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketVarintRowSyntax.row w B f g i) (Context.add (GraphPointwiseSyntax.edgeIncluded g G) (Context.add (GraphPointwiseSyntax.edgeIncluded f F) (Source.SetLanguage.ZF.at m)))
  have h0 : Derives Δ (GraphPointwiseSyntax.edgeIncluded f F) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (GraphPointwiseSyntax.edgeIncluded g G) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (PacketVarintRowSyntax.row w B f g i) := .hyp (Or.inl rfl)
  exact PacketVarintRowMap.row_map w B f g F G i h0 h1 h2

theorem packetVarintBothOriginalGraphsRowTransport_kernel_certificate {m} (w B f g F G i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetVarintBothOriginalGraphsRowTransportSentence w B f g F G i)) := TheoryTransport.sentence (source_packetVarintBothOriginalGraphsRowTransport w B f g F G i)

theorem native_packetVarintBothOriginalGraphsRowTransport {m} (w B f g F G i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetVarintBothOriginalGraphsRowTransportSentence w B f g F G i)) := ZFReplay.replay (packetVarintBothOriginalGraphsRowTransport_kernel_certificate w B f g F G i)

def packetVarintFullOldRowsAndNewLastRowPreservedSentence {m} (w B l d f g F G : Fin m) : Source.Sentence := ((successor d l).imp ((PacketVarintRowSyntax.links w B l f g).imp ((GraphPointwiseSyntax.edgeIncluded f F).imp ((GraphPointwiseSyntax.edgeIncluded g G).imp ((PacketVarintRowSyntax.row w B F G l).imp ((PacketVarintRowSyntax.links w B d F G))))))).close

theorem source_packetVarintFullOldRowsAndNewLastRowPreserved {m} (w B l d f g F G : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetVarintFullOldRowsAndNewLastRowPreservedSentence w B l d f g F G) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketVarintRowSyntax.row w B F G l) (Context.add (GraphPointwiseSyntax.edgeIncluded g G) (Context.add (GraphPointwiseSyntax.edgeIncluded f F) (Context.add (PacketVarintRowSyntax.links w B l f g) (Context.add (successor d l) (Source.SetLanguage.ZF.at m)))))
  have h0 : Derives Δ (successor d l) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (PacketVarintRowSyntax.links w B l f g) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (GraphPointwiseSyntax.edgeIncluded f F) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (GraphPointwiseSyntax.edgeIncluded g G) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (PacketVarintRowSyntax.row w B F G l) := .hyp (Or.inl rfl)
  exact PacketVarintRowMap.append_links w B l d f g F G h0 h1 h2 h3 h4

theorem packetVarintFullOldRowsAndNewLastRowPreserved_kernel_certificate {m} (w B l d f g F G : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetVarintFullOldRowsAndNewLastRowPreservedSentence w B l d f g F G)) := TheoryTransport.sentence (source_packetVarintFullOldRowsAndNewLastRowPreserved w B l d f g F G)

theorem native_packetVarintFullOldRowsAndNewLastRowPreserved {m} (w B l d f g F G : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetVarintFullOldRowsAndNewLastRowPreservedSentence w B l d f g F G)) := ZFReplay.replay (packetVarintFullOldRowsAndNewLastRowPreserved_kernel_certificate w B l d f g F G)

def packetVarintRealDualSequenceExtensionSentence {m} (w B n t a h p b : Fin m) : Source.Sentence := ((omega w).imp ((PacketVarintTraceSyntax.foldAt w B n t a).imp ((StructuralListSyntax.consCode w h n p).imp ((PacketVarintCellSyntax.cell w B n h a b).imp ((PacketVarintTraceSyntax.foldAt w B p t b)))))).close

theorem source_packetVarintRealDualSequenceExtension {m} (w B n t a h p b : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetVarintRealDualSequenceExtensionSentence w B n t a h p b) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketVarintCellSyntax.cell w B n h a b) (Context.add (StructuralListSyntax.consCode w h n p) (Context.add (PacketVarintTraceSyntax.foldAt w B n t a) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (PacketVarintTraceSyntax.foldAt w B n t a) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (StructuralListSyntax.consCode w h n p) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (PacketVarintCellSyntax.cell w B n h a b) := .hyp (Or.inl rfl)
  exact PacketVarintTraceAppend.cons_fold hZ w B n t a h p b h0 h1 h2 h3

theorem packetVarintRealDualSequenceExtension_kernel_certificate {m} (w B n t a h p b : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetVarintRealDualSequenceExtensionSentence w B n t a h p b)) := TheoryTransport.sentence (source_packetVarintRealDualSequenceExtension w B n t a h p b)

theorem native_packetVarintRealDualSequenceExtension {m} (w B n t a h p b : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetVarintRealDualSequenceExtensionSentence w B n t a h p b)) := ZFReplay.replay (packetVarintRealDualSequenceExtension_kernel_certificate w B n t a h p b)

def packetVarintEmptyTraceExactNaturalSeedSentence {m} (w B n t a : Fin m) : Source.Sentence := ((omega w).imp ((StructuralListSyntax.nilCode w n).imp (((PacketVarintTraceSyntax.foldAt w B n t a).iff ((Formula.mem t w).conj (.equal t a)))))).close

theorem source_packetVarintEmptyTraceExactNaturalSeed {m} (w B n t a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetVarintEmptyTraceExactNaturalSeedSentence w B n t a) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralListSyntax.nilCode w n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (StructuralListSyntax.nilCode w n) := .hyp (Or.inl rfl)
  exact PacketVarintTraceBase.nil_iff hZ w B n t a h0 h1

theorem packetVarintEmptyTraceExactNaturalSeed_kernel_certificate {m} (w B n t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetVarintEmptyTraceExactNaturalSeedSentence w B n t a)) := TheoryTransport.sentence (source_packetVarintEmptyTraceExactNaturalSeed w B n t a)

theorem native_packetVarintEmptyTraceExactNaturalSeed {m} (w B n t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetVarintEmptyTraceExactNaturalSeedSentence w B n t a)) := ZFReplay.replay (packetVarintEmptyTraceExactNaturalSeed_kernel_certificate w B n t a)

def packetVarintIndependentCanonicalAtDomainSentence {m} (w B n s : Fin m) : Source.Sentence := ((PacketVarintSyntax.canonicalAt w B n s).imp (((Formula.mem n w).conj ((StructuralListTraceSyntax.valid w s).conj (StructuralListSyntax.nilCode w s).neg)))).close

theorem source_packetVarintIndependentCanonicalAtDomain {m} (w B n s : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetVarintIndependentCanonicalAtDomainSentence w B n s) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (PacketVarintSyntax.canonicalAt w B n s) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (PacketVarintSyntax.canonicalAt w B n s) := .hyp (Or.inl rfl)
  exact PacketVarintDomain.at_domain w B n s h0

theorem packetVarintIndependentCanonicalAtDomain_kernel_certificate {m} (w B n s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetVarintIndependentCanonicalAtDomainSentence w B n s)) := TheoryTransport.sentence (source_packetVarintIndependentCanonicalAtDomain w B n s)

theorem native_packetVarintIndependentCanonicalAtDomain {m} (w B n s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetVarintIndependentCanonicalAtDomainSentence w B n s)) := ZFReplay.replay (packetVarintIndependentCanonicalAtDomain_kernel_certificate w B n s)

def packetVarintIndependentActualCanonicalDomainSentence {m} (w n s : Fin m) : Source.Sentence := ((PacketVarintSyntax.canonical w n s).imp (((Formula.mem n w).conj ((StructuralListTraceSyntax.valid w s).conj (StructuralListSyntax.nilCode w s).neg)))).close

theorem source_packetVarintIndependentActualCanonicalDomain {m} (w n s : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetVarintIndependentActualCanonicalDomainSentence w n s) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (PacketVarintSyntax.canonical w n s) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (PacketVarintSyntax.canonical w n s) := .hyp (Or.inl rfl)
  exact PacketVarintDomain.domain w n s h0

theorem packetVarintIndependentActualCanonicalDomain_kernel_certificate {m} (w n s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetVarintIndependentActualCanonicalDomainSentence w n s)) := TheoryTransport.sentence (source_packetVarintIndependentActualCanonicalDomain w n s)

theorem native_packetVarintIndependentActualCanonicalDomain {m} (w n s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetVarintIndependentActualCanonicalDomainSentence w n s)) := ZFReplay.replay (packetVarintIndependentActualCanonicalDomain_kernel_certificate w n s)

def packetVarintActual128ExactGraphIffSentence {m} (w B n s : Fin m) : Source.Sentence := ((SyntaxNumeralSyntax.numeral 128 B).imp (((PacketVarintSyntax.canonical w n s).iff (PacketVarintSyntax.canonicalAt w B n s)))).close

theorem source_packetVarintActual128ExactGraphIff {m} (w B n s : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetVarintActual128ExactGraphIffSentence w B n s) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNumeralSyntax.numeral 128 B) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (SyntaxNumeralSyntax.numeral 128 B) := .hyp (Or.inl rfl)
  exact PacketVarintDomain.actual_iff hZ w B n s h0

theorem packetVarintActual128ExactGraphIff_kernel_certificate {m} (w B n s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetVarintActual128ExactGraphIffSentence w B n s)) := TheoryTransport.sentence (source_packetVarintActual128ExactGraphIff w B n s)

theorem native_packetVarintActual128ExactGraphIff {m} (w B n s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetVarintActual128ExactGraphIffSentence w B n s)) := ZFReplay.replay (packetVarintActual128ExactGraphIff_kernel_certificate w B n s)

def packetVarintCanonicalTerminalActualGraphsSentence {m} (w B n e s : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 128 B).imp ((Formula.mem n B).imp ((StructuralListSyntax.nilCode w e).imp ((StructuralListSyntax.consCode w n e s).imp ((PacketVarintSyntax.canonical w n s))))))).close

theorem source_packetVarintCanonicalTerminalActualGraphs {m} (w B n e s : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetVarintCanonicalTerminalActualGraphsSentence w B n e s) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralListSyntax.consCode w n e s) (Context.add (StructuralListSyntax.nilCode w e) (Context.add (Formula.mem n B) (Context.add (SyntaxNumeralSyntax.numeral 128 B) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 128 B) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (Formula.mem n B) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (StructuralListSyntax.nilCode w e) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (StructuralListSyntax.consCode w n e s) := .hyp (Or.inl rfl)
  exact PacketVarintConstruct.terminal hZ w B n e s h0 h1 h2 h3 h4

theorem packetVarintCanonicalTerminalActualGraphs_kernel_certificate {m} (w B n e s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetVarintCanonicalTerminalActualGraphsSentence w B n e s)) := TheoryTransport.sentence (source_packetVarintCanonicalTerminalActualGraphs w B n e s)

theorem native_packetVarintCanonicalTerminalActualGraphs {m} (w B n e s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetVarintCanonicalTerminalActualGraphsSentence w B n e s)) := ZFReplay.replay (packetVarintCanonicalTerminalActualGraphs_kernel_certificate w B n e s)

def packetVarintCanonicalNonzeroContinuationActualGraphsSentence {m} (w B q s d h n p : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 128 B).imp (((empty q).neg).imp ((PacketVarintSyntax.canonical w q s).imp ((PacketAffineSyntax.affine w B d q n).imp ((NaturalAdditionSyntax.sum w d B h).imp ((StructuralListSyntax.consCode w h s p).imp ((PacketVarintSyntax.canonical w n p))))))))).close

theorem source_packetVarintCanonicalNonzeroContinuationActualGraphs {m} (w B q s d h n p : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetVarintCanonicalNonzeroContinuationActualGraphsSentence w B q s d h n p) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralListSyntax.consCode w h s p) (Context.add (NaturalAdditionSyntax.sum w d B h) (Context.add (PacketAffineSyntax.affine w B d q n) (Context.add (PacketVarintSyntax.canonical w q s) (Context.add ((empty q).neg) (Context.add (SyntaxNumeralSyntax.numeral 128 B) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))
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
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 128 B) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h2 : Derives Δ ((empty q).neg) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h3 : Derives Δ (PacketVarintSyntax.canonical w q s) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : Derives Δ (PacketAffineSyntax.affine w B d q n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h5 : Derives Δ (NaturalAdditionSyntax.sum w d B h) := .hyp (Or.inr (Or.inl rfl))
  have h6 : Derives Δ (StructuralListSyntax.consCode w h s p) := .hyp (Or.inl rfl)
  exact PacketVarintConstruct.continuation hZ w B q s d h n p h0 h1 h2 h3 h4 h5 h6

theorem packetVarintCanonicalNonzeroContinuationActualGraphs_kernel_certificate {m} (w B q s d h n p : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetVarintCanonicalNonzeroContinuationActualGraphsSentence w B q s d h n p)) := TheoryTransport.sentence (source_packetVarintCanonicalNonzeroContinuationActualGraphs w B q s d h n p)

theorem native_packetVarintCanonicalNonzeroContinuationActualGraphs {m} (w B q s d h n p : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetVarintCanonicalNonzeroContinuationActualGraphsSentence w B q s d h n p)) := ZFReplay.replay (packetVarintCanonicalNonzeroContinuationActualGraphs_kernel_certificate w B q s d h n p)

def packetVarintCanonicalRejectsActualNilSentence {m} (w n s : Fin m) : Source.Sentence := ((StructuralListSyntax.nilCode w s).imp (((PacketVarintSyntax.canonical w n s).neg))).close

theorem source_packetVarintCanonicalRejectsActualNil {m} (w n s : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetVarintCanonicalRejectsActualNilSentence w n s) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralListSyntax.nilCode w s) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (StructuralListSyntax.nilCode w s) := .hyp (Or.inl rfl)
  exact PacketVarintDomain.reject_nil w n s h0

theorem packetVarintCanonicalRejectsActualNil_kernel_certificate {m} (w n s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetVarintCanonicalRejectsActualNilSentence w n s)) := TheoryTransport.sentence (source_packetVarintCanonicalRejectsActualNil w n s)

theorem native_packetVarintCanonicalRejectsActualNil {m} (w n s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetVarintCanonicalRejectsActualNilSentence w n s)) := ZFReplay.replay (packetVarintCanonicalRejectsActualNil_kernel_certificate w n s)

def packetVarintIndependentPrefixExactNumericDomainSentence {m} (w n t a : Fin m) : Source.Sentence := ((PacketVarintPrefixSyntax.prefixCode w n t a).imp (((Formula.mem n w).conj ((Formula.mem t w).conj (.mem a w))))).close

theorem source_packetVarintIndependentPrefixExactNumericDomain {m} (w n t a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetVarintIndependentPrefixExactNumericDomainSentence w n t a) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (PacketVarintPrefixSyntax.prefixCode w n t a) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (PacketVarintPrefixSyntax.prefixCode w n t a) := .hyp (Or.inl rfl)
  exact PacketVarintPrefixDomain.domain w n t a h0

theorem packetVarintIndependentPrefixExactNumericDomain_kernel_certificate {m} (w n t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetVarintIndependentPrefixExactNumericDomainSentence w n t a)) := TheoryTransport.sentence (source_packetVarintIndependentPrefixExactNumericDomain w n t a)

theorem native_packetVarintIndependentPrefixExactNumericDomain {m} (w n t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetVarintIndependentPrefixExactNumericDomainSentence w n t a)) := ZFReplay.replay (packetVarintIndependentPrefixExactNumericDomain_kernel_certificate w n t a)

def packetVarintTerminalPrefixAllCodeWitnessesEliminatedSentence {m} (w B n t a : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 128 B).imp ((Formula.mem n B).imp ((PacketAffineAcceptedSyntax.accepted true w n t a).imp ((PacketVarintPrefixSyntax.prefixCode w n t a)))))).close

theorem source_packetVarintTerminalPrefixAllCodeWitnessesEliminated {m} (w B n t a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetVarintTerminalPrefixAllCodeWitnessesEliminatedSentence w B n t a) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketAffineAcceptedSyntax.accepted true w n t a) (Context.add (Formula.mem n B) (Context.add (SyntaxNumeralSyntax.numeral 128 B) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 128 B) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (Formula.mem n B) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (PacketAffineAcceptedSyntax.accepted true w n t a) := .hyp (Or.inl rfl)
  exact PacketVarintPrefixConstruct.terminal hZ w B n t a h0 h1 h2 h3

theorem packetVarintTerminalPrefixAllCodeWitnessesEliminated_kernel_certificate {m} (w B n t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetVarintTerminalPrefixAllCodeWitnessesEliminatedSentence w B n t a)) := TheoryTransport.sentence (source_packetVarintTerminalPrefixAllCodeWitnessesEliminated w B n t a)

theorem native_packetVarintTerminalPrefixAllCodeWitnessesEliminated {m} (w B n t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetVarintTerminalPrefixAllCodeWitnessesEliminatedSentence w B n t a)) := ZFReplay.replay (packetVarintTerminalPrefixAllCodeWitnessesEliminated_kernel_certificate w B n t a)

def packetVarintContinuationPrefixAllCodeWitnessesEliminatedSentence {m} (w B q t u d h n a : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 128 B).imp (((empty q).neg).imp ((PacketVarintPrefixSyntax.prefixCode w q t u).imp ((PacketAffineSyntax.affine w B d q n).imp ((NaturalAdditionSyntax.sum w d B h).imp ((PacketAffineAcceptedSyntax.accepted true w h u a).imp ((PacketVarintPrefixSyntax.prefixCode w n t a))))))))).close

theorem source_packetVarintContinuationPrefixAllCodeWitnessesEliminated {m} (w B q t u d h n a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetVarintContinuationPrefixAllCodeWitnessesEliminatedSentence w B q t u d h n a) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketAffineAcceptedSyntax.accepted true w h u a) (Context.add (NaturalAdditionSyntax.sum w d B h) (Context.add (PacketAffineSyntax.affine w B d q n) (Context.add (PacketVarintPrefixSyntax.prefixCode w q t u) (Context.add ((empty q).neg) (Context.add (SyntaxNumeralSyntax.numeral 128 B) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))
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
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 128 B) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h2 : Derives Δ ((empty q).neg) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h3 : Derives Δ (PacketVarintPrefixSyntax.prefixCode w q t u) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : Derives Δ (PacketAffineSyntax.affine w B d q n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h5 : Derives Δ (NaturalAdditionSyntax.sum w d B h) := .hyp (Or.inr (Or.inl rfl))
  have h6 : Derives Δ (PacketAffineAcceptedSyntax.accepted true w h u a) := .hyp (Or.inl rfl)
  exact PacketVarintPrefixConstruct.continuation hZ w B q t u d h n a h0 h1 h2 h3 h4 h5 h6

theorem packetVarintContinuationPrefixAllCodeWitnessesEliminated_kernel_certificate {m} (w B q t u d h n a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetVarintContinuationPrefixAllCodeWitnessesEliminatedSentence w B q t u d h n a)) := TheoryTransport.sentence (source_packetVarintContinuationPrefixAllCodeWitnessesEliminated w B q t u d h n a)

theorem native_packetVarintContinuationPrefixAllCodeWitnessesEliminated {m} (w B q t u d h n a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetVarintContinuationPrefixAllCodeWitnessesEliminatedSentence w B q t u d h n a)) := ZFReplay.replay (packetVarintContinuationPrefixAllCodeWitnessesEliminated_kernel_certificate w B q t u d h n a)

end PPAC.Migration.Internal.ObjectPacketVarintPrefix
