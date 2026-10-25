import PPAC.Migration.Internal.PacketReaderEval

/-! Original Replacement constructs exact prepend sequences and real longer histories; whole runs and actual four-field evaluations obey the original step/terminal equations. Full varint segmentation, program/specification bridge, Basic AST, Proof and Con remain unproved -/
namespace PPAC.Migration.Internal.ObjectPacketReaderRecursion
open Source SourceAlgebra SourceLogic OmegaSyntax

def packetReaderRecursionPrependZeroValueExactSentence {m} (f d n i y : Fin m) : Source.Sentence := ((empty i).imp (((SequencePrependSyntax.value f d n i y).iff (Formula.equal y n)))).close

theorem source_packetReaderRecursionPrependZeroValueExact {m} (f d n i y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderRecursionPrependZeroValueExactSentence f d n i y) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (empty i) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (empty i) := .hyp (Or.inl rfl)
  exact SequencePrependValues.at_zero f d n i y h0

theorem packetReaderRecursionPrependZeroValueExact_kernel_certificate {m} (f d n i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderRecursionPrependZeroValueExactSentence f d n i y)) := TheoryTransport.sentence (source_packetReaderRecursionPrependZeroValueExact f d n i y)

theorem native_packetReaderRecursionPrependZeroValueExact {m} (f d n i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderRecursionPrependZeroValueExactSentence f d n i y)) := ZFReplay.replay (packetReaderRecursionPrependZeroValueExact_kernel_certificate f d n i y)

def packetReaderRecursionPrependSuccessorValueExactSentence {m} (w f d n i j y : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem d w).imp ((successor i j).imp (((SequencePrependSyntax.value f d n i y).iff ((Formula.mem j d).conj (GraphSyntax.edge f j y))))))).close

theorem source_packetReaderRecursionPrependSuccessorValueExact {m} (w f d n i j y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderRecursionPrependSuccessorValueExactSentence w f d n i j y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor i j) (Context.add (Formula.mem d w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (Formula.mem d w) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (successor i j) := .hyp (Or.inl rfl)
  exact SequencePrependValues.at_successor hZ w f d n i j y h0 h1 h2

theorem packetReaderRecursionPrependSuccessorValueExact_kernel_certificate {m} (w f d n i j y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderRecursionPrependSuccessorValueExactSentence w f d n i j y)) := TheoryTransport.sentence (source_packetReaderRecursionPrependSuccessorValueExact w f d n i j y)

theorem native_packetReaderRecursionPrependSuccessorValueExact {m} (w f d n i j y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderRecursionPrependSuccessorValueExactSentence w f d n i j y)) := ZFReplay.replay (packetReaderRecursionPrependSuccessorValueExact_kernel_certificate w f d n i j y)

def packetReaderRecursionPrependValueUniqueSentence {m} (w f d n i y z : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem d w).imp ((SequenceSyntax.sequence f d w).imp ((SequencePrependSyntax.value f d n i y).imp ((SequencePrependSyntax.value f d n i z).imp ((Formula.equal y z))))))).close

theorem source_packetReaderRecursionPrependValueUnique {m} (w f d n i y z : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderRecursionPrependValueUniqueSentence w f d n i y z) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SequencePrependSyntax.value f d n i z) (Context.add (SequencePrependSyntax.value f d n i y) (Context.add (SequenceSyntax.sequence f d w) (Context.add (Formula.mem d w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (Formula.mem d w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (SequenceSyntax.sequence f d w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (SequencePrependSyntax.value f d n i y) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (SequencePrependSyntax.value f d n i z) := .hyp (Or.inl rfl)
  exact SequencePrependValues.unique hZ w f d n i y z h0 h1 h2 h3 h4

theorem packetReaderRecursionPrependValueUnique_kernel_certificate {m} (w f d n i y z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderRecursionPrependValueUniqueSentence w f d n i y z)) := TheoryTransport.sentence (source_packetReaderRecursionPrependValueUnique w f d n i y z)

theorem native_packetReaderRecursionPrependValueUnique {m} (w f d n i y z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderRecursionPrependValueUniqueSentence w f d n i y z)) := ZFReplay.replay (packetReaderRecursionPrependValueUnique_kernel_certificate w f d n i y z)

def packetReaderRecursionPrependEveryInternalValueExistsUniqueSentence {m} (w f d n e i : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem d w).imp ((successor e d).imp ((SequenceSyntax.sequence f d w).imp ((Formula.mem i e).imp ((SequencePrependSyntax.valueFiber f d n i))))))).close

theorem source_packetReaderRecursionPrependEveryInternalValueExistsUnique {m} (w f d n e i : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderRecursionPrependEveryInternalValueExistsUniqueSentence w f d n e i) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem i e) (Context.add (SequenceSyntax.sequence f d w) (Context.add (successor e d) (Context.add (Formula.mem d w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (Formula.mem d w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (successor e d) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (SequenceSyntax.sequence f d w) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (Formula.mem i e) := .hyp (Or.inl rfl)
  exact SequencePrependValues.exists_unique hZ w f d n e i h0 h1 h2 h3 h4

theorem packetReaderRecursionPrependEveryInternalValueExistsUnique_kernel_certificate {m} (w f d n e i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderRecursionPrependEveryInternalValueExistsUniqueSentence w f d n e i)) := TheoryTransport.sentence (source_packetReaderRecursionPrependEveryInternalValueExistsUnique w f d n e i)

theorem native_packetReaderRecursionPrependEveryInternalValueExistsUnique {m} (w f d n e i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderRecursionPrependEveryInternalValueExistsUniqueSentence w f d n e i)) := ZFReplay.replay (packetReaderRecursionPrependEveryInternalValueExistsUnique_kernel_certificate w f d n e i)

def packetReaderRecursionPrependValuePreservesActualBoundSentence {m} (f d n w i y : Fin m) : Source.Sentence := ((SequenceSyntax.sequence f d w).imp ((Formula.mem n w).imp ((SequencePrependSyntax.value f d n i y).imp ((Formula.mem y w))))).close

theorem source_packetReaderRecursionPrependValuePreservesActualBound {m} (f d n w i y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderRecursionPrependValuePreservesActualBoundSentence f d n w i y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SequencePrependSyntax.value f d n i y) (Context.add (Formula.mem n w) (Context.add (SequenceSyntax.sequence f d w) (Source.SetLanguage.ZF.at m)))
  have h0 : Derives Δ (SequenceSyntax.sequence f d w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (Formula.mem n w) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SequencePrependSyntax.value f d n i y) := .hyp (Or.inl rfl)
  exact SequencePrependValues.range f d n w i y h0 h1 h2

theorem packetReaderRecursionPrependValuePreservesActualBound_kernel_certificate {m} (f d n w i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderRecursionPrependValuePreservesActualBoundSentence f d n w i y)) := TheoryTransport.sentence (source_packetReaderRecursionPrependValuePreservesActualBound f d n w i y)

theorem native_packetReaderRecursionPrependValuePreservesActualBound {m} (f d n w i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderRecursionPrependValuePreservesActualBoundSentence f d n w i y)) := ZFReplay.replay (packetReaderRecursionPrependValuePreservesActualBound_kernel_certificate f d n w i y)

def packetReaderRecursionOriginalReplacementConstructsExactPrependGraphSentence {m} (w f d n e : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem d w).imp ((successor e d).imp ((SequenceSyntax.sequence f d w).imp ((SequencePrependSyntax.existsGraph f d n e)))))).close

theorem source_packetReaderRecursionOriginalReplacementConstructsExactPrependGraph {m} (w f d n e : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderRecursionOriginalReplacementConstructsExactPrependGraphSentence w f d n e) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SequenceSyntax.sequence f d w) (Context.add (successor e d) (Context.add (Formula.mem d w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (Formula.mem d w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (successor e d) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SequenceSyntax.sequence f d w) := .hyp (Or.inl rfl)
  exact SequencePrependGraph.exists_graph hZ w f d n e h0 h1 h2 h3

theorem packetReaderRecursionOriginalReplacementConstructsExactPrependGraph_kernel_certificate {m} (w f d n e : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderRecursionOriginalReplacementConstructsExactPrependGraphSentence w f d n e)) := TheoryTransport.sentence (source_packetReaderRecursionOriginalReplacementConstructsExactPrependGraph w f d n e)

theorem native_packetReaderRecursionOriginalReplacementConstructsExactPrependGraph {m} (w f d n e : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderRecursionOriginalReplacementConstructsExactPrependGraphSentence w f d n e)) := ZFReplay.replay (packetReaderRecursionOriginalReplacementConstructsExactPrependGraph_kernel_certificate w f d n e)

def packetReaderRecursionPrependGraphIsActualSequenceSentence {m} (w f d n e g : Fin m) : Source.Sentence := ((SequenceSyntax.sequence f d w).imp ((Formula.mem n w).imp ((SequencePrependSyntax.graph f d n e g).imp ((SequenceSyntax.sequence g e w))))).close

theorem source_packetReaderRecursionPrependGraphIsActualSequence {m} (w f d n e g : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderRecursionPrependGraphIsActualSequenceSentence w f d n e g) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SequencePrependSyntax.graph f d n e g) (Context.add (Formula.mem n w) (Context.add (SequenceSyntax.sequence f d w) (Source.SetLanguage.ZF.at m)))
  have h0 : Derives Δ (SequenceSyntax.sequence f d w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (Formula.mem n w) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SequencePrependSyntax.graph f d n e g) := .hyp (Or.inl rfl)
  exact SequencePrependGraph.sequence w f d n e g h0 h1 h2

theorem packetReaderRecursionPrependGraphIsActualSequence_kernel_certificate {m} (w f d n e g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderRecursionPrependGraphIsActualSequenceSentence w f d n e g)) := TheoryTransport.sentence (source_packetReaderRecursionPrependGraphIsActualSequence w f d n e g)

theorem native_packetReaderRecursionPrependGraphIsActualSequence {m} (w f d n e g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderRecursionPrependGraphIsActualSequenceSentence w f d n e g)) := ZFReplay.replay (packetReaderRecursionPrependGraphIsActualSequence_kernel_certificate w f d n e g)

def packetReaderRecursionPrependGraphUniqueSentence {m} (f d n e g h : Fin m) : Source.Sentence := ((SequencePrependSyntax.graph f d n e g).imp ((SequencePrependSyntax.graph f d n e h).imp ((Formula.equal g h)))).close

theorem source_packetReaderRecursionPrependGraphUnique {m} (f d n e g h : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderRecursionPrependGraphUniqueSentence f d n e g h) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SequencePrependSyntax.graph f d n e h) (Context.add (SequencePrependSyntax.graph f d n e g) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (SequencePrependSyntax.graph f d n e g) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SequencePrependSyntax.graph f d n e h) := .hyp (Or.inl rfl)
  exact SequencePrependGraph.unique_graph hZ f d n e g h h0 h1

theorem packetReaderRecursionPrependGraphUnique_kernel_certificate {m} (f d n e g h : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderRecursionPrependGraphUniqueSentence f d n e g h)) := TheoryTransport.sentence (source_packetReaderRecursionPrependGraphUnique f d n e g h)

theorem native_packetReaderRecursionPrependGraphUnique {m} (f d n e g h : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderRecursionPrependGraphUniqueSentence f d n e g h)) := ZFReplay.replay (packetReaderRecursionPrependGraphUnique_kernel_certificate f d n e g h)

def packetReaderRecursionPrependActualZeroEdgeSentence {m} (w f d n e g z : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem d w).imp ((successor e d).imp ((SequencePrependSyntax.graph f d n e g).imp ((empty z).imp ((GraphSyntax.edge g z n))))))).close

theorem source_packetReaderRecursionPrependActualZeroEdge {m} (w f d n e g z : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderRecursionPrependActualZeroEdgeSentence w f d n e g z) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (empty z) (Context.add (SequencePrependSyntax.graph f d n e g) (Context.add (successor e d) (Context.add (Formula.mem d w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (Formula.mem d w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (successor e d) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (SequencePrependSyntax.graph f d n e g) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (empty z) := .hyp (Or.inl rfl)
  exact SequencePrependEdges.zero_edge hZ w f d n e g z h0 h1 h2 h3 h4

theorem packetReaderRecursionPrependActualZeroEdge_kernel_certificate {m} (w f d n e g z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderRecursionPrependActualZeroEdgeSentence w f d n e g z)) := TheoryTransport.sentence (source_packetReaderRecursionPrependActualZeroEdge w f d n e g z)

theorem native_packetReaderRecursionPrependActualZeroEdge {m} (w f d n e g z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderRecursionPrependActualZeroEdgeSentence w f d n e g z)) := ZFReplay.replay (packetReaderRecursionPrependActualZeroEdge_kernel_certificate w f d n e g z)

def packetReaderRecursionPrependEveryActualSuccessorEdgeExactSentence {m} (w f d n e g i j y : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem d w).imp ((successor e d).imp ((SequencePrependSyntax.graph f d n e g).imp ((Formula.mem j d).imp ((successor i j).imp (((GraphSyntax.edge g i y).iff (GraphSyntax.edge f j y))))))))).close

theorem source_packetReaderRecursionPrependEveryActualSuccessorEdgeExact {m} (w f d n e g i j y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderRecursionPrependEveryActualSuccessorEdgeExactSentence w f d n e g i j y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor i j) (Context.add (Formula.mem j d) (Context.add (SequencePrependSyntax.graph f d n e g) (Context.add (successor e d) (Context.add (Formula.mem d w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (Formula.mem d w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (successor e d) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (SequencePrependSyntax.graph f d n e g) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (Formula.mem j d) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (successor i j) := .hyp (Or.inl rfl)
  exact SequencePrependEdges.successor_iff hZ w f d n e g i j y h0 h1 h2 h3 h4 h5

theorem packetReaderRecursionPrependEveryActualSuccessorEdgeExact_kernel_certificate {m} (w f d n e g i j y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderRecursionPrependEveryActualSuccessorEdgeExactSentence w f d n e g i j y)) := TheoryTransport.sentence (source_packetReaderRecursionPrependEveryActualSuccessorEdgeExact w f d n e g i j y)

theorem native_packetReaderRecursionPrependEveryActualSuccessorEdgeExact {m} (w f d n e g i j y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderRecursionPrependEveryActualSuccessorEdgeExactSentence w f d n e g i j y)) := ZFReplay.replay (packetReaderRecursionPrependEveryActualSuccessorEdgeExact_kernel_certificate w f d n e g i j y)

def packetReaderRecursionEveryActualHistoryRowShiftsSentence {m} (w B z o f d n e g i j : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem d w).imp ((successor e d).imp ((SequenceSyntax.sequence f d w).imp ((SequencePrependSyntax.graph f d n e g).imp ((successor i j).imp ((PacketReaderHistorySyntax.row w B z o f j).imp ((PacketReaderHistorySyntax.row w B z o g i))))))))).close

theorem source_packetReaderRecursionEveryActualHistoryRowShifts {m} (w B z o f d n e g i j : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderRecursionEveryActualHistoryRowShiftsSentence w B z o f d n e g i j) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderHistorySyntax.row w B z o f j) (Context.add (successor i j) (Context.add (SequencePrependSyntax.graph f d n e g) (Context.add (SequenceSyntax.sequence f d w) (Context.add (successor e d) (Context.add (Formula.mem d w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))
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
  have h1 : Derives Δ (Formula.mem d w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h2 : Derives Δ (successor e d) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h3 : Derives Δ (SequenceSyntax.sequence f d w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : Derives Δ (SequencePrependSyntax.graph f d n e g) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h5 : Derives Δ (successor i j) := .hyp (Or.inr (Or.inl rfl))
  have h6 : Derives Δ (PacketReaderHistorySyntax.row w B z o f j) := .hyp (Or.inl rfl)
  exact PacketReaderHistoryPrependRows.successor_row hZ w B z o f d n e g i j h0 h1 h2 h3 h4 h5 h6

theorem packetReaderRecursionEveryActualHistoryRowShifts_kernel_certificate {m} (w B z o f d n e g i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderRecursionEveryActualHistoryRowShiftsSentence w B z o f d n e g i j)) := TheoryTransport.sentence (source_packetReaderRecursionEveryActualHistoryRowShifts w B z o f d n e g i j)

theorem native_packetReaderRecursionEveryActualHistoryRowShifts {m} (w B z o f d n e g i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderRecursionEveryActualHistoryRowShiftsSentence w B z o f d n e g i j)) := ZFReplay.replay (packetReaderRecursionEveryActualHistoryRowShifts_kernel_certificate w B z o f d n e g i j)

def packetReaderRecursionActualInitialStepConstructsZeroRowSentence {m} (w B z o n r t l d e f g : Fin m) : Source.Sentence := ((omega w).imp ((PacketReaderHistorySyntax.history w B z o r t l d f).imp ((successor e d).imp ((SequencePrependSyntax.graph f d n e g).imp ((PacketReaderCodedSyntax.step w B z o n r).imp ((PacketReaderHistorySyntax.row w B z o g z))))))).close

theorem source_packetReaderRecursionActualInitialStepConstructsZeroRow {m} (w B z o n r t l d e f g : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderRecursionActualInitialStepConstructsZeroRowSentence w B z o n r t l d e f g) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderCodedSyntax.step w B z o n r) (Context.add (SequencePrependSyntax.graph f d n e g) (Context.add (successor e d) (Context.add (PacketReaderHistorySyntax.history w B z o r t l d f) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (PacketReaderHistorySyntax.history w B z o r t l d f) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (successor e d) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (SequencePrependSyntax.graph f d n e g) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (PacketReaderCodedSyntax.step w B z o n r) := .hyp (Or.inl rfl)
  exact PacketReaderHistoryPrependRows.zero_row hZ w B z o n r t l d e f g h0 h1 h2 h3 h4

theorem packetReaderRecursionActualInitialStepConstructsZeroRow_kernel_certificate {m} (w B z o n r t l d e f g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderRecursionActualInitialStepConstructsZeroRowSentence w B z o n r t l d e f g)) := TheoryTransport.sentence (source_packetReaderRecursionActualInitialStepConstructsZeroRow w B z o n r t l d e f g)

theorem native_packetReaderRecursionActualInitialStepConstructsZeroRow {m} (w B z o n r t l d e f g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderRecursionActualInitialStepConstructsZeroRowSentence w B z o n r t l d e f g)) := ZFReplay.replay (packetReaderRecursionActualInitialStepConstructsZeroRow_kernel_certificate w B z o n r t l d e f g)

def packetReaderRecursionExactPrependGraphConstructsRealWholeHistorySentence {m} (w B z o n r t l d e f g : Fin m) : Source.Sentence := ((omega w).imp ((PacketReaderHistorySyntax.history w B z o r t l d f).imp ((PacketReaderCodedSyntax.step w B z o n r).imp ((successor e d).imp ((SequencePrependSyntax.graph f d n e g).imp ((PacketReaderHistorySyntax.history w B z o n t d e g))))))).close

theorem source_packetReaderRecursionExactPrependGraphConstructsRealWholeHistory {m} (w B z o n r t l d e f g : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderRecursionExactPrependGraphConstructsRealWholeHistorySentence w B z o n r t l d e f g) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SequencePrependSyntax.graph f d n e g) (Context.add (successor e d) (Context.add (PacketReaderCodedSyntax.step w B z o n r) (Context.add (PacketReaderHistorySyntax.history w B z o r t l d f) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (PacketReaderHistorySyntax.history w B z o r t l d f) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (PacketReaderCodedSyntax.step w B z o n r) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (successor e d) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (SequencePrependSyntax.graph f d n e g) := .hyp (Or.inl rfl)
  exact PacketReaderHistoryPrepend.from_graph hZ w B z o n r t l d e f g h0 h1 h2 h3 h4

theorem packetReaderRecursionExactPrependGraphConstructsRealWholeHistory_kernel_certificate {m} (w B z o n r t l d e f g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderRecursionExactPrependGraphConstructsRealWholeHistorySentence w B z o n r t l d e f g)) := TheoryTransport.sentence (source_packetReaderRecursionExactPrependGraphConstructsRealWholeHistory w B z o n r t l d e f g)

theorem native_packetReaderRecursionExactPrependGraphConstructsRealWholeHistory {m} (w B z o n r t l d e f g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderRecursionExactPrependGraphConstructsRealWholeHistorySentence w B z o n r t l d e f g)) := ZFReplay.replay (packetReaderRecursionExactPrependGraphConstructsRealWholeHistory_kernel_certificate w B z o n r t l d e f g)

def packetReaderRecursionRealWholeHistoryPrependExistsSentence {m} (w B z o n r t l d e f : Fin m) : Source.Sentence := ((omega w).imp ((PacketReaderHistorySyntax.history w B z o r t l d f).imp ((PacketReaderCodedSyntax.step w B z o n r).imp ((successor e d).imp ((PacketReaderHistoryPrepend.extension w B z o n t d e f)))))).close

theorem source_packetReaderRecursionRealWholeHistoryPrependExists {m} (w B z o n r t l d e f : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderRecursionRealWholeHistoryPrependExistsSentence w B z o n r t l d e f) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor e d) (Context.add (PacketReaderCodedSyntax.step w B z o n r) (Context.add (PacketReaderHistorySyntax.history w B z o r t l d f) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (PacketReaderHistorySyntax.history w B z o r t l d f) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (PacketReaderCodedSyntax.step w B z o n r) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (successor e d) := .hyp (Or.inl rfl)
  exact PacketReaderHistoryPrepend.exists_extension hZ w B z o n r t l d e f h0 h1 h2 h3

theorem packetReaderRecursionRealWholeHistoryPrependExists_kernel_certificate {m} (w B z o n r t l d e f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderRecursionRealWholeHistoryPrependExistsSentence w B z o n r t l d e f)) := TheoryTransport.sentence (source_packetReaderRecursionRealWholeHistoryPrependExists w B z o n r t l d e f)

theorem native_packetReaderRecursionRealWholeHistoryPrependExists {m} (w B z o n r t l d e f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderRecursionRealWholeHistoryPrependExistsSentence w B z o n r t l d e f)) := ZFReplay.replay (packetReaderRecursionRealWholeHistoryPrependExists_kernel_certificate w B z o n r t l d e f)

def packetReaderRecursionStepAndReturningHistoryConstructWholeRunSentence {m} (w B z o n r t l d f q : Fin m) : Source.Sentence := ((omega w).imp ((PacketReaderCodedSyntax.step w B z o n r).imp ((PacketReaderHistorySyntax.history w B z o r t l d f).imp ((PacketReaderReturnCodedSyntax.coded w B z o t q).imp ((PacketReaderReturnCodedSyntax.run w B z o n q)))))).close

theorem source_packetReaderRecursionStepAndReturningHistoryConstructWholeRun {m} (w B z o n r t l d f q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderRecursionStepAndReturningHistoryConstructWholeRunSentence w B z o n r t l d f q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderReturnCodedSyntax.coded w B z o t q) (Context.add (PacketReaderHistorySyntax.history w B z o r t l d f) (Context.add (PacketReaderCodedSyntax.step w B z o n r) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (PacketReaderCodedSyntax.step w B z o n r) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (PacketReaderHistorySyntax.history w B z o r t l d f) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (PacketReaderReturnCodedSyntax.coded w B z o t q) := .hyp (Or.inl rfl)
  exact PacketReaderRunPrepend.from_history hZ w B z o n r t l d f q h0 h1 h2 h3

theorem packetReaderRecursionStepAndReturningHistoryConstructWholeRun_kernel_certificate {m} (w B z o n r t l d f q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderRecursionStepAndReturningHistoryConstructWholeRunSentence w B z o n r t l d f q)) := TheoryTransport.sentence (source_packetReaderRecursionStepAndReturningHistoryConstructWholeRun w B z o n r t l d f q)

theorem native_packetReaderRecursionStepAndReturningHistoryConstructWholeRun {m} (w B z o n r t l d f q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderRecursionStepAndReturningHistoryConstructWholeRunSentence w B z o n r t l d f q)) := ZFReplay.replay (packetReaderRecursionStepAndReturningHistoryConstructWholeRun_kernel_certificate w B z o n r t l d f q)

def packetReaderRecursionActualStepPropagatesReturningRunBackwardSentence {m} (w B z o n r q : Fin m) : Source.Sentence := ((omega w).imp ((PacketReaderCodedSyntax.step w B z o n r).imp ((PacketReaderReturnCodedSyntax.run w B z o r q).imp ((PacketReaderReturnCodedSyntax.run w B z o n q))))).close

theorem source_packetReaderRecursionActualStepPropagatesReturningRunBackward {m} (w B z o n r q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderRecursionActualStepPropagatesReturningRunBackwardSentence w B z o n r q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderReturnCodedSyntax.run w B z o r q) (Context.add (PacketReaderCodedSyntax.step w B z o n r) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (PacketReaderCodedSyntax.step w B z o n r) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (PacketReaderReturnCodedSyntax.run w B z o r q) := .hyp (Or.inl rfl)
  exact PacketReaderRunPrepend.backward hZ w B z o n r q h0 h1 h2

theorem packetReaderRecursionActualStepPropagatesReturningRunBackward_kernel_certificate {m} (w B z o n r q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderRecursionActualStepPropagatesReturningRunBackwardSentence w B z o n r q)) := TheoryTransport.sentence (source_packetReaderRecursionActualStepPropagatesReturningRunBackward w B z o n r q)

theorem native_packetReaderRecursionActualStepPropagatesReturningRunBackward {m} (w B z o n r q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderRecursionActualStepPropagatesReturningRunBackwardSentence w B z o n r q)) := ZFReplay.replay (packetReaderRecursionActualStepPropagatesReturningRunBackward_kernel_certificate w B z o n r q)

def packetReaderRecursionActualStepPropagatesReturningRunForwardSentence {m} (w B z o n r q : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem B w).imp ((empty z).imp ((Formula.mem o w).imp ((PacketReaderCodedSyntax.step w B z o n r).imp ((PacketReaderReturnCodedSyntax.run w B z o n q).imp ((PacketReaderReturnCodedSyntax.run w B z o r q)))))))).close

theorem source_packetReaderRecursionActualStepPropagatesReturningRunForward {m} (w B z o n r q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderRecursionActualStepPropagatesReturningRunForwardSentence w B z o n r q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderReturnCodedSyntax.run w B z o n q) (Context.add (PacketReaderCodedSyntax.step w B z o n r) (Context.add (Formula.mem o w) (Context.add (empty z) (Context.add (Formula.mem B w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
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
  have h2 : Derives Δ (empty z) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (Formula.mem o w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (PacketReaderCodedSyntax.step w B z o n r) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (PacketReaderReturnCodedSyntax.run w B z o n q) := .hyp (Or.inl rfl)
  exact PacketReaderRunStep.forward hZ w B z o n r q h0 h1 h2 h3 h4 h5

theorem packetReaderRecursionActualStepPropagatesReturningRunForward_kernel_certificate {m} (w B z o n r q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderRecursionActualStepPropagatesReturningRunForwardSentence w B z o n r q)) := TheoryTransport.sentence (source_packetReaderRecursionActualStepPropagatesReturningRunForward w B z o n r q)

theorem native_packetReaderRecursionActualStepPropagatesReturningRunForward {m} (w B z o n r q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderRecursionActualStepPropagatesReturningRunForwardSentence w B z o n r q)) := ZFReplay.replay (packetReaderRecursionActualStepPropagatesReturningRunForward_kernel_certificate w B z o n r q)

def packetReaderRecursionActualStepWholeRunExactEquationSentence {m} (w B z o n r q : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem B w).imp ((empty z).imp ((Formula.mem o w).imp ((PacketReaderCodedSyntax.step w B z o n r).imp (((PacketReaderReturnCodedSyntax.run w B z o n q).iff (PacketReaderReturnCodedSyntax.run w B z o r q)))))))).close

theorem source_packetReaderRecursionActualStepWholeRunExactEquation {m} (w B z o n r q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderRecursionActualStepWholeRunExactEquationSentence w B z o n r q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderCodedSyntax.step w B z o n r) (Context.add (Formula.mem o w) (Context.add (empty z) (Context.add (Formula.mem B w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
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
  have h4 : Derives Δ (PacketReaderCodedSyntax.step w B z o n r) := .hyp (Or.inl rfl)
  exact PacketReaderRunStep.step_iff hZ w B z o n r q h0 h1 h2 h3 h4

theorem packetReaderRecursionActualStepWholeRunExactEquation_kernel_certificate {m} (w B z o n r q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderRecursionActualStepWholeRunExactEquationSentence w B z o n r q)) := TheoryTransport.sentence (source_packetReaderRecursionActualStepWholeRunExactEquation w B z o n r q)

theorem native_packetReaderRecursionActualStepWholeRunExactEquation {m} (w B z o n r q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderRecursionActualStepWholeRunExactEquationSentence w B z o n r q)) := ZFReplay.replay (packetReaderRecursionActualStepWholeRunExactEquation_kernel_certificate w B z o n r q)

def packetReaderRecursionFourFieldEvaluationNormalizesAtActualCodeSentence {m} (w B z o L v s a q n : Fin m) : Source.Sentence := ((omega w).imp ((PacketReaderStateSyntax.code w L v s a n).imp (((PacketReaderEvalSyntax.eval w B z o L v s a q).iff (PacketReaderReturnCodedSyntax.run w B z o n q))))).close

theorem source_packetReaderRecursionFourFieldEvaluationNormalizesAtActualCode {m} (w B z o L v s a q n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderRecursionFourFieldEvaluationNormalizesAtActualCodeSentence w B z o L v s a q n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderStateSyntax.code w L v s a n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PacketReaderStateSyntax.code w L v s a n) := .hyp (Or.inl rfl)
  exact PacketReaderEval.at_code hZ w B z o L v s a q n h0 h1

theorem packetReaderRecursionFourFieldEvaluationNormalizesAtActualCode_kernel_certificate {m} (w B z o L v s a q n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderRecursionFourFieldEvaluationNormalizesAtActualCodeSentence w B z o L v s a q n)) := TheoryTransport.sentence (source_packetReaderRecursionFourFieldEvaluationNormalizesAtActualCode w B z o L v s a q n)

theorem native_packetReaderRecursionFourFieldEvaluationNormalizesAtActualCode {m} (w B z o L v s a q n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderRecursionFourFieldEvaluationNormalizesAtActualCodeSentence w B z o L v s a q n)) := ZFReplay.replay (packetReaderRecursionFourFieldEvaluationNormalizesAtActualCode_kernel_certificate w B z o L v s a q n)

def packetReaderRecursionFourFieldEvaluationOriginalAdvanceEquationSentence {m} (w B z o L v s a X y S c q : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem B w).imp ((empty z).imp ((Formula.mem o w).imp ((PacketReaderInputSyntax.advance w B z o L v s a X y S c).imp (((PacketReaderEvalSyntax.eval w B z o L v s a q).iff (PacketReaderEvalSyntax.eval w B z o X y S c q)))))))).close

theorem source_packetReaderRecursionFourFieldEvaluationOriginalAdvanceEquation {m} (w B z o L v s a X y S c q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderRecursionFourFieldEvaluationOriginalAdvanceEquationSentence w B z o L v s a X y S c q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderInputSyntax.advance w B z o L v s a X y S c) (Context.add (Formula.mem o w) (Context.add (empty z) (Context.add (Formula.mem B w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
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
  have h4 : Derives Δ (PacketReaderInputSyntax.advance w B z o L v s a X y S c) := .hyp (Or.inl rfl)
  exact PacketReaderEval.step_iff hZ w B z o L v s a X y S c q h0 h1 h2 h3 h4

theorem packetReaderRecursionFourFieldEvaluationOriginalAdvanceEquation_kernel_certificate {m} (w B z o L v s a X y S c q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderRecursionFourFieldEvaluationOriginalAdvanceEquationSentence w B z o L v s a X y S c q)) := TheoryTransport.sentence (source_packetReaderRecursionFourFieldEvaluationOriginalAdvanceEquation w B z o L v s a X y S c q)

theorem native_packetReaderRecursionFourFieldEvaluationOriginalAdvanceEquation {m} (w B z o L v s a X y S c q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderRecursionFourFieldEvaluationOriginalAdvanceEquationSentence w B z o L v s a X y S c q)) := ZFReplay.replay (packetReaderRecursionFourFieldEvaluationOriginalAdvanceEquation_kernel_certificate w B z o L v s a X y S c q)

def packetReaderRecursionFourFieldEvaluationOriginalTerminalEquationSentence {m} (w B z o L v s a q : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem B w).imp ((empty z).imp ((successor o z).imp ((PacketReaderTerminalSyntax.raw w B z o L v s a).imp (((PacketReaderEvalSyntax.eval w B z o L v s a q).iff (PacketReaderReturnSyntax.result w B z o L v s a q)))))))).close

theorem source_packetReaderRecursionFourFieldEvaluationOriginalTerminalEquation {m} (w B z o L v s a q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderRecursionFourFieldEvaluationOriginalTerminalEquationSentence w B z o L v s a q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderTerminalSyntax.raw w B z o L v s a) (Context.add (successor o z) (Context.add (empty z) (Context.add (Formula.mem B w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
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
  have h3 : Derives Δ (successor o z) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (PacketReaderTerminalSyntax.raw w B z o L v s a) := .hyp (Or.inl rfl)
  exact PacketReaderEval.at_terminal hZ w B z o L v s a q h0 h1 h2 h3 h4

theorem packetReaderRecursionFourFieldEvaluationOriginalTerminalEquation_kernel_certificate {m} (w B z o L v s a q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderRecursionFourFieldEvaluationOriginalTerminalEquationSentence w B z o L v s a q)) := TheoryTransport.sentence (source_packetReaderRecursionFourFieldEvaluationOriginalTerminalEquation w B z o L v s a q)

theorem native_packetReaderRecursionFourFieldEvaluationOriginalTerminalEquation {m} (w B z o L v s a q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderRecursionFourFieldEvaluationOriginalTerminalEquationSentence w B z o L v s a q)) := ZFReplay.replay (packetReaderRecursionFourFieldEvaluationOriginalTerminalEquation_kernel_certificate w B z o L v s a q)

end PPAC.Migration.Internal.ObjectPacketReaderRecursion
