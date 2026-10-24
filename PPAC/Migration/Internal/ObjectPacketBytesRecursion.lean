import PPAC.Migration.Internal.PacketBytesRecursionLaws

/-! Exact independent ordered byte-fold recursion on all internal candidates; both prefix graphs and radix witnesses eliminated; global totality uniqueness and canonical-byte bridge remain unproved; full Basic AST and varint bridge remain unproved in the original nativeZF kernel; complete schema tests and Con remain unproved. -/
namespace PPAC.Migration.Internal.ObjectPacketBytesRecursion
open Source SourceAlgebra SourceLogic OmegaSyntax

def packetBytesRecursionBothSequenceRowRestrictionSentence {m} (w C p l f g F G i : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem p w).imp ((successor l p).imp ((RestrictionSyntax.restrict F f l).imp ((RestrictionSyntax.restrict G g l).imp ((Formula.mem i p).imp ((PacketBytesRowSyntax.row w C f g i).imp ((PacketBytesRowSyntax.row w C F G i))))))))).close

theorem source_packetBytesRecursionBothSequenceRowRestriction {m} (w C p l f g F G i : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetBytesRecursionBothSequenceRowRestrictionSentence w C p l f g F G i) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketBytesRowSyntax.row w C f g i) (Context.add (Formula.mem i p) (Context.add (RestrictionSyntax.restrict G g l) (Context.add (RestrictionSyntax.restrict F f l) (Context.add (successor l p) (Context.add (Formula.mem p w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))
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
  have h1 : Derives Δ (Formula.mem p w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h2 : Derives Δ (successor l p) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h3 : Derives Δ (RestrictionSyntax.restrict F f l) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : Derives Δ (RestrictionSyntax.restrict G g l) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h5 : Derives Δ (Formula.mem i p) := .hyp (Or.inr (Or.inl rfl))
  have h6 : Derives Δ (PacketBytesRowSyntax.row w C f g i) := .hyp (Or.inl rfl)
  exact PacketBytesRowRestrict.row_restrict hZ w C p l f g F G i h0 h1 h2 h3 h4 h5 h6

theorem packetBytesRecursionBothSequenceRowRestriction_kernel_certificate {m} (w C p l f g F G i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetBytesRecursionBothSequenceRowRestrictionSentence w C p l f g F G i)) := TheoryTransport.sentence (source_packetBytesRecursionBothSequenceRowRestriction w C p l f g F G i)

theorem native_packetBytesRecursionBothSequenceRowRestriction {m} (w C p l f g F G i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetBytesRecursionBothSequenceRowRestrictionSentence w C p l f g F G i)) := ZFReplay.replay (packetBytesRecursionBothSequenceRowRestriction_kernel_certificate w C p l f g F G i)

def packetBytesRecursionAllOldRowsRestrictionSentence {m} (w C p l f g F G : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem p w).imp ((successor l p).imp ((PacketBytesRowSyntax.links w C l f g).imp ((RestrictionSyntax.restrict F f l).imp ((RestrictionSyntax.restrict G g l).imp ((PacketBytesRowSyntax.links w C p F G)))))))).close

theorem source_packetBytesRecursionAllOldRowsRestriction {m} (w C p l f g F G : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetBytesRecursionAllOldRowsRestrictionSentence w C p l f g F G) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (RestrictionSyntax.restrict G g l) (Context.add (RestrictionSyntax.restrict F f l) (Context.add (PacketBytesRowSyntax.links w C l f g) (Context.add (successor l p) (Context.add (Formula.mem p w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (Formula.mem p w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (successor l p) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (PacketBytesRowSyntax.links w C l f g) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (RestrictionSyntax.restrict F f l) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (RestrictionSyntax.restrict G g l) := .hyp (Or.inl rfl)
  exact PacketBytesRowRestrict.links_restrict hZ w C p l f g F G h0 h1 h2 h3 h4 h5

theorem packetBytesRecursionAllOldRowsRestriction_kernel_certificate {m} (w C p l f g F G : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetBytesRecursionAllOldRowsRestrictionSentence w C p l f g F G)) := TheoryTransport.sentence (source_packetBytesRecursionAllOldRowsRestriction w C p l f g F G)

theorem native_packetBytesRecursionAllOldRowsRestriction {m} (w C p l f g F G : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetBytesRecursionAllOldRowsRestrictionSentence w C p l f g F G)) := ZFReplay.replay (packetBytesRecursionAllOldRowsRestriction_kernel_certificate w C p l f g F G)

def packetBytesRecursionFullDualPrefixFromActualRestrictionsSentence {m} (w C n t a z e l d f g p x u F G : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem p w).imp ((successor l p).imp ((PacketBytesTraceSyntax.trace w C n t a z e l d f g).imp ((GraphSyntax.edge f p x).imp ((GraphSyntax.edge g p u).imp ((SequencePrefix.witness F f l w).imp ((SequencePrefix.witness G g l w).imp ((PacketBytesTraceSyntax.trace w C x t u z e p l F G)))))))))).close

theorem source_packetBytesRecursionFullDualPrefixFromActualRestrictions {m} (w C n t a z e l d f g p x u F G : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetBytesRecursionFullDualPrefixFromActualRestrictionsSentence w C n t a z e l d f g p x u F G) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SequencePrefix.witness G g l w) (Context.add (SequencePrefix.witness F f l w) (Context.add (GraphSyntax.edge g p u) (Context.add (GraphSyntax.edge f p x) (Context.add (PacketBytesTraceSyntax.trace w C n t a z e l d f g) (Context.add (successor l p) (Context.add (Formula.mem p w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  have h1 : Derives Δ (Formula.mem p w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h2 : Derives Δ (successor l p) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h3 : Derives Δ (PacketBytesTraceSyntax.trace w C n t a z e l d f g) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h4 : Derives Δ (GraphSyntax.edge f p x) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h5 : Derives Δ (GraphSyntax.edge g p u) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h6 : Derives Δ (SequencePrefix.witness F f l w) := .hyp (Or.inr (Or.inl rfl))
  have h7 : Derives Δ (SequencePrefix.witness G g l w) := .hyp (Or.inl rfl)
  exact PacketBytesTracePrefix.from_prefixes hZ w C n t a z e l d f g p x u F G h0 h1 h2 h3 h4 h5 h6 h7

theorem packetBytesRecursionFullDualPrefixFromActualRestrictions_kernel_certificate {m} (w C n t a z e l d f g p x u F G : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetBytesRecursionFullDualPrefixFromActualRestrictionsSentence w C n t a z e l d f g p x u F G)) := TheoryTransport.sentence (source_packetBytesRecursionFullDualPrefixFromActualRestrictions w C n t a z e l d f g p x u F G)

theorem native_packetBytesRecursionFullDualPrefixFromActualRestrictions {m} (w C n t a z e l d f g p x u F G : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetBytesRecursionFullDualPrefixFromActualRestrictionsSentence w C n t a z e l d f g p x u F G)) := ZFReplay.replay (packetBytesRecursionFullDualPrefixFromActualRestrictions_kernel_certificate w C n t a z e l d f g p x u F G)

def packetBytesRecursionDualPrefixGraphsObjectEliminatedSentence {m} (w C n t a z e l d f g p x u : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem p w).imp ((successor l p).imp ((PacketBytesTraceSyntax.trace w C n t a z e l d f g).imp ((GraphSyntax.edge f p x).imp ((GraphSyntax.edge g p u).imp ((PacketBytesTraceSyntax.foldAt w C x t u)))))))).close

theorem source_packetBytesRecursionDualPrefixGraphsObjectEliminated {m} (w C n t a z e l d f g p x u : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetBytesRecursionDualPrefixGraphsObjectEliminatedSentence w C n t a z e l d f g p x u) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (GraphSyntax.edge g p u) (Context.add (GraphSyntax.edge f p x) (Context.add (PacketBytesTraceSyntax.trace w C n t a z e l d f g) (Context.add (successor l p) (Context.add (Formula.mem p w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (Formula.mem p w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (successor l p) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (PacketBytesTraceSyntax.trace w C n t a z e l d f g) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (GraphSyntax.edge f p x) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (GraphSyntax.edge g p u) := .hyp (Or.inl rfl)
  exact PacketBytesTracePrefix.exists_prefix hZ w C n t a z e l d f g p x u h0 h1 h2 h3 h4 h5

theorem packetBytesRecursionDualPrefixGraphsObjectEliminated_kernel_certificate {m} (w C n t a z e l d f g p x u : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetBytesRecursionDualPrefixGraphsObjectEliminatedSentence w C n t a z e l d f g p x u)) := TheoryTransport.sentence (source_packetBytesRecursionDualPrefixGraphsObjectEliminated w C n t a z e l d f g p x u)

theorem native_packetBytesRecursionDualPrefixGraphsObjectEliminated {m} (w C n t a z e l d f g p x u : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetBytesRecursionDualPrefixGraphsObjectEliminatedSentence w C n t a z e l d f g p x u)) := ZFReplay.replay (packetBytesRecursionDualPrefixGraphsObjectEliminated_kernel_certificate w C n t a z e l d f g p x u)

def packetBytesRecursionCompleteTerminalRowNormalizedSentence {m} (w C n t a z e l d f g p : Fin m) : Source.Sentence := ((successor l p).imp ((PacketBytesTraceSyntax.trace w C n t a z e l d f g).imp ((PacketBytesRowSyntax.row w C f g p).imp ((PacketBytesRecursionSyntax.terminal w C f g p n a))))).close

theorem source_packetBytesRecursionCompleteTerminalRowNormalized {m} (w C n t a z e l d f g p : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetBytesRecursionCompleteTerminalRowNormalizedSentence w C n t a z e l d f g p) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketBytesRowSyntax.row w C f g p) (Context.add (PacketBytesTraceSyntax.trace w C n t a z e l d f g) (Context.add (successor l p) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (successor l p) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (PacketBytesTraceSyntax.trace w C n t a z e l d f g) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (PacketBytesRowSyntax.row w C f g p) := .hyp (Or.inl rfl)
  exact PacketBytesTerminal.of_row hZ w C n t a z e l d f g p h0 h1 h2

theorem packetBytesRecursionCompleteTerminalRowNormalized_kernel_certificate {m} (w C n t a z e l d f g p : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetBytesRecursionCompleteTerminalRowNormalizedSentence w C n t a z e l d f g p)) := TheoryTransport.sentence (source_packetBytesRecursionCompleteTerminalRowNormalized w C n t a z e l d f g p)

theorem native_packetBytesRecursionCompleteTerminalRowNormalized {m} (w C n t a z e l d f g p : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetBytesRecursionCompleteTerminalRowNormalizedSentence w C n t a z e l d f g p)) := ZFReplay.replay (packetBytesRecursionCompleteTerminalRowNormalized_kernel_certificate w C n t a z e l d f g p)

def packetBytesRecursionTerminalWitnessesFromFullTraceSentence {m} (w C n t a z e l d f g p : Fin m) : Source.Sentence := ((successor l p).imp ((PacketBytesTraceSyntax.trace w C n t a z e l d f g).imp ((PacketBytesRecursionSyntax.terminal w C f g p n a)))).close

theorem source_packetBytesRecursionTerminalWitnessesFromFullTrace {m} (w C n t a z e l d f g p : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetBytesRecursionTerminalWitnessesFromFullTraceSentence w C n t a z e l d f g p) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketBytesTraceSyntax.trace w C n t a z e l d f g) (Context.add (successor l p) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (successor l p) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PacketBytesTraceSyntax.trace w C n t a z e l d f g) := .hyp (Or.inl rfl)
  exact PacketBytesTerminal.terminal_row hZ w C n t a z e l d f g p h0 h1

theorem packetBytesRecursionTerminalWitnessesFromFullTrace_kernel_certificate {m} (w C n t a z e l d f g p : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetBytesRecursionTerminalWitnessesFromFullTraceSentence w C n t a z e l d f g p)) := TheoryTransport.sentence (source_packetBytesRecursionTerminalWitnessesFromFullTrace w C n t a z e l d f g p)

theorem native_packetBytesRecursionTerminalWitnessesFromFullTrace {m} (w C n t a z e l d f g p : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetBytesRecursionTerminalWitnessesFromFullTraceSentence w C n t a z e l d f g p)) := ZFReplay.replay (packetBytesRecursionTerminalWitnessesFromFullTrace_kernel_certificate w C n t a z e l d f g p)

def packetBytesRecursionSuccessorFullReverseDecompositionSentence {m} (w C n t a z e l d f g p : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem p w).imp ((successor l p).imp ((PacketBytesTraceSyntax.trace w C n t a z e l d f g).imp ((PacketBytesRecursionSyntax.consCase w C n t a)))))).close

theorem source_packetBytesRecursionSuccessorFullReverseDecomposition {m} (w C n t a z e l d f g p : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetBytesRecursionSuccessorFullReverseDecompositionSentence w C n t a z e l d f g p) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketBytesTraceSyntax.trace w C n t a z e l d f g) (Context.add (successor l p) (Context.add (Formula.mem p w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (Formula.mem p w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (successor l p) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (PacketBytesTraceSyntax.trace w C n t a z e l d f g) := .hyp (Or.inl rfl)
  exact PacketBytesDecomposition.successor_case hZ w C n t a z e l d f g p h0 h1 h2 h3

theorem packetBytesRecursionSuccessorFullReverseDecomposition_kernel_certificate {m} (w C n t a z e l d f g p : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetBytesRecursionSuccessorFullReverseDecompositionSentence w C n t a z e l d f g p)) := TheoryTransport.sentence (source_packetBytesRecursionSuccessorFullReverseDecomposition w C n t a z e l d f g p)

theorem native_packetBytesRecursionSuccessorFullReverseDecomposition {m} (w C n t a z e l d f g p : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetBytesRecursionSuccessorFullReverseDecompositionSentence w C n t a z e l d f g p)) := ZFReplay.replay (packetBytesRecursionSuccessorFullReverseDecomposition_kernel_certificate w C n t a z e l d f g p)

def packetBytesRecursionAllInternalTraceReverseDecompositionSentence {m} (w C n t a z e l d f g : Fin m) : Source.Sentence := ((omega w).imp ((PacketBytesTraceSyntax.trace w C n t a z e l d f g).imp ((PacketBytesRecursionSyntax.caseAt w C n t a)))).close

theorem source_packetBytesRecursionAllInternalTraceReverseDecomposition {m} (w C n t a z e l d f g : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetBytesRecursionAllInternalTraceReverseDecompositionSentence w C n t a z e l d f g) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketBytesTraceSyntax.trace w C n t a z e l d f g) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PacketBytesTraceSyntax.trace w C n t a z e l d f g) := .hyp (Or.inl rfl)
  exact PacketBytesDecomposition.trace_forward hZ w C n t a z e l d f g h0 h1

theorem packetBytesRecursionAllInternalTraceReverseDecomposition_kernel_certificate {m} (w C n t a z e l d f g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetBytesRecursionAllInternalTraceReverseDecompositionSentence w C n t a z e l d f g)) := TheoryTransport.sentence (source_packetBytesRecursionAllInternalTraceReverseDecomposition w C n t a z e l d f g)

theorem native_packetBytesRecursionAllInternalTraceReverseDecomposition {m} (w C n t a z e l d f g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetBytesRecursionAllInternalTraceReverseDecompositionSentence w C n t a z e l d f g)) := ZFReplay.replay (packetBytesRecursionAllInternalTraceReverseDecomposition_kernel_certificate w C n t a z e l d f g)

def packetBytesRecursionAllInternalFoldReverseDecompositionSentence {m} (w C n t a : Fin m) : Source.Sentence := ((omega w).imp ((PacketBytesTraceSyntax.foldAt w C n t a).imp ((PacketBytesRecursionSyntax.caseAt w C n t a)))).close

theorem source_packetBytesRecursionAllInternalFoldReverseDecomposition {m} (w C n t a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetBytesRecursionAllInternalFoldReverseDecompositionSentence w C n t a) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketBytesTraceSyntax.foldAt w C n t a) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PacketBytesTraceSyntax.foldAt w C n t a) := .hyp (Or.inl rfl)
  exact PacketBytesDecomposition.fold_forward hZ w C n t a h0 h1

theorem packetBytesRecursionAllInternalFoldReverseDecomposition_kernel_certificate {m} (w C n t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetBytesRecursionAllInternalFoldReverseDecompositionSentence w C n t a)) := TheoryTransport.sentence (source_packetBytesRecursionAllInternalFoldReverseDecomposition w C n t a)

theorem native_packetBytesRecursionAllInternalFoldReverseDecomposition {m} (w C n t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetBytesRecursionAllInternalFoldReverseDecompositionSentence w C n t a)) := ZFReplay.replay (packetBytesRecursionAllInternalFoldReverseDecomposition_kernel_certificate w C n t a)

def packetBytesRecursionIndependentCriterionBackwardSentence {m} (w C n t a : Fin m) : Source.Sentence := ((omega w).imp ((PacketBytesRecursionSyntax.caseAt w C n t a).imp ((PacketBytesTraceSyntax.foldAt w C n t a)))).close

theorem source_packetBytesRecursionIndependentCriterionBackward {m} (w C n t a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetBytesRecursionIndependentCriterionBackwardSentence w C n t a) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketBytesRecursionSyntax.caseAt w C n t a) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PacketBytesRecursionSyntax.caseAt w C n t a) := .hyp (Or.inl rfl)
  exact PacketBytesRecursionEquation.backward hZ w C n t a h0 h1

theorem packetBytesRecursionIndependentCriterionBackward_kernel_certificate {m} (w C n t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetBytesRecursionIndependentCriterionBackwardSentence w C n t a)) := TheoryTransport.sentence (source_packetBytesRecursionIndependentCriterionBackward w C n t a)

theorem native_packetBytesRecursionIndependentCriterionBackward {m} (w C n t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetBytesRecursionIndependentCriterionBackwardSentence w C n t a)) := ZFReplay.replay (packetBytesRecursionIndependentCriterionBackward_kernel_certificate w C n t a)

def packetBytesRecursionExactAllInternalRadixRecursionSentence {m} (w C n t a : Fin m) : Source.Sentence := ((omega w).imp (((PacketBytesTraceSyntax.foldAt w C n t a).iff (PacketBytesRecursionSyntax.caseAt w C n t a)))).close

theorem source_packetBytesRecursionExactAllInternalRadixRecursion {m} (w C n t a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetBytesRecursionExactAllInternalRadixRecursionSentence w C n t a) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact PacketBytesRecursionEquation.fold_iff hZ w C n t a h0

theorem packetBytesRecursionExactAllInternalRadixRecursion_kernel_certificate {m} (w C n t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetBytesRecursionExactAllInternalRadixRecursionSentence w C n t a)) := TheoryTransport.sentence (source_packetBytesRecursionExactAllInternalRadixRecursion w C n t a)

theorem native_packetBytesRecursionExactAllInternalRadixRecursion {m} (w C n t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetBytesRecursionExactAllInternalRadixRecursionSentence w C n t a)) := ZFReplay.replay (packetBytesRecursionExactAllInternalRadixRecursion_kernel_certificate w C n t a)

def packetBytesRecursionActual256CriterionEquivalenceSentence {m} (w C n t a : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 256 C).imp (((PacketBytesRecursionSyntax.caseAt w C n t a).iff (PacketBytesRecursionSyntax.criterion w n t a))))).close

theorem source_packetBytesRecursionActual256CriterionEquivalence {m} (w C n t a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetBytesRecursionActual256CriterionEquivalenceSentence w C n t a) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNumeralSyntax.numeral 256 C) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 256 C) := .hyp (Or.inl rfl)
  exact PacketBytesRecursionBridge.cases_iff hZ w C n t a h0 h1

theorem packetBytesRecursionActual256CriterionEquivalence_kernel_certificate {m} (w C n t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetBytesRecursionActual256CriterionEquivalenceSentence w C n t a)) := TheoryTransport.sentence (source_packetBytesRecursionActual256CriterionEquivalence w C n t a)

theorem native_packetBytesRecursionActual256CriterionEquivalence {m} (w C n t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetBytesRecursionActual256CriterionEquivalenceSentence w C n t a)) := ZFReplay.replay (packetBytesRecursionActual256CriterionEquivalence_kernel_certificate w C n t a)

def packetBytesRecursionActualBytesExactRecursionOnlyOmegaSentence {m} (w n t a : Fin m) : Source.Sentence := ((omega w).imp (((PacketBytesTraceSyntax.bytes w n t a).iff (PacketBytesRecursionSyntax.criterion w n t a)))).close

theorem source_packetBytesRecursionActualBytesExactRecursionOnlyOmega {m} (w n t a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetBytesRecursionActualBytesExactRecursionOnlyOmegaSentence w n t a) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact PacketBytesRecursionLaws.actual_iff hZ w n t a h0

theorem packetBytesRecursionActualBytesExactRecursionOnlyOmega_kernel_certificate {m} (w n t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetBytesRecursionActualBytesExactRecursionOnlyOmegaSentence w n t a)) := TheoryTransport.sentence (source_packetBytesRecursionActualBytesExactRecursionOnlyOmega w n t a)

theorem native_packetBytesRecursionActualBytesExactRecursionOnlyOmega {m} (w n t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetBytesRecursionActualBytesExactRecursionOnlyOmegaSentence w n t a)) := ZFReplay.replay (packetBytesRecursionActualBytesExactRecursionOnlyOmega_kernel_certificate w n t a)

def packetBytesRecursionAllInternalActualRecursionOnlyOmegaSentence {m} (w : Fin m) : Source.Sentence := ((omega w).imp ((PacketBytesRecursionLaws.allLaw w))).close

theorem source_packetBytesRecursionAllInternalActualRecursionOnlyOmega {m} (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetBytesRecursionAllInternalActualRecursionOnlyOmegaSentence w) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact PacketBytesRecursionLaws.all_law hZ w h0

theorem packetBytesRecursionAllInternalActualRecursionOnlyOmega_kernel_certificate {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetBytesRecursionAllInternalActualRecursionOnlyOmegaSentence w)) := TheoryTransport.sentence (source_packetBytesRecursionAllInternalActualRecursionOnlyOmega w)

theorem native_packetBytesRecursionAllInternalActualRecursionOnlyOmega {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetBytesRecursionAllInternalActualRecursionOnlyOmegaSentence w)) := ZFReplay.replay (packetBytesRecursionAllInternalActualRecursionOnlyOmega_kernel_certificate w)

end PPAC.Migration.Internal.ObjectPacketBytesRecursion
