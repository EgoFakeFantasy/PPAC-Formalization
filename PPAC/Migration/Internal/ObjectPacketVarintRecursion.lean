import PPAC.Migration.Internal.PacketVarintCanonicalRecursionLaws

/-! Exact all-internal independent canonical varint recursion: real restricted graphs, normalized last rows and nonempty smaller suffixes. Full canonical totality/uniqueness/byte domain, actual Tok correspondence, original program bridge, Proof and Con remain unproved -/
namespace PPAC.Migration.Internal.ObjectPacketVarintRecursion
open Source SourceAlgebra SourceLogic OmegaSyntax

def packetVarintRecursionBothGraphsFullOldRowRestrictionSentence {m} (w B p l f g F G i : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem p w).imp ((successor l p).imp ((RestrictionSyntax.restrict F f l).imp ((RestrictionSyntax.restrict G g l).imp ((Formula.mem i p).imp ((PacketVarintRowSyntax.row w B f g i).imp ((PacketVarintRowSyntax.row w B F G i))))))))).close

theorem source_packetVarintRecursionBothGraphsFullOldRowRestriction {m} (w B p l f g F G i : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetVarintRecursionBothGraphsFullOldRowRestrictionSentence w B p l f g F G i) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketVarintRowSyntax.row w B f g i) (Context.add (Formula.mem i p) (Context.add (RestrictionSyntax.restrict G g l) (Context.add (RestrictionSyntax.restrict F f l) (Context.add (successor l p) (Context.add (Formula.mem p w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))
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
  have h6 : Derives Δ (PacketVarintRowSyntax.row w B f g i) := .hyp (Or.inl rfl)
  exact PacketVarintRowRestrict.row_restrict hZ w B p l f g F G i h0 h1 h2 h3 h4 h5 h6

theorem packetVarintRecursionBothGraphsFullOldRowRestriction_kernel_certificate {m} (w B p l f g F G i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetVarintRecursionBothGraphsFullOldRowRestrictionSentence w B p l f g F G i)) := TheoryTransport.sentence (source_packetVarintRecursionBothGraphsFullOldRowRestriction w B p l f g F G i)

theorem native_packetVarintRecursionBothGraphsFullOldRowRestriction {m} (w B p l f g F G i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetVarintRecursionBothGraphsFullOldRowRestrictionSentence w B p l f g F G i)) := ZFReplay.replay (packetVarintRecursionBothGraphsFullOldRowRestriction_kernel_certificate w B p l f g F G i)

def packetVarintRecursionBothGraphsAllOldLinksRestrictionSentence {m} (w B p l f g F G : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem p w).imp ((successor l p).imp ((PacketVarintRowSyntax.links w B l f g).imp ((RestrictionSyntax.restrict F f l).imp ((RestrictionSyntax.restrict G g l).imp ((PacketVarintRowSyntax.links w B p F G)))))))).close

theorem source_packetVarintRecursionBothGraphsAllOldLinksRestriction {m} (w B p l f g F G : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetVarintRecursionBothGraphsAllOldLinksRestrictionSentence w B p l f g F G) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (RestrictionSyntax.restrict G g l) (Context.add (RestrictionSyntax.restrict F f l) (Context.add (PacketVarintRowSyntax.links w B l f g) (Context.add (successor l p) (Context.add (Formula.mem p w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
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
  have h3 : Derives Δ (PacketVarintRowSyntax.links w B l f g) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (RestrictionSyntax.restrict F f l) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (RestrictionSyntax.restrict G g l) := .hyp (Or.inl rfl)
  exact PacketVarintRowRestrict.links_restrict hZ w B p l f g F G h0 h1 h2 h3 h4 h5

theorem packetVarintRecursionBothGraphsAllOldLinksRestriction_kernel_certificate {m} (w B p l f g F G : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetVarintRecursionBothGraphsAllOldLinksRestrictionSentence w B p l f g F G)) := TheoryTransport.sentence (source_packetVarintRecursionBothGraphsAllOldLinksRestriction w B p l f g F G)

theorem native_packetVarintRecursionBothGraphsAllOldLinksRestriction {m} (w B p l f g F G : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetVarintRecursionBothGraphsAllOldLinksRestrictionSentence w B p l f g F G)) := ZFReplay.replay (packetVarintRecursionBothGraphsAllOldLinksRestriction_kernel_certificate w B p l f g F G)

def packetVarintRecursionActualPrefixGraphsConstructedAndEliminatedSentence {m} (w B n t a z e l d f g p x u : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem p w).imp ((successor l p).imp ((PacketVarintTraceSyntax.trace w B n t a z e l d f g).imp ((GraphSyntax.edge f p x).imp ((GraphSyntax.edge g p u).imp ((PacketVarintTraceSyntax.foldAt w B x t u)))))))).close

theorem source_packetVarintRecursionActualPrefixGraphsConstructedAndEliminated {m} (w B n t a z e l d f g p x u : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetVarintRecursionActualPrefixGraphsConstructedAndEliminatedSentence w B n t a z e l d f g p x u) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (GraphSyntax.edge g p u) (Context.add (GraphSyntax.edge f p x) (Context.add (PacketVarintTraceSyntax.trace w B n t a z e l d f g) (Context.add (successor l p) (Context.add (Formula.mem p w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
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
  have h3 : Derives Δ (PacketVarintTraceSyntax.trace w B n t a z e l d f g) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (GraphSyntax.edge f p x) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (GraphSyntax.edge g p u) := .hyp (Or.inl rfl)
  exact PacketVarintTracePrefix.exists_prefix hZ w B n t a z e l d f g p x u h0 h1 h2 h3 h4 h5

theorem packetVarintRecursionActualPrefixGraphsConstructedAndEliminated_kernel_certificate {m} (w B n t a z e l d f g p x u : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetVarintRecursionActualPrefixGraphsConstructedAndEliminatedSentence w B n t a z e l d f g p x u)) := TheoryTransport.sentence (source_packetVarintRecursionActualPrefixGraphsConstructedAndEliminated w B n t a z e l d f g p x u)

theorem native_packetVarintRecursionActualPrefixGraphsConstructedAndEliminated {m} (w B n t a z e l d f g p x u : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetVarintRecursionActualPrefixGraphsConstructedAndEliminatedSentence w B n t a z e l d f g p x u)) := ZFReplay.replay (packetVarintRecursionActualPrefixGraphsConstructedAndEliminated_kernel_certificate w B n t a z e l d f g p x u)

def packetVarintRecursionCompleteActualLastRowNormalizedSentence {m} (w B n t a z e l d f g p : Fin m) : Source.Sentence := ((successor l p).imp ((PacketVarintTraceSyntax.trace w B n t a z e l d f g).imp ((PacketVarintRecursionSyntax.terminal w B f g p n a)))).close

theorem source_packetVarintRecursionCompleteActualLastRowNormalized {m} (w B n t a z e l d f g p : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetVarintRecursionCompleteActualLastRowNormalizedSentence w B n t a z e l d f g p) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketVarintTraceSyntax.trace w B n t a z e l d f g) (Context.add (successor l p) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (successor l p) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PacketVarintTraceSyntax.trace w B n t a z e l d f g) := .hyp (Or.inl rfl)
  exact PacketVarintTerminal.terminal_row hZ w B n t a z e l d f g p h0 h1

theorem packetVarintRecursionCompleteActualLastRowNormalized_kernel_certificate {m} (w B n t a z e l d f g p : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetVarintRecursionCompleteActualLastRowNormalizedSentence w B n t a z e l d f g p)) := TheoryTransport.sentence (source_packetVarintRecursionCompleteActualLastRowNormalized w B n t a z e l d f g p)

theorem native_packetVarintRecursionCompleteActualLastRowNormalized {m} (w B n t a z e l d f g p : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetVarintRecursionCompleteActualLastRowNormalizedSentence w B n t a z e l d f g p)) := ZFReplay.replay (packetVarintRecursionCompleteActualLastRowNormalized_kernel_certificate w B n t a z e l d f g p)

def packetVarintRecursionAllInternalRawFoldReverseDecompositionSentence {m} (w B n t a : Fin m) : Source.Sentence := ((omega w).imp ((PacketVarintTraceSyntax.foldAt w B n t a).imp ((PacketVarintRecursionSyntax.caseAt w B n t a)))).close

theorem source_packetVarintRecursionAllInternalRawFoldReverseDecomposition {m} (w B n t a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetVarintRecursionAllInternalRawFoldReverseDecompositionSentence w B n t a) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketVarintTraceSyntax.foldAt w B n t a) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PacketVarintTraceSyntax.foldAt w B n t a) := .hyp (Or.inl rfl)
  exact PacketVarintDecomposition.fold_forward hZ w B n t a h0 h1

theorem packetVarintRecursionAllInternalRawFoldReverseDecomposition_kernel_certificate {m} (w B n t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetVarintRecursionAllInternalRawFoldReverseDecompositionSentence w B n t a)) := TheoryTransport.sentence (source_packetVarintRecursionAllInternalRawFoldReverseDecomposition w B n t a)

theorem native_packetVarintRecursionAllInternalRawFoldReverseDecomposition {m} (w B n t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetVarintRecursionAllInternalRawFoldReverseDecompositionSentence w B n t a)) := ZFReplay.replay (packetVarintRecursionAllInternalRawFoldReverseDecomposition_kernel_certificate w B n t a)

def packetVarintRecursionAllInternalRawFoldExactRecursionSentence {m} (w B n t a : Fin m) : Source.Sentence := ((omega w).imp (((PacketVarintTraceSyntax.foldAt w B n t a).iff (PacketVarintRecursionSyntax.caseAt w B n t a)))).close

theorem source_packetVarintRecursionAllInternalRawFoldExactRecursion {m} (w B n t a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetVarintRecursionAllInternalRawFoldExactRecursionSentence w B n t a) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact PacketVarintRecursionEquation.fold_iff hZ w B n t a h0

theorem packetVarintRecursionAllInternalRawFoldExactRecursion_kernel_certificate {m} (w B n t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetVarintRecursionAllInternalRawFoldExactRecursionSentence w B n t a)) := TheoryTransport.sentence (source_packetVarintRecursionAllInternalRawFoldExactRecursion w B n t a)

theorem native_packetVarintRecursionAllInternalRawFoldExactRecursion {m} (w B n t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetVarintRecursionAllInternalRawFoldExactRecursionSentence w B n t a)) := ZFReplay.replay (packetVarintRecursionAllInternalRawFoldExactRecursion_kernel_certificate w B n t a)

def packetVarintRecursionNonzeroValueForcesActualNonemptySuffixSentence {m} (w B x z q : Fin m) : Source.Sentence := ((omega w).imp ((empty z).imp ((PacketVarintTraceSyntax.foldAt w B x z q).imp (((empty q).neg).imp (((StructuralListSyntax.nilCode w x).neg)))))).close

theorem source_packetVarintRecursionNonzeroValueForcesActualNonemptySuffix {m} (w B x z q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetVarintRecursionNonzeroValueForcesActualNonemptySuffixSentence w B x z q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add ((empty q).neg) (Context.add (PacketVarintTraceSyntax.foldAt w B x z q) (Context.add (empty z) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (empty z) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (PacketVarintTraceSyntax.foldAt w B x z q) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ ((empty q).neg) := .hyp (Or.inl rfl)
  exact PacketVarintCanonicalPieces.nonempty_suffix hZ w B x z q h0 h1 h2 h3

theorem packetVarintRecursionNonzeroValueForcesActualNonemptySuffix_kernel_certificate {m} (w B x z q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetVarintRecursionNonzeroValueForcesActualNonemptySuffixSentence w B x z q)) := TheoryTransport.sentence (source_packetVarintRecursionNonzeroValueForcesActualNonemptySuffix w B x z q)

theorem native_packetVarintRecursionNonzeroValueForcesActualNonemptySuffix {m} (w B x z q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetVarintRecursionNonzeroValueForcesActualNonemptySuffixSentence w B x z q)) := ZFReplay.replay (packetVarintRecursionNonzeroValueForcesActualNonemptySuffix_kernel_certificate w B x z q)

def packetVarintRecursionCanonicalTerminalHeadAlignedSentence {m} (w B s n h x q : Fin m) : Source.Sentence := ((StructuralListSyntax.consCode w h x s).imp ((PacketVarintCellSyntax.terminal w B x h q n).imp ((PacketVarintCanonicalRecursionSyntax.smallCase w B n s)))).close

theorem source_packetVarintRecursionCanonicalTerminalHeadAligned {m} (w B s n h x q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetVarintRecursionCanonicalTerminalHeadAlignedSentence w B s n h x q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketVarintCellSyntax.terminal w B x h q n) (Context.add (StructuralListSyntax.consCode w h x s) (Source.SetLanguage.ZF.at m))
  have h0 : Derives Δ (StructuralListSyntax.consCode w h x s) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PacketVarintCellSyntax.terminal w B x h q n) := .hyp (Or.inl rfl)
  exact PacketVarintCanonicalPieces.terminal_point w B s n h x q h0 h1

theorem packetVarintRecursionCanonicalTerminalHeadAligned_kernel_certificate {m} (w B s n h x q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetVarintRecursionCanonicalTerminalHeadAlignedSentence w B s n h x q)) := TheoryTransport.sentence (source_packetVarintRecursionCanonicalTerminalHeadAligned w B s n h x q)

theorem native_packetVarintRecursionCanonicalTerminalHeadAligned {m} (w B s n h x q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetVarintRecursionCanonicalTerminalHeadAlignedSentence w B s n h x q)) := ZFReplay.replay (packetVarintRecursionCanonicalTerminalHeadAligned_kernel_certificate w B s n h x q)

def packetVarintRecursionAllInternalCanonicalReverseDecompositionSentence {m} (w B n s : Fin m) : Source.Sentence := ((omega w).imp ((PacketVarintSyntax.canonicalAt w B n s).imp ((PacketVarintCanonicalRecursionSyntax.atCriterion false w B n s)))).close

theorem source_packetVarintRecursionAllInternalCanonicalReverseDecomposition {m} (w B n s : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetVarintRecursionAllInternalCanonicalReverseDecompositionSentence w B n s) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketVarintSyntax.canonicalAt w B n s) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PacketVarintSyntax.canonicalAt w B n s) := .hyp (Or.inl rfl)
  exact PacketVarintCanonicalDecomposition.at_forward hZ w B n s h0 h1

theorem packetVarintRecursionAllInternalCanonicalReverseDecomposition_kernel_certificate {m} (w B n s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetVarintRecursionAllInternalCanonicalReverseDecompositionSentence w B n s)) := TheoryTransport.sentence (source_packetVarintRecursionAllInternalCanonicalReverseDecomposition w B n s)

theorem native_packetVarintRecursionAllInternalCanonicalReverseDecomposition {m} (w B n s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetVarintRecursionAllInternalCanonicalReverseDecompositionSentence w B n s)) := ZFReplay.replay (packetVarintRecursionAllInternalCanonicalReverseDecomposition_kernel_certificate w B n s)

def packetVarintRecursionExactCanonicalRecursionAtNaturalRadixSentence {m} (w B n s : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem B w).imp (((PacketVarintSyntax.canonicalAt w B n s).iff (PacketVarintCanonicalRecursionSyntax.atCriterion false w B n s))))).close

theorem source_packetVarintRecursionExactCanonicalRecursionAtNaturalRadix {m} (w B n s : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetVarintRecursionExactCanonicalRecursionAtNaturalRadixSentence w B n s) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem B w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (Formula.mem B w) := .hyp (Or.inl rfl)
  exact PacketVarintCanonicalRecursionEquation.at_iff hZ w B n s h0 h1

theorem packetVarintRecursionExactCanonicalRecursionAtNaturalRadix_kernel_certificate {m} (w B n s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetVarintRecursionExactCanonicalRecursionAtNaturalRadixSentence w B n s)) := TheoryTransport.sentence (source_packetVarintRecursionExactCanonicalRecursionAtNaturalRadix w B n s)

theorem native_packetVarintRecursionExactCanonicalRecursionAtNaturalRadix {m} (w B n s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetVarintRecursionExactCanonicalRecursionAtNaturalRadixSentence w B n s)) := ZFReplay.replay (packetVarintRecursionExactCanonicalRecursionAtNaturalRadix_kernel_certificate w B n s)

def packetVarintRecursionActual128CompleteSmallerGraphAlignmentSentence {m} (w B n s : Fin m) : Source.Sentence := ((SyntaxNumeralSyntax.numeral 128 B).imp (((PacketVarintCanonicalRecursionSyntax.largeCase false w B n s).iff (PacketVarintCanonicalRecursionSyntax.largeCase true w B n s)))).close

theorem source_packetVarintRecursionActual128CompleteSmallerGraphAlignment {m} (w B n s : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetVarintRecursionActual128CompleteSmallerGraphAlignmentSentence w B n s) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNumeralSyntax.numeral 128 B) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (SyntaxNumeralSyntax.numeral 128 B) := .hyp (Or.inl rfl)
  exact PacketVarintCanonicalRecursionBridge.large_iff hZ w B n s h0

theorem packetVarintRecursionActual128CompleteSmallerGraphAlignment_kernel_certificate {m} (w B n s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetVarintRecursionActual128CompleteSmallerGraphAlignmentSentence w B n s)) := TheoryTransport.sentence (source_packetVarintRecursionActual128CompleteSmallerGraphAlignment w B n s)

theorem native_packetVarintRecursionActual128CompleteSmallerGraphAlignment {m} (w B n s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetVarintRecursionActual128CompleteSmallerGraphAlignmentSentence w B n s)) := ZFReplay.replay (packetVarintRecursionActual128CompleteSmallerGraphAlignment_kernel_certificate w B n s)

def packetVarintRecursionActual128CanonicalExactRecursionSentence {m} (w B n s : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 128 B).imp (((PacketVarintSyntax.canonicalAt w B n s).iff (PacketVarintCanonicalRecursionSyntax.atCriterion true w B n s))))).close

theorem source_packetVarintRecursionActual128CanonicalExactRecursion {m} (w B n s : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetVarintRecursionActual128CanonicalExactRecursionSentence w B n s) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNumeralSyntax.numeral 128 B) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 128 B) := .hyp (Or.inl rfl)
  exact PacketVarintCanonicalRecursionBridge.at_actual_iff hZ w B n s h0 h1

theorem packetVarintRecursionActual128CanonicalExactRecursion_kernel_certificate {m} (w B n s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetVarintRecursionActual128CanonicalExactRecursionSentence w B n s)) := TheoryTransport.sentence (source_packetVarintRecursionActual128CanonicalExactRecursion w B n s)

theorem native_packetVarintRecursionActual128CanonicalExactRecursion {m} (w B n s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetVarintRecursionActual128CanonicalExactRecursionSentence w B n s)) := ZFReplay.replay (packetVarintRecursionActual128CanonicalExactRecursion_kernel_certificate w B n s)

def packetVarintRecursionActualCanonicalExactRecursionOnlyOmegaSentence {m} (w n s : Fin m) : Source.Sentence := ((omega w).imp (((PacketVarintSyntax.canonical w n s).iff (PacketVarintCanonicalRecursionSyntax.criterion w n s)))).close

theorem source_packetVarintRecursionActualCanonicalExactRecursionOnlyOmega {m} (w n s : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetVarintRecursionActualCanonicalExactRecursionOnlyOmegaSentence w n s) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact PacketVarintCanonicalRecursionLaws.actual_iff hZ w n s h0

theorem packetVarintRecursionActualCanonicalExactRecursionOnlyOmega_kernel_certificate {m} (w n s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetVarintRecursionActualCanonicalExactRecursionOnlyOmegaSentence w n s)) := TheoryTransport.sentence (source_packetVarintRecursionActualCanonicalExactRecursionOnlyOmega w n s)

theorem native_packetVarintRecursionActualCanonicalExactRecursionOnlyOmega {m} (w n s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetVarintRecursionActualCanonicalExactRecursionOnlyOmegaSentence w n s)) := ZFReplay.replay (packetVarintRecursionActualCanonicalExactRecursionOnlyOmega_kernel_certificate w n s)

def packetVarintRecursionAllInternalActualCanonicalRecursionOnlyOmegaSentence {m} (w : Fin m) : Source.Sentence := ((omega w).imp ((PacketVarintCanonicalRecursionSyntax.allLaw w))).close

theorem source_packetVarintRecursionAllInternalActualCanonicalRecursionOnlyOmega {m} (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetVarintRecursionAllInternalActualCanonicalRecursionOnlyOmegaSentence w) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact PacketVarintCanonicalRecursionLaws.all_law hZ w h0

theorem packetVarintRecursionAllInternalActualCanonicalRecursionOnlyOmega_kernel_certificate {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetVarintRecursionAllInternalActualCanonicalRecursionOnlyOmegaSentence w)) := TheoryTransport.sentence (source_packetVarintRecursionAllInternalActualCanonicalRecursionOnlyOmega w)

theorem native_packetVarintRecursionAllInternalActualCanonicalRecursionOnlyOmega {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetVarintRecursionAllInternalActualCanonicalRecursionOnlyOmegaSentence w)) := ZFReplay.replay (packetVarintRecursionAllInternalActualCanonicalRecursionOnlyOmega_kernel_certificate w)

end PPAC.Migration.Internal.ObjectPacketVarintRecursion
