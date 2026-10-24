import PPAC.Migration.Internal.PacketBytesLaws

/-! Independent ordered byte-fold traces with exact Nil fiber and constructive Cons closure; global totality uniqueness reverse recurrence and canonical-byte bridge remain unproved; full Basic AST and varint bridge remain unproved in the original nativeZF kernel; complete schema tests and Con remain unproved. -/
namespace PPAC.Migration.Internal.ObjectPacketBytesTrace
open Source SourceAlgebra SourceLogic OmegaSyntax

def packetBytesBothSequenceRowTransportSentence {m} (w C f g F G i : Fin m) : Source.Sentence := ((GraphPointwiseSyntax.edgeIncluded f F).imp ((GraphPointwiseSyntax.edgeIncluded g G).imp ((PacketBytesRowSyntax.row w C f g i).imp ((PacketBytesRowSyntax.row w C F G i))))).close

theorem source_packetBytesBothSequenceRowTransport {m} (w C f g F G i : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetBytesBothSequenceRowTransportSentence w C f g F G i) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketBytesRowSyntax.row w C f g i) (Context.add (GraphPointwiseSyntax.edgeIncluded g G) (Context.add (GraphPointwiseSyntax.edgeIncluded f F) (Source.SetLanguage.ZF.at m)))
  have h0 : Derives Δ (GraphPointwiseSyntax.edgeIncluded f F) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (GraphPointwiseSyntax.edgeIncluded g G) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (PacketBytesRowSyntax.row w C f g i) := .hyp (Or.inl rfl)
  exact PacketBytesRowMap.row_map w C f g F G i h0 h1 h2

theorem packetBytesBothSequenceRowTransport_kernel_certificate {m} (w C f g F G i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetBytesBothSequenceRowTransportSentence w C f g F G i)) := TheoryTransport.sentence (source_packetBytesBothSequenceRowTransport w C f g F G i)

theorem native_packetBytesBothSequenceRowTransport {m} (w C f g F G i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetBytesBothSequenceRowTransportSentence w C f g F G i)) := ZFReplay.replay (packetBytesBothSequenceRowTransport_kernel_certificate w C f g F G i)

def packetBytesBothSequenceLinksAppendSentence {m} (w C l d f g F G : Fin m) : Source.Sentence := ((successor d l).imp ((PacketBytesRowSyntax.links w C l f g).imp ((GraphPointwiseSyntax.edgeIncluded f F).imp ((GraphPointwiseSyntax.edgeIncluded g G).imp ((PacketBytesRowSyntax.row w C F G l).imp ((PacketBytesRowSyntax.links w C d F G))))))).close

theorem source_packetBytesBothSequenceLinksAppend {m} (w C l d f g F G : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetBytesBothSequenceLinksAppendSentence w C l d f g F G) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketBytesRowSyntax.row w C F G l) (Context.add (GraphPointwiseSyntax.edgeIncluded g G) (Context.add (GraphPointwiseSyntax.edgeIncluded f F) (Context.add (PacketBytesRowSyntax.links w C l f g) (Context.add (successor d l) (Source.SetLanguage.ZF.at m)))))
  have h0 : Derives Δ (successor d l) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (PacketBytesRowSyntax.links w C l f g) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (GraphPointwiseSyntax.edgeIncluded f F) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (GraphPointwiseSyntax.edgeIncluded g G) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (PacketBytesRowSyntax.row w C F G l) := .hyp (Or.inl rfl)
  exact PacketBytesRowMap.append_links w C l d f g F G h0 h1 h2 h3 h4

theorem packetBytesBothSequenceLinksAppend_kernel_certificate {m} (w C l d f g F G : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetBytesBothSequenceLinksAppendSentence w C l d f g F G)) := TheoryTransport.sentence (source_packetBytesBothSequenceLinksAppend w C l d f g F G)

theorem native_packetBytesBothSequenceLinksAppend {m} (w C l d f g F G : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetBytesBothSequenceLinksAppendSentence w C l d f g F G)) := ZFReplay.replay (packetBytesBothSequenceLinksAppend_kernel_certificate w C l d f g F G)

def packetBytesOriginalDualSequenceAppendSentence {m} (w C n t a z e l d f g h p b k F G : Fin m) : Source.Sentence := ((omega w).imp ((PacketBytesTraceSyntax.trace w C n t a z e l d f g).imp ((StructuralListSyntax.consCode w h n p).imp ((PacketAffineSyntax.affine w C h a b).imp ((successor k d).imp ((SequenceSyntax.append F k f d p w).imp ((SequenceSyntax.append G k g d b w).imp ((PacketBytesTraceSyntax.trace w C p t b z e d k F G))))))))).close

theorem source_packetBytesOriginalDualSequenceAppend {m} (w C n t a z e l d f g h p b k F G : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetBytesOriginalDualSequenceAppendSentence w C n t a z e l d f g h p b k F G) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SequenceSyntax.append G k g d b w) (Context.add (SequenceSyntax.append F k f d p w) (Context.add (successor k d) (Context.add (PacketAffineSyntax.affine w C h a b) (Context.add (StructuralListSyntax.consCode w h n p) (Context.add (PacketBytesTraceSyntax.trace w C n t a z e l d f g) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))
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
  have h1 : Derives Δ (PacketBytesTraceSyntax.trace w C n t a z e l d f g) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h2 : Derives Δ (StructuralListSyntax.consCode w h n p) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h3 : Derives Δ (PacketAffineSyntax.affine w C h a b) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : Derives Δ (successor k d) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h5 : Derives Δ (SequenceSyntax.append F k f d p w) := .hyp (Or.inr (Or.inl rfl))
  have h6 : Derives Δ (SequenceSyntax.append G k g d b w) := .hyp (Or.inl rfl)
  exact PacketBytesTraceAppend.from_append hZ w C n t a z e l d f g h p b k F G h0 h1 h2 h3 h4 h5 h6

theorem packetBytesOriginalDualSequenceAppend_kernel_certificate {m} (w C n t a z e l d f g h p b k F G : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetBytesOriginalDualSequenceAppendSentence w C n t a z e l d f g h p b k F G)) := TheoryTransport.sentence (source_packetBytesOriginalDualSequenceAppend w C n t a z e l d f g h p b k F G)

theorem native_packetBytesOriginalDualSequenceAppend {m} (w C n t a z e l d f g h p b k F G : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetBytesOriginalDualSequenceAppendSentence w C n t a z e l d f g h p b k F G)) := ZFReplay.replay (packetBytesOriginalDualSequenceAppend_kernel_certificate w C n t a z e l d f g h p b k F G)

def packetBytesTraceExtensionWitnessesEliminatedSentence {m} (w C n t a z e l d f g h p b : Fin m) : Source.Sentence := ((omega w).imp ((PacketBytesTraceSyntax.trace w C n t a z e l d f g).imp ((StructuralListSyntax.consCode w h n p).imp ((PacketAffineSyntax.affine w C h a b).imp ((PacketBytesTraceSyntax.foldAt w C p t b)))))).close

theorem source_packetBytesTraceExtensionWitnessesEliminated {m} (w C n t a z e l d f g h p b : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetBytesTraceExtensionWitnessesEliminatedSentence w C n t a z e l d f g h p b) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketAffineSyntax.affine w C h a b) (Context.add (StructuralListSyntax.consCode w h n p) (Context.add (PacketBytesTraceSyntax.trace w C n t a z e l d f g) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (PacketBytesTraceSyntax.trace w C n t a z e l d f g) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (StructuralListSyntax.consCode w h n p) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (PacketAffineSyntax.affine w C h a b) := .hyp (Or.inl rfl)
  exact PacketBytesTraceAppend.extend_trace hZ w C n t a z e l d f g h p b h0 h1 h2 h3

theorem packetBytesTraceExtensionWitnessesEliminated_kernel_certificate {m} (w C n t a z e l d f g h p b : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetBytesTraceExtensionWitnessesEliminatedSentence w C n t a z e l d f g h p b)) := TheoryTransport.sentence (source_packetBytesTraceExtensionWitnessesEliminated w C n t a z e l d f g h p b)

theorem native_packetBytesTraceExtensionWitnessesEliminated {m} (w C n t a z e l d f g h p b : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetBytesTraceExtensionWitnessesEliminatedSentence w C n t a z e l d f g h p b)) := ZFReplay.replay (packetBytesTraceExtensionWitnessesEliminated_kernel_certificate w C n t a z e l d f g h p b)

def packetBytesFullConsForwardAtRadixSentence {m} (w C n t a h p b : Fin m) : Source.Sentence := ((omega w).imp ((PacketBytesTraceSyntax.foldAt w C n t a).imp ((StructuralListSyntax.consCode w h n p).imp ((PacketAffineSyntax.affine w C h a b).imp ((PacketBytesTraceSyntax.foldAt w C p t b)))))).close

theorem source_packetBytesFullConsForwardAtRadix {m} (w C n t a h p b : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetBytesFullConsForwardAtRadixSentence w C n t a h p b) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketAffineSyntax.affine w C h a b) (Context.add (StructuralListSyntax.consCode w h n p) (Context.add (PacketBytesTraceSyntax.foldAt w C n t a) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (PacketBytesTraceSyntax.foldAt w C n t a) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (StructuralListSyntax.consCode w h n p) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (PacketAffineSyntax.affine w C h a b) := .hyp (Or.inl rfl)
  exact PacketBytesTraceAppend.cons_fold hZ w C n t a h p b h0 h1 h2 h3

theorem packetBytesFullConsForwardAtRadix_kernel_certificate {m} (w C n t a h p b : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetBytesFullConsForwardAtRadixSentence w C n t a h p b)) := TheoryTransport.sentence (source_packetBytesFullConsForwardAtRadix w C n t a h p b)

theorem native_packetBytesFullConsForwardAtRadix {m} (w C n t a h p b : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetBytesFullConsForwardAtRadixSentence w C n t a h p b)) := ZFReplay.replay (packetBytesFullConsForwardAtRadix_kernel_certificate w C n t a h p b)

def packetBytesNilExactFiberAtRadixSentence {m} (w C n t a : Fin m) : Source.Sentence := ((omega w).imp ((StructuralListSyntax.nilCode w n).imp (((PacketBytesTraceSyntax.foldAt w C n t a).iff ((Formula.mem t w).conj (.equal t a)))))).close

theorem source_packetBytesNilExactFiberAtRadix {m} (w C n t a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetBytesNilExactFiberAtRadixSentence w C n t a) := by
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
  exact PacketBytesTraceBase.nil_iff hZ w C n t a h0 h1

theorem packetBytesNilExactFiberAtRadix_kernel_certificate {m} (w C n t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetBytesNilExactFiberAtRadixSentence w C n t a)) := TheoryTransport.sentence (source_packetBytesNilExactFiberAtRadix w C n t a)

theorem native_packetBytesNilExactFiberAtRadix {m} (w C n t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetBytesNilExactFiberAtRadixSentence w C n t a)) := ZFReplay.replay (packetBytesNilExactFiberAtRadix_kernel_certificate w C n t a)

def packetBytesFoldOriginalValidityAndNaturalDomainSentence {m} (w C n t a : Fin m) : Source.Sentence := ((PacketBytesTraceSyntax.foldAt w C n t a).imp (((StructuralListTraceSyntax.valid w n).conj ((Formula.mem t w).conj (.mem a w))))).close

theorem source_packetBytesFoldOriginalValidityAndNaturalDomain {m} (w C n t a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetBytesFoldOriginalValidityAndNaturalDomainSentence w C n t a) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (PacketBytesTraceSyntax.foldAt w C n t a) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (PacketBytesTraceSyntax.foldAt w C n t a) := .hyp (Or.inl rfl)
  exact PacketBytesTraceBase.domain w C n t a h0

theorem packetBytesFoldOriginalValidityAndNaturalDomain_kernel_certificate {m} (w C n t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetBytesFoldOriginalValidityAndNaturalDomainSentence w C n t a)) := TheoryTransport.sentence (source_packetBytesFoldOriginalValidityAndNaturalDomain w C n t a)

theorem native_packetBytesFoldOriginalValidityAndNaturalDomain {m} (w C n t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetBytesFoldOriginalValidityAndNaturalDomainSentence w C n t a)) := ZFReplay.replay (packetBytesFoldOriginalValidityAndNaturalDomain_kernel_certificate w C n t a)

def packetBytesActual256ExactGraphIffSentence {m} (w C n t a : Fin m) : Source.Sentence := ((SyntaxNumeralSyntax.numeral 256 C).imp (((PacketBytesTraceSyntax.bytes w n t a).iff (PacketBytesTraceSyntax.foldAt w C n t a)))).close

theorem source_packetBytesActual256ExactGraphIff {m} (w C n t a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetBytesActual256ExactGraphIffSentence w C n t a) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNumeralSyntax.numeral 256 C) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (SyntaxNumeralSyntax.numeral 256 C) := .hyp (Or.inl rfl)
  exact PacketBytesLaws.fold_iff hZ w C n t a h0

theorem packetBytesActual256ExactGraphIff_kernel_certificate {m} (w C n t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetBytesActual256ExactGraphIffSentence w C n t a)) := TheoryTransport.sentence (source_packetBytesActual256ExactGraphIff w C n t a)

theorem native_packetBytesActual256ExactGraphIff {m} (w C n t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetBytesActual256ExactGraphIffSentence w C n t a)) := ZFReplay.replay (packetBytesActual256ExactGraphIff_kernel_certificate w C n t a)

def packetBytesActualByteDomainSentence {m} (w n t a : Fin m) : Source.Sentence := ((PacketBytesTraceSyntax.bytes w n t a).imp (((StructuralListTraceSyntax.valid w n).conj ((Formula.mem t w).conj (.mem a w))))).close

theorem source_packetBytesActualByteDomain {m} (w n t a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetBytesActualByteDomainSentence w n t a) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (PacketBytesTraceSyntax.bytes w n t a) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (PacketBytesTraceSyntax.bytes w n t a) := .hyp (Or.inl rfl)
  exact PacketBytesLaws.domain w n t a h0

theorem packetBytesActualByteDomain_kernel_certificate {m} (w n t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetBytesActualByteDomainSentence w n t a)) := TheoryTransport.sentence (source_packetBytesActualByteDomain w n t a)

theorem native_packetBytesActualByteDomain {m} (w n t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetBytesActualByteDomainSentence w n t a)) := ZFReplay.replay (packetBytesActualByteDomain_kernel_certificate w n t a)

def packetBytesActualNilExistsOnlyOmegaSentence {m} (w n t : Fin m) : Source.Sentence := ((omega w).imp ((StructuralListSyntax.nilCode w n).imp ((Formula.mem t w).imp ((PacketBytesTraceSyntax.bytes w n t t))))).close

theorem source_packetBytesActualNilExistsOnlyOmega {m} (w n t : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetBytesActualNilExistsOnlyOmegaSentence w n t) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem t w) (Context.add (StructuralListSyntax.nilCode w n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (StructuralListSyntax.nilCode w n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (Formula.mem t w) := .hyp (Or.inl rfl)
  exact PacketBytesLaws.nil_fold hZ w n t h0 h1 h2

theorem packetBytesActualNilExistsOnlyOmega_kernel_certificate {m} (w n t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetBytesActualNilExistsOnlyOmegaSentence w n t)) := TheoryTransport.sentence (source_packetBytesActualNilExistsOnlyOmega w n t)

theorem native_packetBytesActualNilExistsOnlyOmega {m} (w n t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetBytesActualNilExistsOnlyOmegaSentence w n t)) := ZFReplay.replay (packetBytesActualNilExistsOnlyOmega_kernel_certificate w n t)

def packetBytesActualNilIffOnlyOmegaSentence {m} (w n t a : Fin m) : Source.Sentence := ((omega w).imp ((StructuralListSyntax.nilCode w n).imp (((PacketBytesTraceSyntax.bytes w n t a).iff ((Formula.mem t w).conj (.equal t a)))))).close

theorem source_packetBytesActualNilIffOnlyOmega {m} (w n t a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetBytesActualNilIffOnlyOmegaSentence w n t a) := by
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
  exact PacketBytesLaws.nil_iff hZ w n t a h0 h1

theorem packetBytesActualNilIffOnlyOmega_kernel_certificate {m} (w n t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetBytesActualNilIffOnlyOmegaSentence w n t a)) := TheoryTransport.sentence (source_packetBytesActualNilIffOnlyOmega w n t a)

theorem native_packetBytesActualNilIffOnlyOmega {m} (w n t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetBytesActualNilIffOnlyOmegaSentence w n t a)) := ZFReplay.replay (packetBytesActualNilIffOnlyOmega_kernel_certificate w n t a)

def packetBytesActualConsForwardOnlyOmegaSentence {m} (w n t a h p b : Fin m) : Source.Sentence := ((omega w).imp ((PacketBytesTraceSyntax.bytes w n t a).imp ((StructuralListSyntax.consCode w h n p).imp ((PacketAffineAcceptedSyntax.accepted true w h a b).imp ((PacketBytesTraceSyntax.bytes w p t b)))))).close

theorem source_packetBytesActualConsForwardOnlyOmega {m} (w n t a h p b : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetBytesActualConsForwardOnlyOmegaSentence w n t a h p b) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketAffineAcceptedSyntax.accepted true w h a b) (Context.add (StructuralListSyntax.consCode w h n p) (Context.add (PacketBytesTraceSyntax.bytes w n t a) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (PacketBytesTraceSyntax.bytes w n t a) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (StructuralListSyntax.consCode w h n p) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (PacketAffineAcceptedSyntax.accepted true w h a b) := .hyp (Or.inl rfl)
  exact PacketBytesLaws.cons_bytes hZ w n t a h p b h0 h1 h2 h3

theorem packetBytesActualConsForwardOnlyOmega_kernel_certificate {m} (w n t a h p b : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetBytesActualConsForwardOnlyOmegaSentence w n t a h p b)) := TheoryTransport.sentence (source_packetBytesActualConsForwardOnlyOmega w n t a h p b)

theorem native_packetBytesActualConsForwardOnlyOmega {m} (w n t a h p b : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetBytesActualConsForwardOnlyOmegaSentence w n t a h p b)) := ZFReplay.replay (packetBytesActualConsForwardOnlyOmega_kernel_certificate w n t a h p b)

def packetBytesActualSingletonOnlyOmegaSentence {m} (w e n t h a : Fin m) : Source.Sentence := ((omega w).imp ((StructuralListSyntax.nilCode w e).imp ((Formula.mem t w).imp ((StructuralListSyntax.consCode w h e n).imp ((PacketAffineAcceptedSyntax.accepted true w h t a).imp ((PacketBytesTraceSyntax.bytes w n t a))))))).close

theorem source_packetBytesActualSingletonOnlyOmega {m} (w e n t h a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetBytesActualSingletonOnlyOmegaSentence w e n t h a) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketAffineAcceptedSyntax.accepted true w h t a) (Context.add (StructuralListSyntax.consCode w h e n) (Context.add (Formula.mem t w) (Context.add (StructuralListSyntax.nilCode w e) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (StructuralListSyntax.nilCode w e) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (Formula.mem t w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (StructuralListSyntax.consCode w h e n) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (PacketAffineAcceptedSyntax.accepted true w h t a) := .hyp (Or.inl rfl)
  exact PacketBytesLaws.singleton_bytes hZ w e n t h a h0 h1 h2 h3 h4

theorem packetBytesActualSingletonOnlyOmega_kernel_certificate {m} (w e n t h a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetBytesActualSingletonOnlyOmegaSentence w e n t h a)) := TheoryTransport.sentence (source_packetBytesActualSingletonOnlyOmega w e n t h a)

theorem native_packetBytesActualSingletonOnlyOmega {m} (w e n t h a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetBytesActualSingletonOnlyOmegaSentence w e n t h a)) := ZFReplay.replay (packetBytesActualSingletonOnlyOmega_kernel_certificate w e n t h a)

end PPAC.Migration.Internal.ObjectPacketBytesTrace
