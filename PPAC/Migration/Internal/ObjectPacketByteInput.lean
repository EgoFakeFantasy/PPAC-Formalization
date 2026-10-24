import PPAC.Migration.Internal.PacketByteInputLaws

/-! Independent valid-byte input guard from full original Fields graphs and exact all-internal Nil Cons recursion; byte execution totality uniqueness and canonical-byte bridge remain unproved; full Basic AST and varint bridge remain unproved in the original nativeZF kernel; complete schema tests and Con remain unproved. -/
namespace PPAC.Migration.Internal.ObjectPacketByteInput
open Source SourceAlgebra SourceLogic OmegaSyntax

def packetByteInputCompleteFieldsToAllFieldBoundsSentence {m} (w C n l f : Fin m) : Source.Sentence := ((StructuralListFieldGraphSyntax.fields w n l f).imp ((SequenceSyntax.bounded f C).imp ((PacketByteInputSyntax.bounds w C n l)))).close

theorem source_packetByteInputCompleteFieldsToAllFieldBounds {m} (w C n l f : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetByteInputCompleteFieldsToAllFieldBoundsSentence w C n l f) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SequenceSyntax.bounded f C) (Context.add (StructuralListFieldGraphSyntax.fields w n l f) (Source.SetLanguage.ZF.at m))
  have h0 : Derives Δ (StructuralListFieldGraphSyntax.fields w n l f) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SequenceSyntax.bounded f C) := .hyp (Or.inl rfl)
  exact PacketByteInputGraph.graph_to_bounds w C n l f h0 h1

theorem packetByteInputCompleteFieldsToAllFieldBounds_kernel_certificate {m} (w C n l f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetByteInputCompleteFieldsToAllFieldBoundsSentence w C n l f)) := TheoryTransport.sentence (source_packetByteInputCompleteFieldsToAllFieldBounds w C n l f)

theorem native_packetByteInputCompleteFieldsToAllFieldBounds {m} (w C n l f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetByteInputCompleteFieldsToAllFieldBoundsSentence w C n l f)) := ZFReplay.replay (packetByteInputCompleteFieldsToAllFieldBounds_kernel_certificate w C n l f)

def packetByteInputAllFieldBoundsToActualGraphSentence {m} (w C n l f : Fin m) : Source.Sentence := ((StructuralListFieldGraphSyntax.fields w n l f).imp ((PacketByteInputSyntax.bounds w C n l).imp ((SequenceSyntax.bounded f C)))).close

theorem source_packetByteInputAllFieldBoundsToActualGraph {m} (w C n l f : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetByteInputAllFieldBoundsToActualGraphSentence w C n l f) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketByteInputSyntax.bounds w C n l) (Context.add (StructuralListFieldGraphSyntax.fields w n l f) (Source.SetLanguage.ZF.at m))
  have h0 : Derives Δ (StructuralListFieldGraphSyntax.fields w n l f) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PacketByteInputSyntax.bounds w C n l) := .hyp (Or.inl rfl)
  exact PacketByteInputGraph.bounds_to_graph w C n l f h0 h1

theorem packetByteInputAllFieldBoundsToActualGraph_kernel_certificate {m} (w C n l f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetByteInputAllFieldBoundsToActualGraphSentence w C n l f)) := TheoryTransport.sentence (source_packetByteInputAllFieldBoundsToActualGraph w C n l f)

theorem native_packetByteInputAllFieldBoundsToActualGraph {m} (w C n l f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetByteInputAllFieldBoundsToActualGraphSentence w C n l f)) := ZFReplay.replay (packetByteInputAllFieldBoundsToActualGraph_kernel_certificate w C n l f)

def packetByteInputOriginalGraphAndLengthBoundsIffSentence {m} (w C n : Fin m) : Source.Sentence := ((omega w).imp (((PacketByteInputSyntax.inputAt w C n).iff (PacketByteInputSyntax.lengthExists w C n)))).close

theorem source_packetByteInputOriginalGraphAndLengthBoundsIff {m} (w C n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetByteInputOriginalGraphAndLengthBoundsIffSentence w C n) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact PacketByteInputGraph.length_iff hZ w C n h0

theorem packetByteInputOriginalGraphAndLengthBoundsIff_kernel_certificate {m} (w C n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetByteInputOriginalGraphAndLengthBoundsIffSentence w C n)) := TheoryTransport.sentence (source_packetByteInputOriginalGraphAndLengthBoundsIff w C n)

theorem native_packetByteInputOriginalGraphAndLengthBoundsIff {m} (w C n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetByteInputOriginalGraphAndLengthBoundsIffSentence w C n)) := ZFReplay.replay (packetByteInputOriginalGraphAndLengthBoundsIff_kernel_certificate w C n)

def packetByteInputFullConsFieldBoundsForwardSentence {m} (w C r s h t n : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem r w).imp ((successor s r).imp ((Formula.mem h w).imp ((Formula.mem t w).imp ((StructuralListSyntax.consCode w h t n).imp ((PacketByteInputSyntax.bounds w C t r).imp ((Formula.mem h C).imp ((PacketByteInputSyntax.bounds w C n s)))))))))).close

theorem source_packetByteInputFullConsFieldBoundsForward {m} (w C r s h t n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetByteInputFullConsFieldBoundsForwardSentence w C r s h t n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem h C) (Context.add (PacketByteInputSyntax.bounds w C t r) (Context.add (StructuralListSyntax.consCode w h t n) (Context.add (Formula.mem t w) (Context.add (Formula.mem h w) (Context.add (successor s r) (Context.add (Formula.mem r w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))))
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
  have h1 : Derives Δ (Formula.mem r w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h2 : Derives Δ (successor s r) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h3 : Derives Δ (Formula.mem h w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h4 : Derives Δ (Formula.mem t w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h5 : Derives Δ (StructuralListSyntax.consCode w h t n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h6 : Derives Δ (PacketByteInputSyntax.bounds w C t r) := .hyp (Or.inr (Or.inl rfl))
  have h7 : Derives Δ (Formula.mem h C) := .hyp (Or.inl rfl)
  exact PacketByteInputBounds.cons_bounds hZ w C r s h t n h0 h1 h2 h3 h4 h5 h6 h7

theorem packetByteInputFullConsFieldBoundsForward_kernel_certificate {m} (w C r s h t n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetByteInputFullConsFieldBoundsForwardSentence w C r s h t n)) := TheoryTransport.sentence (source_packetByteInputFullConsFieldBoundsForward w C r s h t n)

theorem native_packetByteInputFullConsFieldBoundsForward {m} (w C r s h t n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetByteInputFullConsFieldBoundsForwardSentence w C r s h t n)) := ZFReplay.replay (packetByteInputFullConsFieldBoundsForward_kernel_certificate w C r s h t n)

def packetByteInputFirstActualFieldByteBoundSentence {m} (w C r s h t n : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem r w).imp ((successor s r).imp ((Formula.mem h w).imp ((Formula.mem t w).imp ((StructuralListSyntax.consCode w h t n).imp ((PacketByteInputSyntax.bounds w C n s).imp ((Formula.mem h C))))))))).close

theorem source_packetByteInputFirstActualFieldByteBound {m} (w C r s h t n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetByteInputFirstActualFieldByteBoundSentence w C r s h t n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketByteInputSyntax.bounds w C n s) (Context.add (StructuralListSyntax.consCode w h t n) (Context.add (Formula.mem t w) (Context.add (Formula.mem h w) (Context.add (successor s r) (Context.add (Formula.mem r w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))
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
  have h1 : Derives Δ (Formula.mem r w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h2 : Derives Δ (successor s r) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h3 : Derives Δ (Formula.mem h w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : Derives Δ (Formula.mem t w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h5 : Derives Δ (StructuralListSyntax.consCode w h t n) := .hyp (Or.inr (Or.inl rfl))
  have h6 : Derives Δ (PacketByteInputSyntax.bounds w C n s) := .hyp (Or.inl rfl)
  exact PacketByteInputBounds.head_bound hZ w C r s h t n h0 h1 h2 h3 h4 h5 h6

theorem packetByteInputFirstActualFieldByteBound_kernel_certificate {m} (w C r s h t n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetByteInputFirstActualFieldByteBoundSentence w C r s h t n)) := TheoryTransport.sentence (source_packetByteInputFirstActualFieldByteBound w C r s h t n)

theorem native_packetByteInputFirstActualFieldByteBound {m} (w C r s h t n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetByteInputFirstActualFieldByteBoundSentence w C r s h t n)) := ZFReplay.replay (packetByteInputFirstActualFieldByteBound_kernel_certificate w C r s h t n)

def packetByteInputAllSuccessorFieldsTailBoundsSentence {m} (w C r s h t n : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem r w).imp ((successor s r).imp ((Formula.mem h w).imp ((Formula.mem t w).imp ((StructuralListSyntax.consCode w h t n).imp ((PacketByteInputSyntax.bounds w C n s).imp ((PacketByteInputSyntax.bounds w C t r))))))))).close

theorem source_packetByteInputAllSuccessorFieldsTailBounds {m} (w C r s h t n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetByteInputAllSuccessorFieldsTailBoundsSentence w C r s h t n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketByteInputSyntax.bounds w C n s) (Context.add (StructuralListSyntax.consCode w h t n) (Context.add (Formula.mem t w) (Context.add (Formula.mem h w) (Context.add (successor s r) (Context.add (Formula.mem r w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))
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
  have h1 : Derives Δ (Formula.mem r w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h2 : Derives Δ (successor s r) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h3 : Derives Δ (Formula.mem h w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : Derives Δ (Formula.mem t w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h5 : Derives Δ (StructuralListSyntax.consCode w h t n) := .hyp (Or.inr (Or.inl rfl))
  have h6 : Derives Δ (PacketByteInputSyntax.bounds w C n s) := .hyp (Or.inl rfl)
  exact PacketByteInputBounds.tail_bounds hZ w C r s h t n h0 h1 h2 h3 h4 h5 h6

theorem packetByteInputAllSuccessorFieldsTailBounds_kernel_certificate {m} (w C r s h t n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetByteInputAllSuccessorFieldsTailBoundsSentence w C r s h t n)) := TheoryTransport.sentence (source_packetByteInputAllSuccessorFieldsTailBounds w C r s h t n)

theorem native_packetByteInputAllSuccessorFieldsTailBounds {m} (w C r s h t n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetByteInputAllSuccessorFieldsTailBoundsSentence w C r s h t n)) := ZFReplay.replay (packetByteInputAllSuccessorFieldsTailBounds_kernel_certificate w C r s h t n)

def packetByteInputBoundsAtAnyActualLengthSentence {m} (w C n l : Fin m) : Source.Sentence := ((omega w).imp ((PacketByteInputSyntax.inputAt w C n).imp ((StructuralListLengthSyntax.hasLength w n l).imp ((PacketByteInputSyntax.bounds w C n l))))).close

theorem source_packetByteInputBoundsAtAnyActualLength {m} (w C n l : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetByteInputBoundsAtAnyActualLengthSentence w C n l) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralListLengthSyntax.hasLength w n l) (Context.add (PacketByteInputSyntax.inputAt w C n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (PacketByteInputSyntax.inputAt w C n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (StructuralListLengthSyntax.hasLength w n l) := .hyp (Or.inl rfl)
  exact PacketByteInputProperties.at_length hZ w C n l h0 h1 h2

theorem packetByteInputBoundsAtAnyActualLength_kernel_certificate {m} (w C n l : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetByteInputBoundsAtAnyActualLengthSentence w C n l)) := TheoryTransport.sentence (source_packetByteInputBoundsAtAnyActualLength w C n l)

theorem native_packetByteInputBoundsAtAnyActualLength {m} (w C n l : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetByteInputBoundsAtAnyActualLengthSentence w C n l)) := ZFReplay.replay (packetByteInputBoundsAtAnyActualLength_kernel_certificate w C n l)

def packetByteInputNilGuardConstructedSentence {m} (w C n : Fin m) : Source.Sentence := ((omega w).imp ((StructuralListSyntax.nilCode w n).imp ((PacketByteInputSyntax.inputAt w C n)))).close

theorem source_packetByteInputNilGuardConstructed {m} (w C n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetByteInputNilGuardConstructedSentence w C n) := by
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
  exact PacketByteInputProperties.nil_input hZ w C n h0 h1

theorem packetByteInputNilGuardConstructed_kernel_certificate {m} (w C n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetByteInputNilGuardConstructedSentence w C n)) := TheoryTransport.sentence (source_packetByteInputNilGuardConstructed w C n)

theorem native_packetByteInputNilGuardConstructed {m} (w C n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetByteInputNilGuardConstructedSentence w C n)) := ZFReplay.replay (packetByteInputNilGuardConstructed_kernel_certificate w C n)

def packetByteInputFullConsGuardConstructedSentence {m} (w C h t n : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem C w).imp ((Formula.mem h C).imp ((PacketByteInputSyntax.inputAt w C t).imp ((StructuralListSyntax.consCode w h t n).imp ((PacketByteInputSyntax.inputAt w C n))))))).close

theorem source_packetByteInputFullConsGuardConstructed {m} (w C h t n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetByteInputFullConsGuardConstructedSentence w C h t n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralListSyntax.consCode w h t n) (Context.add (PacketByteInputSyntax.inputAt w C t) (Context.add (Formula.mem h C) (Context.add (Formula.mem C w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (Formula.mem C w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (Formula.mem h C) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (PacketByteInputSyntax.inputAt w C t) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (StructuralListSyntax.consCode w h t n) := .hyp (Or.inl rfl)
  exact PacketByteInputProperties.cons_input hZ w C h t n h0 h1 h2 h3 h4

theorem packetByteInputFullConsGuardConstructed_kernel_certificate {m} (w C h t n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetByteInputFullConsGuardConstructedSentence w C h t n)) := TheoryTransport.sentence (source_packetByteInputFullConsGuardConstructed w C h t n)

theorem native_packetByteInputFullConsGuardConstructed {m} (w C h t n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetByteInputFullConsGuardConstructedSentence w C h t n)) := ZFReplay.replay (packetByteInputFullConsGuardConstructed_kernel_certificate w C h t n)

def packetByteInputTypedConsHeadAndTailRecoveredSentence {m} (w C h t n : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem h w).imp ((Formula.mem t w).imp ((StructuralListSyntax.consCode w h t n).imp ((PacketByteInputSyntax.inputAt w C n).imp (((Formula.mem h C).conj (PacketByteInputSyntax.inputAt w C t)))))))).close

theorem source_packetByteInputTypedConsHeadAndTailRecovered {m} (w C h t n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetByteInputTypedConsHeadAndTailRecoveredSentence w C h t n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketByteInputSyntax.inputAt w C n) (Context.add (StructuralListSyntax.consCode w h t n) (Context.add (Formula.mem t w) (Context.add (Formula.mem h w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (Formula.mem h w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (Formula.mem t w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (StructuralListSyntax.consCode w h t n) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (PacketByteInputSyntax.inputAt w C n) := .hyp (Or.inl rfl)
  exact PacketByteInputProperties.typed_cons_inverse hZ w C h t n h0 h1 h2 h3 h4

theorem packetByteInputTypedConsHeadAndTailRecovered_kernel_certificate {m} (w C h t n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetByteInputTypedConsHeadAndTailRecoveredSentence w C h t n)) := TheoryTransport.sentence (source_packetByteInputTypedConsHeadAndTailRecovered w C h t n)

theorem native_packetByteInputTypedConsHeadAndTailRecovered {m} (w C h t n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetByteInputTypedConsHeadAndTailRecoveredSentence w C h t n)) := ZFReplay.replay (packetByteInputTypedConsHeadAndTailRecovered_kernel_certificate w C h t n)

def packetByteInputAllInternalRadixGuardRecursionSentence {m} (w C n : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem C w).imp (((PacketByteInputSyntax.inputAt w C n).iff (PacketByteInputRecursionSyntax.criterionAt w C n))))).close

theorem source_packetByteInputAllInternalRadixGuardRecursion {m} (w C n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetByteInputAllInternalRadixGuardRecursionSentence w C n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem C w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (Formula.mem C w) := .hyp (Or.inl rfl)
  exact PacketByteInputDecomposition.input_iff hZ w C n h0 h1

theorem packetByteInputAllInternalRadixGuardRecursion_kernel_certificate {m} (w C n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetByteInputAllInternalRadixGuardRecursionSentence w C n)) := TheoryTransport.sentence (source_packetByteInputAllInternalRadixGuardRecursion w C n)

theorem native_packetByteInputAllInternalRadixGuardRecursion {m} (w C n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetByteInputAllInternalRadixGuardRecursionSentence w C n)) := ZFReplay.replay (packetByteInputAllInternalRadixGuardRecursion_kernel_certificate w C n)

def packetByteInputActual256ExactGuardIffSentence {m} (w C n : Fin m) : Source.Sentence := ((SyntaxNumeralSyntax.numeral 256 C).imp (((PacketByteInputSyntax.byteList w n).iff (PacketByteInputSyntax.inputAt w C n)))).close

theorem source_packetByteInputActual256ExactGuardIff {m} (w C n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetByteInputActual256ExactGuardIffSentence w C n) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNumeralSyntax.numeral 256 C) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (SyntaxNumeralSyntax.numeral 256 C) := .hyp (Or.inl rfl)
  exact PacketByteInputBridge.actual_iff_at hZ w C n h0

theorem packetByteInputActual256ExactGuardIff_kernel_certificate {m} (w C n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetByteInputActual256ExactGuardIffSentence w C n)) := TheoryTransport.sentence (source_packetByteInputActual256ExactGuardIff w C n)

theorem native_packetByteInputActual256ExactGuardIff {m} (w C n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetByteInputActual256ExactGuardIffSentence w C n)) := ZFReplay.replay (packetByteInputActual256ExactGuardIff_kernel_certificate w C n)

def packetByteInputActualByteNaturalOnlyOmegaSentence {m} (w h : Fin m) : Source.Sentence := ((omega w).imp ((PacketByteInputSyntax.byte h).imp ((Formula.mem h w)))).close

theorem source_packetByteInputActualByteNaturalOnlyOmega {m} (w h : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetByteInputActualByteNaturalOnlyOmegaSentence w h) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketByteInputSyntax.byte h) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PacketByteInputSyntax.byte h) := .hyp (Or.inl rfl)
  exact PacketByteInputLaws.byte_natural hZ w h h0 h1

theorem packetByteInputActualByteNaturalOnlyOmega_kernel_certificate {m} (w h : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetByteInputActualByteNaturalOnlyOmegaSentence w h)) := TheoryTransport.sentence (source_packetByteInputActualByteNaturalOnlyOmega w h)

theorem native_packetByteInputActualByteNaturalOnlyOmega {m} (w h : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetByteInputActualByteNaturalOnlyOmegaSentence w h)) := ZFReplay.replay (packetByteInputActualByteNaturalOnlyOmega_kernel_certificate w h)

def packetByteInputActualGuardImpliesOriginalListValiditySentence {m} (w n : Fin m) : Source.Sentence := ((PacketByteInputSyntax.byteList w n).imp ((StructuralListTraceSyntax.valid w n))).close

theorem source_packetByteInputActualGuardImpliesOriginalListValidity {m} (w n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetByteInputActualGuardImpliesOriginalListValiditySentence w n) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (PacketByteInputSyntax.byteList w n) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (PacketByteInputSyntax.byteList w n) := .hyp (Or.inl rfl)
  exact PacketByteInputLaws.valid w n h0

theorem packetByteInputActualGuardImpliesOriginalListValidity_kernel_certificate {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetByteInputActualGuardImpliesOriginalListValiditySentence w n)) := TheoryTransport.sentence (source_packetByteInputActualGuardImpliesOriginalListValidity w n)

theorem native_packetByteInputActualGuardImpliesOriginalListValidity {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetByteInputActualGuardImpliesOriginalListValiditySentence w n)) := ZFReplay.replay (packetByteInputActualGuardImpliesOriginalListValidity_kernel_certificate w n)

def packetByteInputActualGuardExactRecursionOnlyOmegaSentence {m} (w n : Fin m) : Source.Sentence := ((omega w).imp (((PacketByteInputSyntax.byteList w n).iff (PacketByteInputRecursionSyntax.criterion w n)))).close

theorem source_packetByteInputActualGuardExactRecursionOnlyOmega {m} (w n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetByteInputActualGuardExactRecursionOnlyOmegaSentence w n) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact PacketByteInputLaws.actual_iff hZ w n h0

theorem packetByteInputActualGuardExactRecursionOnlyOmega_kernel_certificate {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetByteInputActualGuardExactRecursionOnlyOmegaSentence w n)) := TheoryTransport.sentence (source_packetByteInputActualGuardExactRecursionOnlyOmega w n)

theorem native_packetByteInputActualGuardExactRecursionOnlyOmega {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetByteInputActualGuardExactRecursionOnlyOmegaSentence w n)) := ZFReplay.replay (packetByteInputActualGuardExactRecursionOnlyOmega_kernel_certificate w n)

def packetByteInputAllInternalActualGuardOnlyOmegaSentence {m} (w : Fin m) : Source.Sentence := ((omega w).imp ((PacketByteInputLaws.allLaw w))).close

theorem source_packetByteInputAllInternalActualGuardOnlyOmega {m} (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetByteInputAllInternalActualGuardOnlyOmegaSentence w) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact PacketByteInputLaws.all_law hZ w h0

theorem packetByteInputAllInternalActualGuardOnlyOmega_kernel_certificate {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetByteInputAllInternalActualGuardOnlyOmegaSentence w)) := TheoryTransport.sentence (source_packetByteInputAllInternalActualGuardOnlyOmega w)

theorem native_packetByteInputAllInternalActualGuardOnlyOmega {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetByteInputAllInternalActualGuardOnlyOmegaSentence w)) := ZFReplay.replay (packetByteInputAllInternalActualGuardOnlyOmega_kernel_certificate w)

end PPAC.Migration.Internal.ObjectPacketByteInput
