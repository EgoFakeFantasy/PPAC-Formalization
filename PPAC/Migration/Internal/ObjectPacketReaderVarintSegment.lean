import PPAC.Migration.Internal.PacketReaderVarintConsumption

/-! Every internal canonical varint consumes exactly one actual whole segment with arbitrary tail, value, scale and accumulator; actual splice exists uniquely and every output candidate is covered. Multi-token/inverse/full program specification bridge, Basic AST, Proof and Con remain unproved -/
namespace PPAC.Migration.Internal.ObjectPacketReaderVarintSegment
open Source SourceAlgebra SourceLogic OmegaSyntax

def varintSegmentSpliceExactNilSentence {m} (w C T L : Fin m) : Source.Sentence := ((omega w).imp ((StructuralListSyntax.nilCode w C).imp (((StructuralListSpliceSyntax.splice w C T L).iff ((StructuralListTraceSyntax.valid w T).conj (Formula.equal T L)))))).close

theorem source_varintSegmentSpliceExactNil {m} (w C T L : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (varintSegmentSpliceExactNilSentence w C T L) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralListSyntax.nilCode w C) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (StructuralListSyntax.nilCode w C) := .hyp (Or.inl rfl)
  exact StructuralListSplice.nil_iff hZ w C T L h0 h1

theorem varintSegmentSpliceExactNil_kernel_certificate {m} (w C T L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (varintSegmentSpliceExactNilSentence w C T L)) := TheoryTransport.sentence (source_varintSegmentSpliceExactNil w C T L)

theorem native_varintSegmentSpliceExactNil {m} (w C T L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (varintSegmentSpliceExactNilSentence w C T L)) := ZFReplay.replay (varintSegmentSpliceExactNil_kernel_certificate w C T L)

def varintSegmentSpliceExactConsSentence {m} (w h X C T L : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem h w).imp ((Formula.mem X w).imp ((StructuralListSyntax.consCode w h X C).imp (((StructuralListSpliceSyntax.splice w C T L).iff (StructuralListSplice.remaining w h X T L))))))).close

theorem source_varintSegmentSpliceExactCons {m} (w h X C T L : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (varintSegmentSpliceExactConsSentence w h X C T L) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralListSyntax.consCode w h X C) (Context.add (Formula.mem X w) (Context.add (Formula.mem h w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (Formula.mem h w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (Formula.mem X w) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (StructuralListSyntax.consCode w h X C) := .hyp (Or.inl rfl)
  exact StructuralListSplice.cons_iff hZ w h X C T L h0 h1 h2 h3

theorem varintSegmentSpliceExactCons_kernel_certificate {m} (w h X C T L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (varintSegmentSpliceExactConsSentence w h X C T L)) := TheoryTransport.sentence (source_varintSegmentSpliceExactCons w h X C T L)

theorem native_varintSegmentSpliceExactCons {m} (w h X C T L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (varintSegmentSpliceExactConsSentence w h X C T L)) := ZFReplay.replay (varintSegmentSpliceExactCons_kernel_certificate w h X C T L)

def varintSegmentSpliceRequiresActualTailSentence {m} (w C T L : Fin m) : Source.Sentence := ((StructuralListSpliceSyntax.splice w C T L).imp ((StructuralListTraceSyntax.valid w T))).close

theorem source_varintSegmentSpliceRequiresActualTail {m} (w C T L : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (varintSegmentSpliceRequiresActualTailSentence w C T L) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralListSpliceSyntax.splice w C T L) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (StructuralListSpliceSyntax.splice w C T L) := .hyp (Or.inl rfl)
  exact StructuralListSplice.tail_valid w C T L h0

theorem varintSegmentSpliceRequiresActualTail_kernel_certificate {m} (w C T L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (varintSegmentSpliceRequiresActualTailSentence w C T L)) := TheoryTransport.sentence (source_varintSegmentSpliceRequiresActualTail w C T L)

theorem native_varintSegmentSpliceRequiresActualTail {m} (w C T L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (varintSegmentSpliceRequiresActualTailSentence w C T L)) := ZFReplay.replay (varintSegmentSpliceRequiresActualTail_kernel_certificate w C T L)

def varintSegmentSpliceRequiresActualJoinedListSentence {m} (w C T L : Fin m) : Source.Sentence := ((StructuralListSpliceSyntax.splice w C T L).imp ((StructuralListTraceSyntax.valid w L))).close

theorem source_varintSegmentSpliceRequiresActualJoinedList {m} (w C T L : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (varintSegmentSpliceRequiresActualJoinedListSentence w C T L) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralListSpliceSyntax.splice w C T L) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (StructuralListSpliceSyntax.splice w C T L) := .hyp (Or.inl rfl)
  exact StructuralListSplice.joined_valid w C T L h0

theorem varintSegmentSpliceRequiresActualJoinedList_kernel_certificate {m} (w C T L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (varintSegmentSpliceRequiresActualJoinedListSentence w C T L)) := TheoryTransport.sentence (source_varintSegmentSpliceRequiresActualJoinedList w C T L)

theorem native_varintSegmentSpliceRequiresActualJoinedList {m} (w C T L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (varintSegmentSpliceRequiresActualJoinedListSentence w C T L)) := ZFReplay.replay (varintSegmentSpliceRequiresActualJoinedList_kernel_certificate w C T L)

def varintSegmentSpliceRequiresActualPrefixSentence {m} (w C T L : Fin m) : Source.Sentence := ((StructuralListSpliceSyntax.splice w C T L).imp ((StructuralListTraceSyntax.valid w C))).close

theorem source_varintSegmentSpliceRequiresActualPrefix {m} (w C T L : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (varintSegmentSpliceRequiresActualPrefixSentence w C T L) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralListSpliceSyntax.splice w C T L) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (StructuralListSpliceSyntax.splice w C T L) := .hyp (Or.inl rfl)
  exact StructuralListSplice.prefix_valid w C T L h0

theorem varintSegmentSpliceRequiresActualPrefix_kernel_certificate {m} (w C T L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (varintSegmentSpliceRequiresActualPrefixSentence w C T L)) := TheoryTransport.sentence (source_varintSegmentSpliceRequiresActualPrefix w C T L)

theorem native_varintSegmentSpliceRequiresActualPrefix {m} (w C T L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (varintSegmentSpliceRequiresActualPrefixSentence w C T L)) := ZFReplay.replay (varintSegmentSpliceRequiresActualPrefix_kernel_certificate w C T L)

def varintSegmentEveryTwoInternalListsHaveUniqueSpliceSentence {m} (w C T : Fin m) : Source.Sentence := ((omega w).imp ((StructuralListTraceSyntax.valid w C).imp ((StructuralListTraceSyntax.valid w T).imp ((StructuralListSpliceTotalSyntax.fiber w C T))))).close

theorem source_varintSegmentEveryTwoInternalListsHaveUniqueSplice {m} (w C T : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (varintSegmentEveryTwoInternalListsHaveUniqueSpliceSentence w C T) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralListTraceSyntax.valid w T) (Context.add (StructuralListTraceSyntax.valid w C) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (StructuralListTraceSyntax.valid w C) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (StructuralListTraceSyntax.valid w T) := .hyp (Or.inl rfl)
  exact StructuralListSpliceTotal.exists_unique hZ w C T h0 h1 h2

theorem varintSegmentEveryTwoInternalListsHaveUniqueSplice_kernel_certificate {m} (w C T : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (varintSegmentEveryTwoInternalListsHaveUniqueSpliceSentence w C T)) := TheoryTransport.sentence (source_varintSegmentEveryTwoInternalListsHaveUniqueSplice w C T)

theorem native_varintSegmentEveryTwoInternalListsHaveUniqueSplice {m} (w C T : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (varintSegmentEveryTwoInternalListsHaveUniqueSpliceSentence w C T)) := ZFReplay.replay (varintSegmentEveryTwoInternalListsHaveUniqueSplice_kernel_certificate w C T)

def varintSegmentSpliceAllCandidateOutputsUniqueSentence {m} (w C T L M : Fin m) : Source.Sentence := ((omega w).imp ((StructuralListSpliceSyntax.splice w C T L).imp ((StructuralListSpliceSyntax.splice w C T M).imp ((Formula.equal L M))))).close

theorem source_varintSegmentSpliceAllCandidateOutputsUnique {m} (w C T L M : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (varintSegmentSpliceAllCandidateOutputsUniqueSentence w C T L M) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralListSpliceSyntax.splice w C T M) (Context.add (StructuralListSpliceSyntax.splice w C T L) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (StructuralListSpliceSyntax.splice w C T L) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (StructuralListSpliceSyntax.splice w C T M) := .hyp (Or.inl rfl)
  exact StructuralListSpliceTotal.unique hZ w C T L M h0 h1 h2

theorem varintSegmentSpliceAllCandidateOutputsUnique_kernel_certificate {m} (w C T L M : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (varintSegmentSpliceAllCandidateOutputsUniqueSentence w C T L M)) := TheoryTransport.sentence (source_varintSegmentSpliceAllCandidateOutputsUnique w C T L M)

theorem native_varintSegmentSpliceAllCandidateOutputsUnique {m} (w C T L M : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (varintSegmentSpliceAllCandidateOutputsUniqueSentence w C T L M)) := ZFReplay.replay (varintSegmentSpliceAllCandidateOutputsUnique_kernel_certificate w C T L M)

def varintSegmentSpliceOutputIsNaturalSentence {m} (w C T L : Fin m) : Source.Sentence := ((StructuralListSpliceSyntax.splice w C T L).imp ((Formula.mem L w))).close

theorem source_varintSegmentSpliceOutputIsNatural {m} (w C T L : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (varintSegmentSpliceOutputIsNaturalSentence w C T L) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralListSpliceSyntax.splice w C T L) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (StructuralListSpliceSyntax.splice w C T L) := .hyp (Or.inl rfl)
  exact StructuralListSpliceTotal.natural w C T L h0

theorem varintSegmentSpliceOutputIsNatural_kernel_certificate {m} (w C T L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (varintSegmentSpliceOutputIsNaturalSentence w C T L)) := TheoryTransport.sentence (source_varintSegmentSpliceOutputIsNatural w C T L)

theorem native_varintSegmentSpliceOutputIsNatural {m} (w C T L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (varintSegmentSpliceOutputIsNaturalSentence w C T L)) := ZFReplay.replay (varintSegmentSpliceOutputIsNatural_kernel_certificate w C T L)

def varintSegmentFullContinuationArithmeticComposeSentence {m} (w B d k n v s v1 s1 u : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem B w).imp ((Formula.mem d w).imp ((Formula.mem k w).imp ((Formula.mem v w).imp ((Formula.mem s w).imp ((PacketAffineSyntax.equation w B d k n).imp ((PacketAffineSyntax.equation w d v s v1).imp ((NaturalMultiplicationSyntax.product w s B s1).imp ((PacketAffineSyntax.equation w k v1 s1 u).imp ((PacketAffineSyntax.equation w n v s u)))))))))))).close

theorem source_varintSegmentFullContinuationArithmeticCompose {m} (w B d k n v s v1 s1 u : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (varintSegmentFullContinuationArithmeticComposeSentence w B d k n v s v1 s1 u) := by
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
  let Δ : Context m := Context.add (PacketAffineSyntax.equation w k v1 s1 u) (Context.add (NaturalMultiplicationSyntax.product w s B s1) (Context.add (PacketAffineSyntax.equation w d v s v1) (Context.add (PacketAffineSyntax.equation w B d k n) (Context.add (Formula.mem s w) (Context.add (Formula.mem v w) (Context.add (Formula.mem k w) (Context.add (Formula.mem d w) (Context.add (Formula.mem B w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))))))
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
  have h2 : Derives Δ (Formula.mem d w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  have h3 : Derives Δ (Formula.mem k w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h4 : Derives Δ (Formula.mem v w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h5 : Derives Δ (Formula.mem s w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h6 : Derives Δ (PacketAffineSyntax.equation w B d k n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h7 : Derives Δ (PacketAffineSyntax.equation w d v s v1) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h8 : Derives Δ (NaturalMultiplicationSyntax.product w s B s1) := .hyp (Or.inr (Or.inl rfl))
  have h9 : Derives Δ (PacketAffineSyntax.equation w k v1 s1 u) := .hyp (Or.inl rfl)
  exact PacketReaderAffineCompose.compose hZ w B d k n v s v1 s1 u h0 h1 h2 h3 h4 h5 h6 h7 h8 h9

theorem varintSegmentFullContinuationArithmeticCompose_kernel_certificate {m} (w B d k n v s v1 s1 u : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (varintSegmentFullContinuationArithmeticComposeSentence w B d k n v s v1 s1 u)) := TheoryTransport.sentence (source_varintSegmentFullContinuationArithmeticCompose w B d k n v s v1 s1 u)

theorem native_varintSegmentFullContinuationArithmeticCompose {m} (w B d k n v s v1 s1 u : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (varintSegmentFullContinuationArithmeticComposeSentence w B d k n v s v1 s1 u)) := ZFReplay.replay (varintSegmentFullContinuationArithmeticCompose_kernel_certificate w B d k n v s v1 s1 u)

def varintSegmentFullContinuationArithmeticDecomposeSentence {m} (w B d k n v s v1 s1 u : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem B w).imp ((Formula.mem d w).imp ((Formula.mem k w).imp ((Formula.mem v w).imp ((Formula.mem s w).imp ((PacketAffineSyntax.equation w B d k n).imp ((PacketAffineSyntax.equation w d v s v1).imp ((NaturalMultiplicationSyntax.product w s B s1).imp ((PacketAffineSyntax.equation w n v s u).imp ((PacketAffineSyntax.equation w k v1 s1 u)))))))))))).close

theorem source_varintSegmentFullContinuationArithmeticDecompose {m} (w B d k n v s v1 s1 u : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (varintSegmentFullContinuationArithmeticDecomposeSentence w B d k n v s v1 s1 u) := by
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
  let Δ : Context m := Context.add (PacketAffineSyntax.equation w n v s u) (Context.add (NaturalMultiplicationSyntax.product w s B s1) (Context.add (PacketAffineSyntax.equation w d v s v1) (Context.add (PacketAffineSyntax.equation w B d k n) (Context.add (Formula.mem s w) (Context.add (Formula.mem v w) (Context.add (Formula.mem k w) (Context.add (Formula.mem d w) (Context.add (Formula.mem B w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))))))
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
  have h2 : Derives Δ (Formula.mem d w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  have h3 : Derives Δ (Formula.mem k w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h4 : Derives Δ (Formula.mem v w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h5 : Derives Δ (Formula.mem s w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h6 : Derives Δ (PacketAffineSyntax.equation w B d k n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h7 : Derives Δ (PacketAffineSyntax.equation w d v s v1) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h8 : Derives Δ (NaturalMultiplicationSyntax.product w s B s1) := .hyp (Or.inr (Or.inl rfl))
  have h9 : Derives Δ (PacketAffineSyntax.equation w n v s u) := .hyp (Or.inl rfl)
  exact PacketReaderAffineCompose.decompose hZ w B d k n v s v1 s1 u h0 h1 h2 h3 h4 h5 h6 h7 h8 h9

theorem varintSegmentFullContinuationArithmeticDecompose_kernel_certificate {m} (w B d k n v s v1 s1 u : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (varintSegmentFullContinuationArithmeticDecomposeSentence w B d k n v s v1 s1 u)) := TheoryTransport.sentence (source_varintSegmentFullContinuationArithmeticDecompose w B d k n v s v1 s1 u)

theorem native_varintSegmentFullContinuationArithmeticDecompose {m} (w B d k n v s v1 s1 u : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (varintSegmentFullContinuationArithmeticDecomposeSentence w B d k n v s v1 s1 u)) := ZFReplay.replay (varintSegmentFullContinuationArithmeticDecompose_kernel_certificate w B d k n v s v1 s1 u)

def varintSegmentFullContinuationArithmeticExactSentence {m} (w B d k n v s v1 s1 u : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem B w).imp ((Formula.mem d w).imp ((Formula.mem k w).imp ((Formula.mem v w).imp ((Formula.mem s w).imp ((PacketAffineSyntax.equation w B d k n).imp ((PacketAffineSyntax.equation w d v s v1).imp ((NaturalMultiplicationSyntax.product w s B s1).imp (((PacketAffineSyntax.equation w n v s u).iff (PacketAffineSyntax.equation w k v1 s1 u)))))))))))).close

theorem source_varintSegmentFullContinuationArithmeticExact {m} (w B d k n v s v1 s1 u : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (varintSegmentFullContinuationArithmeticExactSentence w B d k n v s v1 s1 u) := by
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
  let Δ : Context m := Context.add (NaturalMultiplicationSyntax.product w s B s1) (Context.add (PacketAffineSyntax.equation w d v s v1) (Context.add (PacketAffineSyntax.equation w B d k n) (Context.add (Formula.mem s w) (Context.add (Formula.mem v w) (Context.add (Formula.mem k w) (Context.add (Formula.mem d w) (Context.add (Formula.mem B w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))))
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
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))
  have h1 : Derives Δ (Formula.mem B w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  have h2 : Derives Δ (Formula.mem d w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h3 : Derives Δ (Formula.mem k w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h4 : Derives Δ (Formula.mem v w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h5 : Derives Δ (Formula.mem s w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h6 : Derives Δ (PacketAffineSyntax.equation w B d k n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h7 : Derives Δ (PacketAffineSyntax.equation w d v s v1) := .hyp (Or.inr (Or.inl rfl))
  have h8 : Derives Δ (NaturalMultiplicationSyntax.product w s B s1) := .hyp (Or.inl rfl)
  exact PacketReaderAffineCompose.exact_iff hZ w B d k n v s v1 s1 u h0 h1 h2 h3 h4 h5 h6 h7 h8

theorem varintSegmentFullContinuationArithmeticExact_kernel_certificate {m} (w B d k n v s v1 s1 u : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (varintSegmentFullContinuationArithmeticExactSentence w B d k n v s v1 s1 u)) := TheoryTransport.sentence (source_varintSegmentFullContinuationArithmeticExact w B d k n v s v1 s1 u)

theorem native_varintSegmentFullContinuationArithmeticExact {m} (w B d k n v s v1 s1 u : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (varintSegmentFullContinuationArithmeticExactSentence w B d k n v s v1 s1 u)) := ZFReplay.replay (varintSegmentFullContinuationArithmeticExact_kernel_certificate w B d k n v s v1 s1 u)

def varintSegmentActualTerminalDigitEvaluationSentence {m} (w B z o L b T v s a u c p : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem B w).imp ((empty z).imp ((Formula.mem o w).imp ((PacketReaderStepSyntax.state w T v s a).imp ((PacketReaderInputSyntax.headRest w L b T).imp ((Formula.mem b B).imp (((Formula.equal s o).disj (empty b).neg).imp ((PacketAffineSyntax.equation w b v s u).imp ((StructuralListSyntax.consCode w u a c).imp (((PacketReaderEvalSyntax.eval w B z o L v s a p).iff (PacketReaderEvalSyntax.eval w B z o T z o c p))))))))))))).close

theorem source_varintSegmentActualTerminalDigitEvaluation {m} (w B z o L b T v s a u c p : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (varintSegmentActualTerminalDigitEvaluationSentence w B z o L b T v s a u c p) := by
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
  let Δ : Context m := Context.add (StructuralListSyntax.consCode w u a c) (Context.add (PacketAffineSyntax.equation w b v s u) (Context.add ((Formula.equal s o).disj (empty b).neg) (Context.add (Formula.mem b B) (Context.add (PacketReaderInputSyntax.headRest w L b T) (Context.add (PacketReaderStepSyntax.state w T v s a) (Context.add (Formula.mem o w) (Context.add (empty z) (Context.add (Formula.mem B w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))))))
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
  have h2 : Derives Δ (empty z) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  have h3 : Derives Δ (Formula.mem o w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h4 : Derives Δ (PacketReaderStepSyntax.state w T v s a) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h5 : Derives Δ (PacketReaderInputSyntax.headRest w L b T) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h6 : Derives Δ (Formula.mem b B) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h7 : Derives Δ ((Formula.equal s o).disj (empty b).neg) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h8 : Derives Δ (PacketAffineSyntax.equation w b v s u) := .hyp (Or.inr (Or.inl rfl))
  have h9 : Derives Δ (StructuralListSyntax.consCode w u a c) := .hyp (Or.inl rfl)
  exact PacketReaderVarintBranches.terminal_digit hZ w B z o L b T v s a u c p h0 h1 h2 h3 h4 h5 h6 h7 h8 h9

theorem varintSegmentActualTerminalDigitEvaluation_kernel_certificate {m} (w B z o L b T v s a u c p : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (varintSegmentActualTerminalDigitEvaluationSentence w B z o L b T v s a u c p)) := TheoryTransport.sentence (source_varintSegmentActualTerminalDigitEvaluation w B z o L b T v s a u c p)

theorem native_varintSegmentActualTerminalDigitEvaluation {m} (w B z o L b T v s a u c p : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (varintSegmentActualTerminalDigitEvaluationSentence w B z o L b T v s a u c p)) := ZFReplay.replay (varintSegmentActualTerminalDigitEvaluation_kernel_certificate w B z o L b T v s a u c p)

def varintSegmentActualContinuationDigitEvaluationSentence {m} (w B z o L b T v s a d y S p : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem B w).imp ((empty z).imp ((Formula.mem o w).imp ((PacketReaderStepSyntax.state w T v s a).imp ((PacketReaderInputSyntax.headRest w L b T).imp ((Formula.mem d w).imp ((NaturalAdditionSyntax.sum w d B b).imp ((PacketAffineSyntax.equation w d v s y).imp ((NaturalMultiplicationSyntax.product w s B S).imp (((PacketReaderEvalSyntax.eval w B z o L v s a p).iff (PacketReaderEvalSyntax.eval w B z o T y S a p))))))))))))).close

theorem source_varintSegmentActualContinuationDigitEvaluation {m} (w B z o L b T v s a d y S p : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (varintSegmentActualContinuationDigitEvaluationSentence w B z o L b T v s a d y S p) := by
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
  let Δ : Context m := Context.add (NaturalMultiplicationSyntax.product w s B S) (Context.add (PacketAffineSyntax.equation w d v s y) (Context.add (NaturalAdditionSyntax.sum w d B b) (Context.add (Formula.mem d w) (Context.add (PacketReaderInputSyntax.headRest w L b T) (Context.add (PacketReaderStepSyntax.state w T v s a) (Context.add (Formula.mem o w) (Context.add (empty z) (Context.add (Formula.mem B w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))))))
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
  have h2 : Derives Δ (empty z) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  have h3 : Derives Δ (Formula.mem o w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h4 : Derives Δ (PacketReaderStepSyntax.state w T v s a) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h5 : Derives Δ (PacketReaderInputSyntax.headRest w L b T) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h6 : Derives Δ (Formula.mem d w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h7 : Derives Δ (NaturalAdditionSyntax.sum w d B b) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h8 : Derives Δ (PacketAffineSyntax.equation w d v s y) := .hyp (Or.inr (Or.inl rfl))
  have h9 : Derives Δ (NaturalMultiplicationSyntax.product w s B S) := .hyp (Or.inl rfl)
  exact PacketReaderVarintBranches.continuation_digit hZ w B z o L b T v s a d y S p h0 h1 h2 h3 h4 h5 h6 h7 h8 h9

theorem varintSegmentActualContinuationDigitEvaluation_kernel_certificate {m} (w B z o L b T v s a d y S p : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (varintSegmentActualContinuationDigitEvaluationSentence w B z o L b T v s a d y S p)) := TheoryTransport.sentence (source_varintSegmentActualContinuationDigitEvaluation w B z o L b T v s a d y S p)

theorem native_varintSegmentActualContinuationDigitEvaluation {m} (w B z o L b T v s a d y S p : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (varintSegmentActualContinuationDigitEvaluationSentence w B z o L b T v s a d y S p)) := ZFReplay.replay (varintSegmentActualContinuationDigitEvaluation_kernel_certificate w B z o L b T v s a d y S p)

def varintSegmentAllInternalTokenSegmentPropertiesSentence {m} (w B z o : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 128 B).imp ((empty z).imp ((Formula.mem o w).imp ((PacketReaderVarintSegmentSyntax.allProperties w B z o)))))).close

theorem source_varintSegmentAllInternalTokenSegmentProperties {m} (w B z o : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (varintSegmentAllInternalTokenSegmentPropertiesSentence w B z o) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem o w) (Context.add (empty z) (Context.add (SyntaxNumeralSyntax.numeral 128 B) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 128 B) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (empty z) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (Formula.mem o w) := .hyp (Or.inl rfl)
  exact PacketReaderVarintSegmentInduction.all_properties hZ w B z o h0 h1 h2 h3

theorem varintSegmentAllInternalTokenSegmentProperties_kernel_certificate {m} (w B z o : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (varintSegmentAllInternalTokenSegmentPropertiesSentence w B z o)) := TheoryTransport.sentence (source_varintSegmentAllInternalTokenSegmentProperties w B z o)

theorem native_varintSegmentAllInternalTokenSegmentProperties {m} (w B z o : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (varintSegmentAllInternalTokenSegmentPropertiesSentence w B z o)) := ZFReplay.replay (varintSegmentAllInternalTokenSegmentProperties_kernel_certificate w B z o)

def varintSegmentEveryActualCanonicalSegmentConsumesExactlySentence {m} (w B z o n C T L v s a u c p : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 128 B).imp ((empty z).imp ((Formula.mem o w).imp ((PacketVarintSyntax.canonical w n C).imp ((StructuralListSpliceSyntax.splice w C T L).imp ((PacketReaderStepSyntax.state w T v s a).imp ((PacketReaderVarintSegmentSyntax.guard o n s).imp ((PacketAffineSyntax.equation w n v s u).imp ((StructuralListSyntax.consCode w u a c).imp ((PacketReaderVarintSegmentSyntax.agreement w B z o L T v s a c p)))))))))))).close

theorem source_varintSegmentEveryActualCanonicalSegmentConsumesExactly {m} (w B z o n C T L v s a u c p : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (varintSegmentEveryActualCanonicalSegmentConsumesExactlySentence w B z o n C T L v s a u c p) := by
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
  let Δ : Context m := Context.add (StructuralListSyntax.consCode w u a c) (Context.add (PacketAffineSyntax.equation w n v s u) (Context.add (PacketReaderVarintSegmentSyntax.guard o n s) (Context.add (PacketReaderStepSyntax.state w T v s a) (Context.add (StructuralListSpliceSyntax.splice w C T L) (Context.add (PacketVarintSyntax.canonical w n C) (Context.add (Formula.mem o w) (Context.add (empty z) (Context.add (SyntaxNumeralSyntax.numeral 128 B) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))))))
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
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 128 B) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))
  have h2 : Derives Δ (empty z) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  have h3 : Derives Δ (Formula.mem o w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h4 : Derives Δ (PacketVarintSyntax.canonical w n C) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h5 : Derives Δ (StructuralListSpliceSyntax.splice w C T L) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h6 : Derives Δ (PacketReaderStepSyntax.state w T v s a) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h7 : Derives Δ (PacketReaderVarintSegmentSyntax.guard o n s) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h8 : Derives Δ (PacketAffineSyntax.equation w n v s u) := .hyp (Or.inr (Or.inl rfl))
  have h9 : Derives Δ (StructuralListSyntax.consCode w u a c) := .hyp (Or.inl rfl)
  exact PacketReaderVarintSegmentInduction.segment hZ w B z o n C T L v s a u c p h0 h1 h2 h3 h4 h5 h6 h7 h8 h9

theorem varintSegmentEveryActualCanonicalSegmentConsumesExactly_kernel_certificate {m} (w B z o n C T L v s a u c p : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (varintSegmentEveryActualCanonicalSegmentConsumesExactlySentence w B z o n C T L v s a u c p)) := TheoryTransport.sentence (source_varintSegmentEveryActualCanonicalSegmentConsumesExactly w B z o n C T L v s a u c p)

theorem native_varintSegmentEveryActualCanonicalSegmentConsumesExactly {m} (w B z o n C T L v s a u c p : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (varintSegmentEveryActualCanonicalSegmentConsumesExactlySentence w B z o n C T L v s a u c p)) := ZFReplay.replay (varintSegmentEveryActualCanonicalSegmentConsumesExactly_kernel_certificate w B z o n C T L v s a u c p)

def varintSegmentCompleteCanonicalSegmentAllOutputsSentence {m} (w B z o n C T L v s a u c : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 128 B).imp ((empty z).imp ((Formula.mem o w).imp ((PacketVarintSyntax.canonical w n C).imp ((StructuralListSpliceSyntax.splice w C T L).imp ((PacketReaderStepSyntax.state w T v s a).imp ((PacketReaderVarintSegmentSyntax.guard o n s).imp ((PacketAffineSyntax.equation w n v s u).imp ((StructuralListSyntax.consCode w u a c).imp ((PacketReaderVarintConsumption.allOutputs w B z o L T v s a c)))))))))))).close

theorem source_varintSegmentCompleteCanonicalSegmentAllOutputs {m} (w B z o n C T L v s a u c : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (varintSegmentCompleteCanonicalSegmentAllOutputsSentence w B z o n C T L v s a u c) := by
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
  let Δ : Context m := Context.add (StructuralListSyntax.consCode w u a c) (Context.add (PacketAffineSyntax.equation w n v s u) (Context.add (PacketReaderVarintSegmentSyntax.guard o n s) (Context.add (PacketReaderStepSyntax.state w T v s a) (Context.add (StructuralListSpliceSyntax.splice w C T L) (Context.add (PacketVarintSyntax.canonical w n C) (Context.add (Formula.mem o w) (Context.add (empty z) (Context.add (SyntaxNumeralSyntax.numeral 128 B) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))))))
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
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 128 B) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))
  have h2 : Derives Δ (empty z) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  have h3 : Derives Δ (Formula.mem o w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h4 : Derives Δ (PacketVarintSyntax.canonical w n C) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h5 : Derives Δ (StructuralListSpliceSyntax.splice w C T L) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h6 : Derives Δ (PacketReaderStepSyntax.state w T v s a) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h7 : Derives Δ (PacketReaderVarintSegmentSyntax.guard o n s) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h8 : Derives Δ (PacketAffineSyntax.equation w n v s u) := .hyp (Or.inr (Or.inl rfl))
  have h9 : Derives Δ (StructuralListSyntax.consCode w u a c) := .hyp (Or.inl rfl)
  exact PacketReaderVarintConsumption.all_outputs hZ w B z o n C T L v s a u c h0 h1 h2 h3 h4 h5 h6 h7 h8 h9

theorem varintSegmentCompleteCanonicalSegmentAllOutputs_kernel_certificate {m} (w B z o n C T L v s a u c : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (varintSegmentCompleteCanonicalSegmentAllOutputsSentence w B z o n C T L v s a u c)) := TheoryTransport.sentence (source_varintSegmentCompleteCanonicalSegmentAllOutputs w B z o n C T L v s a u c)

theorem native_varintSegmentCompleteCanonicalSegmentAllOutputs {m} (w B z o n C T L v s a u c : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (varintSegmentCompleteCanonicalSegmentAllOutputsSentence w B z o n C T L v s a u c)) := ZFReplay.replay (varintSegmentCompleteCanonicalSegmentAllOutputs_kernel_certificate w B z o n C T L v s a u c)

def varintSegmentUniqueActualJoinedInputAndAllOutputConsumptionSentence {m} (w B z o n C T v s a u c : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 128 B).imp ((empty z).imp ((Formula.mem o w).imp ((PacketVarintSyntax.canonical w n C).imp ((PacketReaderStepSyntax.state w T v s a).imp ((PacketReaderVarintSegmentSyntax.guard o n s).imp ((PacketAffineSyntax.equation w n v s u).imp ((StructuralListSyntax.consCode w u a c).imp ((PacketReaderVarintConsumption.complete w B z o C T v s a c))))))))))).close

theorem source_varintSegmentUniqueActualJoinedInputAndAllOutputConsumption {m} (w B z o n C T v s a u c : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (varintSegmentUniqueActualJoinedInputAndAllOutputConsumptionSentence w B z o n C T v s a u c) := by
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
  let Δ : Context m := Context.add (StructuralListSyntax.consCode w u a c) (Context.add (PacketAffineSyntax.equation w n v s u) (Context.add (PacketReaderVarintSegmentSyntax.guard o n s) (Context.add (PacketReaderStepSyntax.state w T v s a) (Context.add (PacketVarintSyntax.canonical w n C) (Context.add (Formula.mem o w) (Context.add (empty z) (Context.add (SyntaxNumeralSyntax.numeral 128 B) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))))
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
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 128 B) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  have h2 : Derives Δ (empty z) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h3 : Derives Δ (Formula.mem o w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h4 : Derives Δ (PacketVarintSyntax.canonical w n C) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h5 : Derives Δ (PacketReaderStepSyntax.state w T v s a) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h6 : Derives Δ (PacketReaderVarintSegmentSyntax.guard o n s) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h7 : Derives Δ (PacketAffineSyntax.equation w n v s u) := .hyp (Or.inr (Or.inl rfl))
  have h8 : Derives Δ (StructuralListSyntax.consCode w u a c) := .hyp (Or.inl rfl)
  exact PacketReaderVarintConsumption.exists_unique hZ w B z o n C T v s a u c h0 h1 h2 h3 h4 h5 h6 h7 h8

theorem varintSegmentUniqueActualJoinedInputAndAllOutputConsumption_kernel_certificate {m} (w B z o n C T v s a u c : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (varintSegmentUniqueActualJoinedInputAndAllOutputConsumptionSentence w B z o n C T v s a u c)) := TheoryTransport.sentence (source_varintSegmentUniqueActualJoinedInputAndAllOutputConsumption w B z o n C T v s a u c)

theorem native_varintSegmentUniqueActualJoinedInputAndAllOutputConsumption {m} (w B z o n C T v s a u c : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (varintSegmentUniqueActualJoinedInputAndAllOutputConsumptionSentence w B z o n C T v s a u c)) := ZFReplay.replay (varintSegmentUniqueActualJoinedInputAndAllOutputConsumption_kernel_certificate w B z o n C T v s a u c)

end PPAC.Migration.Internal.ObjectPacketReaderVarintSegment
