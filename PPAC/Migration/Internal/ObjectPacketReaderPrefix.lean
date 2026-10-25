import PPAC.Migration.Internal.PacketReaderPrefixInduction
import PPAC.Migration.Internal.PacketReaderOutputBackward

/-! Every successful bounded nonempty actual byte input at positive scale has a real canonical prefix and strict actual suffix-code descent, by original full Separation and Foundation. Complete multi-token inverse, Proof and Con remain unproved -/
namespace PPAC.Migration.Internal.ObjectPacketReaderPrefix
open Source SourceAlgebra SourceLogic OmegaSyntax

def readerPrefixOutputOrderBackwardConsSentence {m} (w h A A1 e T HT O : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem h w).imp ((StructuralListSyntax.nilCode w e).imp ((StructuralListSyntax.consCode w h A A1).imp ((StructuralListTraceSyntax.valid w A).imp ((StructuralListTraceSyntax.valid w T).imp ((StructuralListSyntax.consCode w h T HT).imp ((PacketReaderOutputOrder.output w A1 T O).imp ((PacketReaderOutputOrder.output w A HT O)))))))))).close

theorem source_readerPrefixOutputOrderBackwardCons {m} (w h A A1 e T HT O : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (readerPrefixOutputOrderBackwardConsSentence w h A A1 e T HT O) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderOutputOrder.output w A1 T O) (Context.add (StructuralListSyntax.consCode w h T HT) (Context.add (StructuralListTraceSyntax.valid w T) (Context.add (StructuralListTraceSyntax.valid w A) (Context.add (StructuralListSyntax.consCode w h A A1) (Context.add (StructuralListSyntax.nilCode w e) (Context.add (Formula.mem h w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))))
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
  have h1 : Derives Δ (Formula.mem h w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h2 : Derives Δ (StructuralListSyntax.nilCode w e) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h3 : Derives Δ (StructuralListSyntax.consCode w h A A1) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h4 : Derives Δ (StructuralListTraceSyntax.valid w A) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h5 : Derives Δ (StructuralListTraceSyntax.valid w T) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h6 : Derives Δ (StructuralListSyntax.consCode w h T HT) := .hyp (Or.inr (Or.inl rfl))
  have h7 : Derives Δ (PacketReaderOutputOrder.output w A1 T O) := .hyp (Or.inl rfl)
  exact PacketReaderOutputBackward.step hZ w h A A1 e T HT O h0 h1 h2 h3 h4 h5 h6 h7

theorem readerPrefixOutputOrderBackwardCons_kernel_certificate {m} (w h A A1 e T HT O : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (readerPrefixOutputOrderBackwardConsSentence w h A A1 e T HT O)) := TheoryTransport.sentence (source_readerPrefixOutputOrderBackwardCons w h A A1 e T HT O)

theorem native_readerPrefixOutputOrderBackwardCons {m} (w h A A1 e T HT O : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (readerPrefixOutputOrderBackwardConsSentence w h A A1 e T HT O)) := ZFReplay.replay (readerPrefixOutputOrderBackwardCons_kernel_certificate w h A A1 e T HT O)

def readerPrefixOutputOrderExactConsSentence {m} (w h A A1 e T HT O : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem h w).imp ((StructuralListSyntax.nilCode w e).imp ((StructuralListSyntax.consCode w h A A1).imp ((StructuralListTraceSyntax.valid w A).imp ((StructuralListTraceSyntax.valid w T).imp ((StructuralListSyntax.consCode w h T HT).imp (((PacketReaderOutputOrder.output w A1 T O).iff (PacketReaderOutputOrder.output w A HT O)))))))))).close

theorem source_readerPrefixOutputOrderExactCons {m} (w h A A1 e T HT O : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (readerPrefixOutputOrderExactConsSentence w h A A1 e T HT O) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralListSyntax.consCode w h T HT) (Context.add (StructuralListTraceSyntax.valid w T) (Context.add (StructuralListTraceSyntax.valid w A) (Context.add (StructuralListSyntax.consCode w h A A1) (Context.add (StructuralListSyntax.nilCode w e) (Context.add (Formula.mem h w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))
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
  have h1 : Derives Δ (Formula.mem h w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h2 : Derives Δ (StructuralListSyntax.nilCode w e) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h3 : Derives Δ (StructuralListSyntax.consCode w h A A1) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : Derives Δ (StructuralListTraceSyntax.valid w A) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h5 : Derives Δ (StructuralListTraceSyntax.valid w T) := .hyp (Or.inr (Or.inl rfl))
  have h6 : Derives Δ (StructuralListSyntax.consCode w h T HT) := .hyp (Or.inl rfl)
  exact PacketReaderOutputBackward.step_iff hZ w h A A1 e T HT O h0 h1 h2 h3 h4 h5 h6

theorem readerPrefixOutputOrderExactCons_kernel_certificate {m} (w h A A1 e T HT O : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (readerPrefixOutputOrderExactConsSentence w h A A1 e T HT O)) := TheoryTransport.sentence (source_readerPrefixOutputOrderExactCons w h A A1 e T HT O)

theorem native_readerPrefixOutputOrderExactCons {m} (w h A A1 e T HT O : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (readerPrefixOutputOrderExactConsSentence w h A A1 e T HT O)) := ZFReplay.replay (readerPrefixOutputOrderExactCons_kernel_certificate w h A A1 e T HT O)

def readerPrefixOutputOrderExactNilAccumulatorSentence {m} (w e T O : Fin m) : Source.Sentence := ((omega w).imp ((StructuralListSyntax.nilCode w e).imp (((PacketReaderOutputOrder.output w e T O).iff ((StructuralListTraceSyntax.valid w T).conj (Formula.equal T O)))))).close

theorem source_readerPrefixOutputOrderExactNilAccumulator {m} (w e T O : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (readerPrefixOutputOrderExactNilAccumulatorSentence w e T O) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralListSyntax.nilCode w e) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (StructuralListSyntax.nilCode w e) := .hyp (Or.inl rfl)
  exact PacketReaderOutputBackward.nil_accumulator hZ w e T O h0 h1

theorem readerPrefixOutputOrderExactNilAccumulator_kernel_certificate {m} (w e T O : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (readerPrefixOutputOrderExactNilAccumulatorSentence w e T O)) := TheoryTransport.sentence (source_readerPrefixOutputOrderExactNilAccumulator w e T O)

theorem native_readerPrefixOutputOrderExactNilAccumulator {m} (w e T O : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (readerPrefixOutputOrderExactNilAccumulatorSentence w e T O)) := ZFReplay.replay (readerPrefixOutputOrderExactNilAccumulator_kernel_certificate w e T O)

def readerPrefixEveryActualEvaluationHasGenuineStateSentence {m} (w B z o L v s A p : Fin m) : Source.Sentence := ((PacketReaderEvalSyntax.eval w B z o L v s A p).imp ((PacketReaderStepSyntax.state w L v s A))).close

theorem source_readerPrefixEveryActualEvaluationHasGenuineState {m} (w B z o L v s A p : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (readerPrefixEveryActualEvaluationHasGenuineStateSentence w B z o L v s A p) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderEvalSyntax.eval w B z o L v s A p) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (PacketReaderEvalSyntax.eval w B z o L v s A p) := .hyp (Or.inl rfl)
  exact PacketReaderSuccess.state w B z o L v s A p h0

theorem readerPrefixEveryActualEvaluationHasGenuineState_kernel_certificate {m} (w B z o L v s A p : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (readerPrefixEveryActualEvaluationHasGenuineStateSentence w B z o L v s A p)) := TheoryTransport.sentence (source_readerPrefixEveryActualEvaluationHasGenuineState w B z o L v s A p)

theorem native_readerPrefixEveryActualEvaluationHasGenuineState {m} (w B z o L v s A p : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (readerPrefixEveryActualEvaluationHasGenuineStateSentence w B z o L v s A p)) := ZFReplay.replay (readerPrefixEveryActualEvaluationHasGenuineState_kernel_certificate w B z o L v s A p)

def readerPrefixActualNilSuccessHasEOFGuardAndReverseSentence {m} (w B z o L v s A O p : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem B w).imp ((empty z).imp ((successor o z).imp ((StructuralListSyntax.nilCode w L).imp ((PacketReaderEvalSyntax.eval w B z o L v s A p).imp ((PacketReaderReturnSyntax.some w O p).imp (((PacketReaderInputSyntax.eofSuccess w z o L v s A).conj (StructuralListReverseSyntax.reverses w A O)))))))))).close

theorem source_readerPrefixActualNilSuccessHasEOFGuardAndReverse {m} (w B z o L v s A O p : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (readerPrefixActualNilSuccessHasEOFGuardAndReverseSentence w B z o L v s A O p) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderReturnSyntax.some w O p) (Context.add (PacketReaderEvalSyntax.eval w B z o L v s A p) (Context.add (StructuralListSyntax.nilCode w L) (Context.add (successor o z) (Context.add (empty z) (Context.add (Formula.mem B w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))
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
  have h1 : Derives Δ (Formula.mem B w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h2 : Derives Δ (empty z) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h3 : Derives Δ (successor o z) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : Derives Δ (StructuralListSyntax.nilCode w L) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h5 : Derives Δ (PacketReaderEvalSyntax.eval w B z o L v s A p) := .hyp (Or.inr (Or.inl rfl))
  have h6 : Derives Δ (PacketReaderReturnSyntax.some w O p) := .hyp (Or.inl rfl)
  exact PacketReaderSuccess.nil_success hZ w B z o L v s A O p h0 h1 h2 h3 h4 h5 h6

theorem readerPrefixActualNilSuccessHasEOFGuardAndReverse_kernel_certificate {m} (w B z o L v s A O p : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (readerPrefixActualNilSuccessHasEOFGuardAndReverseSentence w B z o L v s A O p)) := TheoryTransport.sentence (source_readerPrefixActualNilSuccessHasEOFGuardAndReverse w B z o L v s A O p)

theorem native_readerPrefixActualNilSuccessHasEOFGuardAndReverse {m} (w B z o L v s A O p : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (readerPrefixActualNilSuccessHasEOFGuardAndReverseSentence w B z o L v s A O p)) := ZFReplay.replay (readerPrefixActualNilSuccessHasEOFGuardAndReverse_kernel_certificate w B z o L v s A O p)

def readerPrefixActualNilSuccessHasExactGuardSentence {m} (w B z o L v s A O p : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem B w).imp ((empty z).imp ((successor o z).imp ((StructuralListSyntax.nilCode w L).imp ((PacketReaderEvalSyntax.eval w B z o L v s A p).imp ((PacketReaderReturnSyntax.some w O p).imp (((Formula.equal s o).conj (Formula.equal v z)))))))))).close

theorem source_readerPrefixActualNilSuccessHasExactGuard {m} (w B z o L v s A O p : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (readerPrefixActualNilSuccessHasExactGuardSentence w B z o L v s A O p) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderReturnSyntax.some w O p) (Context.add (PacketReaderEvalSyntax.eval w B z o L v s A p) (Context.add (StructuralListSyntax.nilCode w L) (Context.add (successor o z) (Context.add (empty z) (Context.add (Formula.mem B w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))
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
  have h1 : Derives Δ (Formula.mem B w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h2 : Derives Δ (empty z) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h3 : Derives Δ (successor o z) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : Derives Δ (StructuralListSyntax.nilCode w L) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h5 : Derives Δ (PacketReaderEvalSyntax.eval w B z o L v s A p) := .hyp (Or.inr (Or.inl rfl))
  have h6 : Derives Δ (PacketReaderReturnSyntax.some w O p) := .hyp (Or.inl rfl)
  exact PacketReaderSuccess.nil_guard hZ w B z o L v s A O p h0 h1 h2 h3 h4 h5 h6

theorem readerPrefixActualNilSuccessHasExactGuard_kernel_certificate {m} (w B z o L v s A O p : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (readerPrefixActualNilSuccessHasExactGuardSentence w B z o L v s A O p)) := TheoryTransport.sentence (source_readerPrefixActualNilSuccessHasExactGuard w B z o L v s A O p)

theorem native_readerPrefixActualNilSuccessHasExactGuard {m} (w B z o L v s A O p : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (readerPrefixActualNilSuccessHasExactGuardSentence w B z o L v s A O p)) := ZFReplay.replay (readerPrefixActualNilSuccessHasExactGuard_kernel_certificate w B z o L v s A O p)

def readerPrefixActualNilSuccessHasActualReverseSentence {m} (w B z o L v s A O p : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem B w).imp ((empty z).imp ((successor o z).imp ((StructuralListSyntax.nilCode w L).imp ((PacketReaderEvalSyntax.eval w B z o L v s A p).imp ((PacketReaderReturnSyntax.some w O p).imp ((StructuralListReverseSyntax.reverses w A O))))))))).close

theorem source_readerPrefixActualNilSuccessHasActualReverse {m} (w B z o L v s A O p : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (readerPrefixActualNilSuccessHasActualReverseSentence w B z o L v s A O p) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderReturnSyntax.some w O p) (Context.add (PacketReaderEvalSyntax.eval w B z o L v s A p) (Context.add (StructuralListSyntax.nilCode w L) (Context.add (successor o z) (Context.add (empty z) (Context.add (Formula.mem B w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))
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
  have h1 : Derives Δ (Formula.mem B w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h2 : Derives Δ (empty z) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h3 : Derives Δ (successor o z) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : Derives Δ (StructuralListSyntax.nilCode w L) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h5 : Derives Δ (PacketReaderEvalSyntax.eval w B z o L v s A p) := .hyp (Or.inr (Or.inl rfl))
  have h6 : Derives Δ (PacketReaderReturnSyntax.some w O p) := .hyp (Or.inl rfl)
  exact PacketReaderSuccess.nil_reverse hZ w B z o L v s A O p h0 h1 h2 h3 h4 h5 h6

theorem readerPrefixActualNilSuccessHasActualReverse_kernel_certificate {m} (w B z o L v s A O p : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (readerPrefixActualNilSuccessHasActualReverseSentence w B z o L v s A O p)) := TheoryTransport.sentence (source_readerPrefixActualNilSuccessHasActualReverse w B z o L v s A O p)

theorem native_readerPrefixActualNilSuccessHasActualReverse {m} (w B z o L v s A O p : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (readerPrefixActualNilSuccessHasActualReverseSentence w B z o L v s A O p)) := ZFReplay.replay (readerPrefixActualNilSuccessHasActualReverse_kernel_certificate w B z o L v s A O p)

def readerPrefixActualSomeSuccessExcludesRejectionSentence {m} (w B z o L v s A O p : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem B w).imp ((empty z).imp ((successor o z).imp ((PacketReaderReturnSyntax.rejection w B z o L v s A).imp ((PacketReaderEvalSyntax.eval w B z o L v s A p).imp ((PacketReaderReturnSyntax.some w O p).imp ((Formula.bot))))))))).close

theorem source_readerPrefixActualSomeSuccessExcludesRejection {m} (w B z o L v s A O p : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (readerPrefixActualSomeSuccessExcludesRejectionSentence w B z o L v s A O p) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderReturnSyntax.some w O p) (Context.add (PacketReaderEvalSyntax.eval w B z o L v s A p) (Context.add (PacketReaderReturnSyntax.rejection w B z o L v s A) (Context.add (successor o z) (Context.add (empty z) (Context.add (Formula.mem B w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))
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
  have h1 : Derives Δ (Formula.mem B w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h2 : Derives Δ (empty z) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h3 : Derives Δ (successor o z) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : Derives Δ (PacketReaderReturnSyntax.rejection w B z o L v s A) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h5 : Derives Δ (PacketReaderEvalSyntax.eval w B z o L v s A p) := .hyp (Or.inr (Or.inl rfl))
  have h6 : Derives Δ (PacketReaderReturnSyntax.some w O p) := .hyp (Or.inl rfl)
  exact PacketReaderSuccess.rejection_disjoint hZ w B z o L v s A O p h0 h1 h2 h3 h4 h5 h6

theorem readerPrefixActualSomeSuccessExcludesRejection_kernel_certificate {m} (w B z o L v s A O p : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (readerPrefixActualSomeSuccessExcludesRejectionSentence w B z o L v s A O p)) := TheoryTransport.sentence (source_readerPrefixActualSomeSuccessExcludesRejection w B z o L v s A O p)

theorem native_readerPrefixActualSomeSuccessExcludesRejection {m} (w B z o L v s A O p : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (readerPrefixActualSomeSuccessExcludesRejectionSentence w B z o L v s A O p)) := ZFReplay.replay (readerPrefixActualSomeSuccessExcludesRejection_kernel_certificate w B z o L v s A O p)

def readerPrefixActualSomeSuccessExcludesRejectedHeadSentence {m} (w B z o L b X v s A O p : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem B w).imp ((empty z).imp ((successor o z).imp ((PacketReaderInputSyntax.headRest w L b X).imp ((PacketReaderStepSyntax.reject B z o b s).imp ((PacketReaderEvalSyntax.eval w B z o L v s A p).imp ((PacketReaderReturnSyntax.some w O p).imp ((Formula.bot)))))))))).close

theorem source_readerPrefixActualSomeSuccessExcludesRejectedHead {m} (w B z o L b X v s A O p : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (readerPrefixActualSomeSuccessExcludesRejectedHeadSentence w B z o L b X v s A O p) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderReturnSyntax.some w O p) (Context.add (PacketReaderEvalSyntax.eval w B z o L v s A p) (Context.add (PacketReaderStepSyntax.reject B z o b s) (Context.add (PacketReaderInputSyntax.headRest w L b X) (Context.add (successor o z) (Context.add (empty z) (Context.add (Formula.mem B w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))))
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
  have h1 : Derives Δ (Formula.mem B w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h2 : Derives Δ (empty z) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h3 : Derives Δ (successor o z) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h4 : Derives Δ (PacketReaderInputSyntax.headRest w L b X) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h5 : Derives Δ (PacketReaderStepSyntax.reject B z o b s) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h6 : Derives Δ (PacketReaderEvalSyntax.eval w B z o L v s A p) := .hyp (Or.inr (Or.inl rfl))
  have h7 : Derives Δ (PacketReaderReturnSyntax.some w O p) := .hyp (Or.inl rfl)
  exact PacketReaderSuccess.reject_at_cons hZ w B z o L b X v s A O p h0 h1 h2 h3 h4 h5 h6 h7

theorem readerPrefixActualSomeSuccessExcludesRejectedHead_kernel_certificate {m} (w B z o L b X v s A O p : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (readerPrefixActualSomeSuccessExcludesRejectedHeadSentence w B z o L b X v s A O p)) := TheoryTransport.sentence (source_readerPrefixActualSomeSuccessExcludesRejectedHead w B z o L b X v s A O p)

theorem native_readerPrefixActualSomeSuccessExcludesRejectedHead {m} (w B z o L b X v s A O p : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (readerPrefixActualSomeSuccessExcludesRejectedHeadSentence w B z o L b X v s A O p)) := ZFReplay.replay (readerPrefixActualSomeSuccessExcludesRejectedHead_kernel_certificate w B z o L b X v s A O p)

def readerPrefixNonunitSuccessfulInputIsNotNilSentence {m} (w B z o L v s A O p : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem B w).imp ((empty z).imp ((successor o z).imp ((PacketReaderEvalSyntax.eval w B z o L v s A p).imp ((PacketReaderReturnSyntax.some w O p).imp (((Formula.equal s o).neg).imp (((StructuralListSyntax.nilCode w L).neg))))))))).close

theorem source_readerPrefixNonunitSuccessfulInputIsNotNil {m} (w B z o L v s A O p : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (readerPrefixNonunitSuccessfulInputIsNotNilSentence w B z o L v s A O p) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add ((Formula.equal s o).neg) (Context.add (PacketReaderReturnSyntax.some w O p) (Context.add (PacketReaderEvalSyntax.eval w B z o L v s A p) (Context.add (successor o z) (Context.add (empty z) (Context.add (Formula.mem B w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))
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
  have h1 : Derives Δ (Formula.mem B w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h2 : Derives Δ (empty z) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h3 : Derives Δ (successor o z) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : Derives Δ (PacketReaderEvalSyntax.eval w B z o L v s A p) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h5 : Derives Δ (PacketReaderReturnSyntax.some w O p) := .hyp (Or.inr (Or.inl rfl))
  have h6 : Derives Δ ((Formula.equal s o).neg) := .hyp (Or.inl rfl)
  exact PacketReaderSuccess.nonunit_not_nil hZ w B z o L v s A O p h0 h1 h2 h3 h4 h5 h6

theorem readerPrefixNonunitSuccessfulInputIsNotNil_kernel_certificate {m} (w B z o L v s A O p : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (readerPrefixNonunitSuccessfulInputIsNotNilSentence w B z o L v s A O p)) := TheoryTransport.sentence (source_readerPrefixNonunitSuccessfulInputIsNotNil w B z o L v s A O p)

theorem native_readerPrefixNonunitSuccessfulInputIsNotNil {m} (w B z o L v s A O p : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (readerPrefixNonunitSuccessfulInputIsNotNilSentence w B z o L v s A O p)) := ZFReplay.replay (readerPrefixNonunitSuccessfulInputIsNotNil_kernel_certificate w B z o L v s A O p)

def readerPrefixContinuationReconstructsActualCanonicalConsSentence {m} (w B d k n b Q C : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 128 B).imp ((PacketAffineSyntax.affine w B d k n).imp (((empty k).neg).imp ((NaturalAdditionSyntax.sum w B d b).imp ((PacketVarintSyntax.canonical w k Q).imp ((StructuralListSyntax.consCode w b Q C).imp ((PacketVarintSyntax.canonical w n C))))))))).close

theorem source_readerPrefixContinuationReconstructsActualCanonicalCons {m} (w B d k n b Q C : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (readerPrefixContinuationReconstructsActualCanonicalConsSentence w B d k n b Q C) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralListSyntax.consCode w b Q C) (Context.add (PacketVarintSyntax.canonical w k Q) (Context.add (NaturalAdditionSyntax.sum w B d b) (Context.add ((empty k).neg) (Context.add (PacketAffineSyntax.affine w B d k n) (Context.add (SyntaxNumeralSyntax.numeral 128 B) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))
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
  have h2 : Derives Δ (PacketAffineSyntax.affine w B d k n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h3 : Derives Δ ((empty k).neg) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : Derives Δ (NaturalAdditionSyntax.sum w B d b) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h5 : Derives Δ (PacketVarintSyntax.canonical w k Q) := .hyp (Or.inr (Or.inl rfl))
  have h6 : Derives Δ (StructuralListSyntax.consCode w b Q C) := .hyp (Or.inl rfl)
  exact PacketReaderPrefixReconstruct.canonical_cons hZ w B d k n b Q C h0 h1 h2 h3 h4 h5 h6

theorem readerPrefixContinuationReconstructsActualCanonicalCons_kernel_certificate {m} (w B d k n b Q C : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (readerPrefixContinuationReconstructsActualCanonicalConsSentence w B d k n b Q C)) := TheoryTransport.sentence (source_readerPrefixContinuationReconstructsActualCanonicalCons w B d k n b Q C)

theorem native_readerPrefixContinuationReconstructsActualCanonicalCons {m} (w B d k n b Q C : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (readerPrefixContinuationReconstructsActualCanonicalConsSentence w B d k n b Q C)) := ZFReplay.replay (readerPrefixContinuationReconstructsActualCanonicalCons_kernel_certificate w B d k n b Q C)

def readerPrefixStrictSuffixCodeMembershipComposesSentence {m} (w L X T : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem L w).imp ((Formula.mem X L).imp ((Formula.mem T X).imp ((Formula.mem T L)))))).close

theorem source_readerPrefixStrictSuffixCodeMembershipComposes {m} (w L X T : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (readerPrefixStrictSuffixCodeMembershipComposesSentence w L X T) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem T X) (Context.add (Formula.mem X L) (Context.add (Formula.mem L w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (Formula.mem L w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (Formula.mem X L) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (Formula.mem T X) := .hyp (Or.inl rfl)
  exact PacketReaderPrefixReconstruct.suffix_member hZ w L X T h0 h1 h2 h3

theorem readerPrefixStrictSuffixCodeMembershipComposes_kernel_certificate {m} (w L X T : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (readerPrefixStrictSuffixCodeMembershipComposesSentence w L X T)) := TheoryTransport.sentence (source_readerPrefixStrictSuffixCodeMembershipComposes w L X T)

theorem native_readerPrefixStrictSuffixCodeMembershipComposes {m} (w L X T : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (readerPrefixStrictSuffixCodeMembershipComposesSentence w L X T)) := ZFReplay.replay (readerPrefixStrictSuffixCodeMembershipComposes_kernel_certificate w L X T)

def readerPrefixNonzeroContinuationHasSourceGuardSentence {m} (w B d k n o s : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 128 B).imp ((PacketAffineSyntax.affine w B d k n).imp (((empty k).neg).imp ((PacketReaderVarintSegmentSyntax.guard o n s)))))).close

theorem source_readerPrefixNonzeroContinuationHasSourceGuard {m} (w B d k n o s : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (readerPrefixNonzeroContinuationHasSourceGuardSentence w B d k n o s) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add ((empty k).neg) (Context.add (PacketAffineSyntax.affine w B d k n) (Context.add (SyntaxNumeralSyntax.numeral 128 B) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 128 B) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (PacketAffineSyntax.affine w B d k n) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ ((empty k).neg) := .hyp (Or.inl rfl)
  exact PacketReaderPrefixReconstruct.nonzero_guard hZ w B d k n o s h0 h1 h2 h3

theorem readerPrefixNonzeroContinuationHasSourceGuard_kernel_certificate {m} (w B d k n o s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (readerPrefixNonzeroContinuationHasSourceGuardSentence w B d k n o s)) := TheoryTransport.sentence (source_readerPrefixNonzeroContinuationHasSourceGuard w B d k n o s)

theorem native_readerPrefixNonzeroContinuationHasSourceGuard {m} (w B d k n o s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (readerPrefixNonzeroContinuationHasSourceGuardSentence w B d k n o s)) := ZFReplay.replay (readerPrefixNonzeroContinuationHasSourceGuard_kernel_certificate w B d k n o s)

def readerPrefixContinuationReconstructsActualSpliceConsSentence {m} (w b Q C X T L : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem b w).imp ((StructuralListSyntax.consCode w b Q C).imp ((StructuralListSpliceSyntax.splice w Q T X).imp ((StructuralListSyntax.consCode w b X L).imp ((StructuralListSpliceSyntax.splice w C T L))))))).close

theorem source_readerPrefixContinuationReconstructsActualSpliceCons {m} (w b Q C X T L : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (readerPrefixContinuationReconstructsActualSpliceConsSentence w b Q C X T L) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralListSyntax.consCode w b X L) (Context.add (StructuralListSpliceSyntax.splice w Q T X) (Context.add (StructuralListSyntax.consCode w b Q C) (Context.add (Formula.mem b w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (Formula.mem b w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (StructuralListSyntax.consCode w b Q C) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (StructuralListSpliceSyntax.splice w Q T X) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (StructuralListSyntax.consCode w b X L) := .hyp (Or.inl rfl)
  exact PacketReaderPrefixReconstruct.splice_cons hZ w b Q C X T L h0 h1 h2 h3 h4

theorem readerPrefixContinuationReconstructsActualSpliceCons_kernel_certificate {m} (w b Q C X T L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (readerPrefixContinuationReconstructsActualSpliceConsSentence w b Q C X T L)) := TheoryTransport.sentence (source_readerPrefixContinuationReconstructsActualSpliceCons w b Q C X T L)

theorem native_readerPrefixContinuationReconstructsActualSpliceCons {m} (w b Q C X T L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (readerPrefixContinuationReconstructsActualSpliceConsSentence w b Q C X T L)) := ZFReplay.replay (readerPrefixContinuationReconstructsActualSpliceCons_kernel_certificate w b Q C X T L)

def readerPrefixTerminalDigitReconstructsActualPrefixSentence {m} (w B z o L b X v s A p : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 128 B).imp ((empty z).imp ((successor o z).imp ((StructuralListSyntax.consCode w b X L).imp ((PacketByteInputSyntax.byteList w X).imp ((Formula.mem b B).imp ((PacketReaderVarintSegmentSyntax.guard o b s).imp ((PacketReaderStepSyntax.state w L v s A).imp ((PacketReaderEvalSyntax.eval w B z o L v s A p).imp ((PacketReaderPrefixSyntax.result w B z o L v s A p)))))))))))).close

theorem source_readerPrefixTerminalDigitReconstructsActualPrefix {m} (w B z o L b X v s A p : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (readerPrefixTerminalDigitReconstructsActualPrefixSentence w B z o L b X v s A p) := by
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
  let Δ : Context m := Context.add (PacketReaderEvalSyntax.eval w B z o L v s A p) (Context.add (PacketReaderStepSyntax.state w L v s A) (Context.add (PacketReaderVarintSegmentSyntax.guard o b s) (Context.add (Formula.mem b B) (Context.add (PacketByteInputSyntax.byteList w X) (Context.add (StructuralListSyntax.consCode w b X L) (Context.add (successor o z) (Context.add (empty z) (Context.add (SyntaxNumeralSyntax.numeral 128 B) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))))))
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
  have h3 : Derives Δ (successor o z) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h4 : Derives Δ (StructuralListSyntax.consCode w b X L) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h5 : Derives Δ (PacketByteInputSyntax.byteList w X) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h6 : Derives Δ (Formula.mem b B) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h7 : Derives Δ (PacketReaderVarintSegmentSyntax.guard o b s) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h8 : Derives Δ (PacketReaderStepSyntax.state w L v s A) := .hyp (Or.inr (Or.inl rfl))
  have h9 : Derives Δ (PacketReaderEvalSyntax.eval w B z o L v s A p) := .hyp (Or.inl rfl)
  exact PacketReaderPrefixSmall.small hZ w B z o L b X v s A p h0 h1 h2 h3 h4 h5 h6 h7 h8 h9

theorem readerPrefixTerminalDigitReconstructsActualPrefix_kernel_certificate {m} (w B z o L b X v s A p : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (readerPrefixTerminalDigitReconstructsActualPrefixSentence w B z o L b X v s A p)) := TheoryTransport.sentence (source_readerPrefixTerminalDigitReconstructsActualPrefix w B z o L b X v s A p)

theorem native_readerPrefixTerminalDigitReconstructsActualPrefix {m} (w B z o L b X v s A p : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (readerPrefixTerminalDigitReconstructsActualPrefixSentence w B z o L b X v s A p)) := ZFReplay.replay (readerPrefixTerminalDigitReconstructsActualPrefix_kernel_certificate w B z o L b X v s A p)

def readerPrefixAllInternalCanonicalPrefixPropertiesSentence {m} (w B z o : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 128 B).imp ((empty z).imp ((successor o z).imp ((PacketReaderPrefixSyntax.allProperties w B z o)))))).close

theorem source_readerPrefixAllInternalCanonicalPrefixProperties {m} (w B z o : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (readerPrefixAllInternalCanonicalPrefixPropertiesSentence w B z o) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor o z) (Context.add (empty z) (Context.add (SyntaxNumeralSyntax.numeral 128 B) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 128 B) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (empty z) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (successor o z) := .hyp (Or.inl rfl)
  exact PacketReaderPrefixInduction.all_properties hZ w B z o h0 h1 h2 h3

theorem readerPrefixAllInternalCanonicalPrefixProperties_kernel_certificate {m} (w B z o : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (readerPrefixAllInternalCanonicalPrefixPropertiesSentence w B z o)) := TheoryTransport.sentence (source_readerPrefixAllInternalCanonicalPrefixProperties w B z o)

theorem native_readerPrefixAllInternalCanonicalPrefixProperties {m} (w B z o : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (readerPrefixAllInternalCanonicalPrefixPropertiesSentence w B z o)) := ZFReplay.replay (readerPrefixAllInternalCanonicalPrefixProperties_kernel_certificate w B z o)

def readerPrefixEverySuccessfulBoundedNonemptyInputHasCanonicalPrefixSentence {m} (w B z o L v s A O p : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 128 B).imp ((empty z).imp ((successor o z).imp ((PacketByteInputSyntax.byteList w L).imp (((empty s).neg).imp (((StructuralListSyntax.nilCode w L).neg).imp ((PacketReaderEvalSyntax.eval w B z o L v s A p).imp ((PacketReaderReturnSyntax.some w O p).imp ((PacketReaderPrefixSyntax.result w B z o L v s A p))))))))))).close

theorem source_readerPrefixEverySuccessfulBoundedNonemptyInputHasCanonicalPrefix {m} (w B z o L v s A O p : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (readerPrefixEverySuccessfulBoundedNonemptyInputHasCanonicalPrefixSentence w B z o L v s A O p) := by
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
  let Δ : Context m := Context.add (PacketReaderReturnSyntax.some w O p) (Context.add (PacketReaderEvalSyntax.eval w B z o L v s A p) (Context.add ((StructuralListSyntax.nilCode w L).neg) (Context.add ((empty s).neg) (Context.add (PacketByteInputSyntax.byteList w L) (Context.add (successor o z) (Context.add (empty z) (Context.add (SyntaxNumeralSyntax.numeral 128 B) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))))
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
  have h3 : Derives Δ (successor o z) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h4 : Derives Δ (PacketByteInputSyntax.byteList w L) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h5 : Derives Δ ((empty s).neg) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h6 : Derives Δ ((StructuralListSyntax.nilCode w L).neg) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h7 : Derives Δ (PacketReaderEvalSyntax.eval w B z o L v s A p) := .hyp (Or.inr (Or.inl rfl))
  have h8 : Derives Δ (PacketReaderReturnSyntax.some w O p) := .hyp (Or.inl rfl)
  exact PacketReaderPrefixInduction.extract_prefix hZ w B z o L v s A O p h0 h1 h2 h3 h4 (PacketReaderSuccess.state w B z o L v s A p h7) h5 h6 h7 h8

theorem readerPrefixEverySuccessfulBoundedNonemptyInputHasCanonicalPrefix_kernel_certificate {m} (w B z o L v s A O p : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (readerPrefixEverySuccessfulBoundedNonemptyInputHasCanonicalPrefixSentence w B z o L v s A O p)) := TheoryTransport.sentence (source_readerPrefixEverySuccessfulBoundedNonemptyInputHasCanonicalPrefix w B z o L v s A O p)

theorem native_readerPrefixEverySuccessfulBoundedNonemptyInputHasCanonicalPrefix {m} (w B z o L v s A O p : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (readerPrefixEverySuccessfulBoundedNonemptyInputHasCanonicalPrefixSentence w B z o L v s A O p)) := ZFReplay.replay (readerPrefixEverySuccessfulBoundedNonemptyInputHasCanonicalPrefix_kernel_certificate w B z o L v s A O p)

end PPAC.Migration.Internal.ObjectPacketReaderPrefix
