import PPAC.Migration.Internal.HornLookupSomeValue

/-! 完整原规则表关系式编译的任意内部lookup轨迹、实际规范集合及成功/拒绝的原YesMetaZFC核证书。 -/
namespace PPAC.Migration.Internal.ObjectLookupTrace
open Source SourceAlgebra SourceLogic OmegaSyntax

def actualOriginalLookupRowSentence {m} (w n i y : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem n w).imp ((Formula.mem i w).imp ((Formula.mem y w).imp ((HornLookupRowSyntax.existsRow w n i y)))))).close

theorem source_actualOriginalLookupRow {m} (w n i y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (actualOriginalLookupRowSentence w n i y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem y w) (Context.add (Formula.mem i w) (Context.add (Formula.mem n w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (Formula.mem n w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (Formula.mem i w) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (Formula.mem y w) := .hyp (Or.inl rfl)
  exact HornLookupRowSyntax.exists_row hZ w n i y h0 h1 h2 h3

theorem actualOriginalLookupRow_kernel_certificate {m} (w n i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (actualOriginalLookupRowSentence w n i y)) := TheoryTransport.sentence (source_actualOriginalLookupRow w n i y)

theorem native_actualOriginalLookupRow {m} (w n i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (actualOriginalLookupRowSentence w n i y)) := ZFReplay.replay (actualOriginalLookupRow_kernel_certificate w n i y)

def originalLookupRowNaturalFieldsSentence {m} (w n i y r : Fin m) : Source.Sentence := ((omega w).imp ((HornLookupRowSyntax.row w n i y r).imp (((Formula.mem n w).conj ((Formula.mem i w).conj (.mem y w)))))).close

theorem source_originalLookupRowNaturalFields {m} (w n i y r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalLookupRowNaturalFieldsSentence w n i y r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornLookupRowSyntax.row w n i y r) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (HornLookupRowSyntax.row w n i y r) := .hyp (Or.inl rfl)
  exact HornLookupRowSyntax.naturals hZ w n i y r h0 h1

theorem originalLookupRowNaturalFields_kernel_certificate {m} (w n i y r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalLookupRowNaturalFieldsSentence w n i y r)) := TheoryTransport.sentence (source_originalLookupRowNaturalFields w n i y r)

theorem native_originalLookupRowNaturalFields {m} (w n i y r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalLookupRowNaturalFieldsSentence w n i y r)) := ZFReplay.replay (originalLookupRowNaturalFields_kernel_certificate w n i y r)

def originalHeadApplicationSoundSentence {m} (w n i y r R : Fin m) : Source.Sentence := ((omega w).imp ((HornLookupRowSyntax.row w n i y r).imp ((HornApplicationSyntax.application YesMetaZFC.Automation.ObjectSyntaxTransform.lookupHead w r R).imp ((LookupTableExecutionSyntax.executed w n i y))))).close

theorem source_originalHeadApplicationSound {m} (w n i y r R : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalHeadApplicationSoundSentence w n i y r R) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornApplicationSyntax.application YesMetaZFC.Automation.ObjectSyntaxTransform.lookupHead w r R) (Context.add (HornLookupRowSyntax.row w n i y r) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornLookupRowSyntax.row w n i y r) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (HornApplicationSyntax.application YesMetaZFC.Automation.ObjectSyntaxTransform.lookupHead w r R) := .hyp (Or.inl rfl)
  exact HornLookupHeadSound.application_execution hZ w n i y r R h0 h1 h2

theorem originalHeadApplicationSound_kernel_certificate {m} (w n i y r R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalHeadApplicationSoundSentence w n i y r R)) := TheoryTransport.sentence (source_originalHeadApplicationSound w n i y r R)

theorem native_originalHeadApplicationSound {m} (w n i y r R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalHeadApplicationSoundSentence w n i y r R)) := ZFReplay.replay (originalHeadApplicationSound_kernel_certificate w n i y r R)

def arbitraryClosedInternalTraceSoundSentence {m} (w R n i y r : Fin m) : Source.Sentence := ((omega w).imp ((HornLookupSoundSyntax.closed w R).imp ((HornLookupRowSyntax.row w n i y r).imp ((Formula.mem r R).imp ((LookupTableExecutionSyntax.executed w n i y)))))).close

theorem source_arbitraryClosedInternalTraceSound {m} (w R n i y r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (arbitraryClosedInternalTraceSoundSentence w R n i y r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem r R) (Context.add (HornLookupRowSyntax.row w n i y r) (Context.add (HornLookupSoundSyntax.closed w R) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (HornLookupSoundSyntax.closed w R) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (HornLookupRowSyntax.row w n i y r) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (Formula.mem r R) := .hyp (Or.inl rfl)
  exact HornLookupSoundInduction.sound hZ w R n i y r h0 h1 h2 h3

theorem arbitraryClosedInternalTraceSound_kernel_certificate {m} (w R n i y r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (arbitraryClosedInternalTraceSoundSentence w R n i y r)) := TheoryTransport.sentence (source_arbitraryClosedInternalTraceSound w R n i y r)

theorem native_arbitraryClosedInternalTraceSound {m} (w R n i y r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (arbitraryClosedInternalTraceSoundSentence w R n i y r)) := ZFReplay.replay (arbitraryClosedInternalTraceSound_kernel_certificate w R n i y r)

def canonicalTraceActualSetSentence {m} (w : Fin m) : Source.Sentence := ((HornLookupTraceValueSyntax.existsValue w)).close

theorem source_canonicalTraceActualSet {m} (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (canonicalTraceActualSetSentence w) := by
  apply close_derives
  let Δ : Context m := Source.SetLanguage.ZF.at m
  have hZ : ZFContext.Evidence Δ := by
    exact ZFContext.source_ZF m
  exact HornLookupTraceValue.exists_value hZ w

theorem canonicalTraceActualSet_kernel_certificate {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (canonicalTraceActualSetSentence w)) := TheoryTransport.sentence (source_canonicalTraceActualSet w)

theorem native_canonicalTraceActualSet {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (canonicalTraceActualSetSentence w)) := ZFReplay.replay (canonicalTraceActualSet_kernel_certificate w)

def canonicalTraceSubsetOmegaSentence {m} (w R : Fin m) : Source.Sentence := ((HornLookupTraceValueSyntax.value w R).imp ((RestrictionSyntax.subset R w))).close

theorem source_canonicalTraceSubsetOmega {m} (w R : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (canonicalTraceSubsetOmegaSentence w R) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (HornLookupTraceValueSyntax.value w R) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (HornLookupTraceValueSyntax.value w R) := .hyp (Or.inl rfl)
  exact HornLookupTraceValue.subset w R h0

theorem canonicalTraceSubsetOmega_kernel_certificate {m} (w R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (canonicalTraceSubsetOmegaSentence w R)) := TheoryTransport.sentence (source_canonicalTraceSubsetOmega w R)

theorem native_canonicalTraceSubsetOmega {m} (w R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (canonicalTraceSubsetOmegaSentence w R)) := ZFReplay.replay (canonicalTraceSubsetOmega_kernel_certificate w R)

def canonicalTraceSuccessfulMemberSentence {m} (w R n i y r : Fin m) : Source.Sentence := ((omega w).imp ((HornLookupTraceValueSyntax.value w R).imp ((HornLookupRowSyntax.row w n i y r).imp ((LookupTableExecutionSyntax.executed w n i y).imp ((Formula.mem r R)))))).close

theorem source_canonicalTraceSuccessfulMember {m} (w R n i y r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (canonicalTraceSuccessfulMemberSentence w R n i y r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (LookupTableExecutionSyntax.executed w n i y) (Context.add (HornLookupRowSyntax.row w n i y r) (Context.add (HornLookupTraceValueSyntax.value w R) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (HornLookupTraceValueSyntax.value w R) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (HornLookupRowSyntax.row w n i y r) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (LookupTableExecutionSyntax.executed w n i y) := .hyp (Or.inl rfl)
  exact HornLookupTraceValue.successful_member hZ w R n i y r h0 h1 h2 h3

theorem canonicalTraceSuccessfulMember_kernel_certificate {m} (w R n i y r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (canonicalTraceSuccessfulMemberSentence w R n i y r)) := TheoryTransport.sentence (source_canonicalTraceSuccessfulMember w R n i y r)

theorem native_canonicalTraceSuccessfulMember {m} (w R n i y r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (canonicalTraceSuccessfulMemberSentence w R n i y r)) := ZFReplay.replay (canonicalTraceSuccessfulMember_kernel_certificate w R n i y r)

def canonicalTraceClosedSentence {m} (w R : Fin m) : Source.Sentence := ((omega w).imp ((HornLookupTraceValueSyntax.value w R).imp ((HornLookupSoundSyntax.closed w R)))).close

theorem source_canonicalTraceClosed {m} (w R : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (canonicalTraceClosedSentence w R) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornLookupTraceValueSyntax.value w R) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (HornLookupTraceValueSyntax.value w R) := .hyp (Or.inl rfl)
  exact HornLookupTraceClosed.closed hZ w R h0 h1

theorem canonicalTraceClosed_kernel_certificate {m} (w R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (canonicalTraceClosedSentence w R)) := TheoryTransport.sentence (source_canonicalTraceClosed w R)

theorem native_canonicalTraceClosed {m} (w R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (canonicalTraceClosedSentence w R)) := ZFReplay.replay (canonicalTraceClosed_kernel_certificate w R)

def compiledTraceCompleteSentence {m} (w n i y r : Fin m) : Source.Sentence := ((omega w).imp ((HornLookupRowSyntax.row w n i y r).imp ((LookupTableExecutionSyntax.executed w n i y).imp ((HornLookupConditionSyntax.condition w r))))).close

theorem source_compiledTraceComplete {m} (w n i y r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (compiledTraceCompleteSentence w n i y r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (LookupTableExecutionSyntax.executed w n i y) (Context.add (HornLookupRowSyntax.row w n i y r) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornLookupRowSyntax.row w n i y r) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (LookupTableExecutionSyntax.executed w n i y) := .hyp (Or.inl rfl)
  exact HornLookupCondition.complete hZ w n i y r h0 h1 h2

theorem compiledTraceComplete_kernel_certificate {m} (w n i y r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (compiledTraceCompleteSentence w n i y r)) := TheoryTransport.sentence (source_compiledTraceComplete w n i y r)

theorem native_compiledTraceComplete {m} (w n i y r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (compiledTraceCompleteSentence w n i y r)) := ZFReplay.replay (compiledTraceComplete_kernel_certificate w n i y r)

def compiledTraceExecutionIffSentence {m} (w n i y r : Fin m) : Source.Sentence := ((omega w).imp ((HornLookupRowSyntax.row w n i y r).imp (((HornLookupConditionSyntax.condition w r).iff (LookupTableExecutionSyntax.executed w n i y))))).close

theorem source_compiledTraceExecutionIff {m} (w n i y r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (compiledTraceExecutionIffSentence w n i y r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornLookupRowSyntax.row w n i y r) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (HornLookupRowSyntax.row w n i y r) := .hyp (Or.inl rfl)
  exact HornLookupCondition.execution_iff hZ w n i y r h0 h1

theorem compiledTraceExecutionIff_kernel_certificate {m} (w n i y r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (compiledTraceExecutionIffSentence w n i y r)) := TheoryTransport.sentence (source_compiledTraceExecutionIff w n i y r)

theorem native_compiledTraceExecutionIff {m} (w n i y r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (compiledTraceExecutionIffSentence w n i y r)) := ZFReplay.replay (compiledTraceExecutionIff_kernel_certificate w n i y r)

def compiledTraceCandidateRejectionIffSentence {m} (w n i y r : Fin m) : Source.Sentence := ((omega w).imp ((HornLookupRowSyntax.row w n i y r).imp (((HornLookupConditionSyntax.condition w r).neg.iff (LookupTableExecutionSyntax.executed w n i y).neg)))).close

theorem source_compiledTraceCandidateRejectionIff {m} (w n i y r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (compiledTraceCandidateRejectionIffSentence w n i y r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornLookupRowSyntax.row w n i y r) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (HornLookupRowSyntax.row w n i y r) := .hyp (Or.inl rfl)
  exact HornLookupCondition.rejected_iff hZ w n i y r h0 h1

theorem compiledTraceCandidateRejectionIff_kernel_certificate {m} (w n i y r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (compiledTraceCandidateRejectionIffSentence w n i y r)) := TheoryTransport.sentence (source_compiledTraceCandidateRejectionIff w n i y r)

theorem native_compiledTraceCandidateRejectionIff {m} (w n i y r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (compiledTraceCandidateRejectionIffSentence w n i y r)) := ZFReplay.replay (compiledTraceCandidateRejectionIff_kernel_certificate w n i y r)

def originalBoundedSearchClosureIffSentence {m} (w R : Fin m) : Source.Sentence := ((omega w).imp ((RestrictionSyntax.subset R w).imp (((HornLookupSoundSyntax.closed w R).iff (HornLookupSearchCondition.closed w R))))).close

theorem source_originalBoundedSearchClosureIff {m} (w R : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalBoundedSearchClosureIffSentence w R) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (RestrictionSyntax.subset R w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (RestrictionSyntax.subset R w) := .hyp (Or.inl rfl)
  exact HornLookupSearchCondition.closed_iff hZ w R h0 h1

theorem originalBoundedSearchClosureIff_kernel_certificate {m} (w R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalBoundedSearchClosureIffSentence w R)) := TheoryTransport.sentence (source_originalBoundedSearchClosureIff w R)

theorem native_originalBoundedSearchClosureIff {m} (w R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalBoundedSearchClosureIffSentence w R)) := ZFReplay.replay (originalBoundedSearchClosureIff_kernel_certificate w R)

def originalBoundedSearchTraceIffSentence {m} (w r : Fin m) : Source.Sentence := ((omega w).imp (((HornLookupConditionSyntax.condition w r).iff (HornLookupSearchCondition.condition w r)))).close

theorem source_originalBoundedSearchTraceIff {m} (w r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalBoundedSearchTraceIffSentence w r) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact HornLookupSearchCondition.condition_iff hZ w r h0

theorem originalBoundedSearchTraceIff_kernel_certificate {m} (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalBoundedSearchTraceIffSentence w r)) := TheoryTransport.sentence (source_originalBoundedSearchTraceIff w r)

theorem native_originalBoundedSearchTraceIff {m} (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalBoundedSearchTraceIffSentence w r)) := ZFReplay.replay (originalBoundedSearchTraceIff_kernel_certificate w r)

def originalBoundedSearchTraceExecutionIffSentence {m} (w n i y r : Fin m) : Source.Sentence := ((omega w).imp ((HornLookupRowSyntax.row w n i y r).imp (((HornLookupSearchCondition.condition w r).iff (LookupTableExecutionSyntax.executed w n i y))))).close

theorem source_originalBoundedSearchTraceExecutionIff {m} (w n i y r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalBoundedSearchTraceExecutionIffSentence w n i y r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornLookupRowSyntax.row w n i y r) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (HornLookupRowSyntax.row w n i y r) := .hyp (Or.inl rfl)
  exact HornLookupSearchCondition.execution_iff hZ w n i y r h0 h1

theorem originalBoundedSearchTraceExecutionIff_kernel_certificate {m} (w n i y r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalBoundedSearchTraceExecutionIffSentence w n i y r)) := TheoryTransport.sentence (source_originalBoundedSearchTraceExecutionIff w n i y r)

theorem native_originalBoundedSearchTraceExecutionIff {m} (w n i y r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalBoundedSearchTraceExecutionIffSentence w n i y r)) := ZFReplay.replay (originalBoundedSearchTraceExecutionIff_kernel_certificate w n i y r)

def actualPowerTraceDomainIffSentence {m} (w r P : Fin m) : Source.Sentence := ((PowerSetSyntax.powerOf P w).imp (((HornLookupPowerCondition.atPower w r P).iff (HornLookupSearchCondition.condition w r)))).close

theorem source_actualPowerTraceDomainIff {m} (w r P : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (actualPowerTraceDomainIffSentence w r P) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (PowerSetSyntax.powerOf P w) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (PowerSetSyntax.powerOf P w) := .hyp (Or.inl rfl)
  exact HornLookupPowerCondition.at_power_iff w r P h0

theorem actualPowerTraceDomainIff_kernel_certificate {m} (w r P : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (actualPowerTraceDomainIffSentence w r P)) := TheoryTransport.sentence (source_actualPowerTraceDomainIff w r P)

theorem native_actualPowerTraceDomainIff {m} (w r P : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (actualPowerTraceDomainIffSentence w r P)) := ZFReplay.replay (actualPowerTraceDomainIff_kernel_certificate w r P)

def actualPowerTraceSearchIffSentence {m} (w r : Fin m) : Source.Sentence := (((HornLookupPowerCondition.condition w r).iff (HornLookupSearchCondition.condition w r))).close

theorem source_actualPowerTraceSearchIff {m} (w r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (actualPowerTraceSearchIffSentence w r) := by
  apply close_derives
  let Δ : Context m := Source.SetLanguage.ZF.at m
  have hZ : ZFContext.Evidence Δ := by
    exact ZFContext.source_ZF m
  exact HornLookupPowerCondition.search_condition_iff hZ w r

theorem actualPowerTraceSearchIff_kernel_certificate {m} (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (actualPowerTraceSearchIffSentence w r)) := TheoryTransport.sentence (source_actualPowerTraceSearchIff w r)

theorem native_actualPowerTraceSearchIff {m} (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (actualPowerTraceSearchIffSentence w r)) := ZFReplay.replay (actualPowerTraceSearchIff_kernel_certificate w r)

def actualPowerTraceExecutionIffSentence {m} (w n i y r : Fin m) : Source.Sentence := ((omega w).imp ((HornLookupRowSyntax.row w n i y r).imp (((HornLookupPowerCondition.condition w r).iff (LookupTableExecutionSyntax.executed w n i y))))).close

theorem source_actualPowerTraceExecutionIff {m} (w n i y r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (actualPowerTraceExecutionIffSentence w n i y r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornLookupRowSyntax.row w n i y r) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (HornLookupRowSyntax.row w n i y r) := .hyp (Or.inl rfl)
  exact HornLookupPowerCondition.execution_iff hZ w n i y r h0 h1

theorem actualPowerTraceExecutionIff_kernel_certificate {m} (w n i y r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (actualPowerTraceExecutionIffSentence w n i y r)) := TheoryTransport.sentence (source_actualPowerTraceExecutionIff w n i y r)

theorem native_actualPowerTraceExecutionIff {m} (w n i y r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (actualPowerTraceExecutionIffSentence w n i y r)) := ZFReplay.replay (actualPowerTraceExecutionIff_kernel_certificate w n i y r)

def allInternalTraceSomeExecutionIffSentence {m} (w n i y : Fin m) : Source.Sentence := ((omega w).imp (((HornLookupSomeSyntax.returned w n i y).iff (LookupTableExecutionSyntax.executed w n i y)))).close

theorem source_allInternalTraceSomeExecutionIff {m} (w n i y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (allInternalTraceSomeExecutionIffSentence w n i y) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact HornLookupSome.execution_iff hZ w n i y h0

theorem allInternalTraceSomeExecutionIff_kernel_certificate {m} (w n i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (allInternalTraceSomeExecutionIffSentence w n i y)) := TheoryTransport.sentence (source_allInternalTraceSomeExecutionIff w n i y)

theorem native_allInternalTraceSomeExecutionIff {m} (w n i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (allInternalTraceSomeExecutionIffSentence w n i y)) := ZFReplay.replay (allInternalTraceSomeExecutionIff_kernel_certificate w n i y)

def allInternalTraceSomeCheckedIffSentence {m} (w n i y : Fin m) : Source.Sentence := ((omega w).imp (((HornLookupSomeSyntax.returned w n i y).iff (StrictLookupSyntax.checked w n i y)))).close

theorem source_allInternalTraceSomeCheckedIff {m} (w n i y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (allInternalTraceSomeCheckedIffSentence w n i y) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact HornLookupSome.checked_iff hZ w n i y h0

theorem allInternalTraceSomeCheckedIff_kernel_certificate {m} (w n i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (allInternalTraceSomeCheckedIffSentence w n i y)) := TheoryTransport.sentence (source_allInternalTraceSomeCheckedIff w n i y)

theorem native_allInternalTraceSomeCheckedIff {m} (w n i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (allInternalTraceSomeCheckedIffSentence w n i y)) := ZFReplay.replay (allInternalTraceSomeCheckedIff_kernel_certificate w n i y)

def naturalTraceSomeRawLookupIffSentence {m} (w n i y : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem n w).imp ((Formula.mem i w).imp (((HornLookupSomeSyntax.returned w n i y).iff (StrictLookupSyntax.returned w n i y)))))).close

theorem source_naturalTraceSomeRawLookupIff {m} (w n i y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (naturalTraceSomeRawLookupIffSentence w n i y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem i w) (Context.add (Formula.mem n w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (Formula.mem n w) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (Formula.mem i w) := .hyp (Or.inl rfl)
  exact HornLookupSomeValue.raw_iff hZ w n i y h0 h1 h2

theorem naturalTraceSomeRawLookupIff_kernel_certificate {m} (w n i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (naturalTraceSomeRawLookupIffSentence w n i y)) := TheoryTransport.sentence (source_naturalTraceSomeRawLookupIff w n i y)

theorem native_naturalTraceSomeRawLookupIff {m} (w n i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (naturalTraceSomeRawLookupIffSentence w n i y)) := ZFReplay.replay (naturalTraceSomeRawLookupIff_kernel_certificate w n i y)

def allInternalTraceHasOutputIffSentence {m} (w n i : Fin m) : Source.Sentence := ((omega w).imp (((HornLookupSomeSyntax.hasOutput w n i).iff (LookupTableOutcomeSyntax.hasOutput w n i)))).close

theorem source_allInternalTraceHasOutputIff {m} (w n i : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (allInternalTraceHasOutputIffSentence w n i) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact HornLookupSome.has_output_iff hZ w n i h0

theorem allInternalTraceHasOutputIff_kernel_certificate {m} (w n i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (allInternalTraceHasOutputIffSentence w n i)) := TheoryTransport.sentence (source_allInternalTraceHasOutputIff w n i)

theorem native_allInternalTraceHasOutputIff {m} (w n i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (allInternalTraceHasOutputIffSentence w n i)) := ZFReplay.replay (allInternalTraceHasOutputIff_kernel_certificate w n i)

def allInternalTraceNoOutputIffSentence {m} (w n i : Fin m) : Source.Sentence := ((omega w).imp (((HornLookupSomeSyntax.noOutput w n i).iff (LookupTableOutcomeSyntax.noOutput w n i)))).close

theorem source_allInternalTraceNoOutputIff {m} (w n i : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (allInternalTraceNoOutputIffSentence w n i) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact HornLookupSome.no_output_iff hZ w n i h0

theorem allInternalTraceNoOutputIff_kernel_certificate {m} (w n i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (allInternalTraceNoOutputIffSentence w n i)) := TheoryTransport.sentence (source_allInternalTraceNoOutputIff w n i)

theorem native_allInternalTraceNoOutputIff {m} (w n i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (allInternalTraceNoOutputIffSentence w n i)) := ZFReplay.replay (allInternalTraceNoOutputIff_kernel_certificate w n i)

def naturalTraceHasOutputStrictIffSentence {m} (w n i : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem n w).imp ((Formula.mem i w).imp (((HornLookupSomeSyntax.hasOutput w n i).iff (StrictLookupSyntax.hasOutput w n i)))))).close

theorem source_naturalTraceHasOutputStrictIff {m} (w n i : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (naturalTraceHasOutputStrictIffSentence w n i) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem i w) (Context.add (Formula.mem n w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (Formula.mem n w) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (Formula.mem i w) := .hyp (Or.inl rfl)
  exact HornLookupSomeValue.has_output_iff hZ w n i h0 h1 h2

theorem naturalTraceHasOutputStrictIff_kernel_certificate {m} (w n i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (naturalTraceHasOutputStrictIffSentence w n i)) := TheoryTransport.sentence (source_naturalTraceHasOutputStrictIff w n i)

theorem native_naturalTraceHasOutputStrictIff {m} (w n i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (naturalTraceHasOutputStrictIffSentence w n i)) := ZFReplay.replay (naturalTraceHasOutputStrictIff_kernel_certificate w n i)

def naturalTraceNoOutputStrictIffSentence {m} (w n i : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem n w).imp ((Formula.mem i w).imp (((HornLookupSomeSyntax.noOutput w n i).iff (StrictLookupSyntax.rejected w n i)))))).close

theorem source_naturalTraceNoOutputStrictIff {m} (w n i : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (naturalTraceNoOutputStrictIffSentence w n i) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem i w) (Context.add (Formula.mem n w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (Formula.mem n w) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (Formula.mem i w) := .hyp (Or.inl rfl)
  exact HornLookupSome.strict_no_output_iff hZ w n i h0 h1 h2

theorem naturalTraceNoOutputStrictIff_kernel_certificate {m} (w n i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (naturalTraceNoOutputStrictIffSentence w n i)) := TheoryTransport.sentence (source_naturalTraceNoOutputStrictIff w n i)

theorem native_naturalTraceNoOutputStrictIff {m} (w n i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (naturalTraceNoOutputStrictIffSentence w n i)) := ZFReplay.replay (naturalTraceNoOutputStrictIff_kernel_certificate w n i)

def allInternalTraceOutputUniqueSentence {m} (w n i y z : Fin m) : Source.Sentence := ((omega w).imp ((HornLookupSomeSyntax.returned w n i y).imp ((HornLookupSomeSyntax.returned w n i z).imp ((Formula.equal y z))))).close

theorem source_allInternalTraceOutputUnique {m} (w n i y z : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (allInternalTraceOutputUniqueSentence w n i y z) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornLookupSomeSyntax.returned w n i z) (Context.add (HornLookupSomeSyntax.returned w n i y) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornLookupSomeSyntax.returned w n i y) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (HornLookupSomeSyntax.returned w n i z) := .hyp (Or.inl rfl)
  exact HornLookupSomeValue.unique hZ w n i y z h0 h1 h2

theorem allInternalTraceOutputUnique_kernel_certificate {m} (w n i y z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (allInternalTraceOutputUniqueSentence w n i y z)) := TheoryTransport.sentence (source_allInternalTraceOutputUnique w n i y z)

theorem native_allInternalTraceOutputUnique {m} (w n i y z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (allInternalTraceOutputUniqueSentence w n i y z)) := ZFReplay.replay (allInternalTraceOutputUnique_kernel_certificate w n i y z)

end PPAC.Migration.Internal.ObjectLookupTrace
