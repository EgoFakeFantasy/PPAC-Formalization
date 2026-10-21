import PPAC.Migration.Internal.StructuralListCheckCorrectness

/-! 全内部自然码的实际递归列表检查、唯一性及接受/拒绝正确性的原核完整闭句。 -/
namespace PPAC.Migration.Internal.ObjectStructuralListCheck
open Source SourceAlgebra SourceLogic OmegaSyntax StructuralListSyntax StructuralListProjectionSyntax StructuralListCheckSyntax
open StructuralListTraceSyntax (valid)

def terminationSentence : Source.Sentence := ((((omega 0).imp ((Formula.mem 1 0).imp (eventually 0 1))) : Formula 2)).close

def existsSentence : Source.Sentence := ((((omega 0).imp ((Formula.mem 1 0).imp (hasCheck 0 1))) : Formula 2)).close

def fiberSentence : Source.Sentence := ((((omega 0).imp ((Formula.mem 1 0).imp (checkFiber 0 1))) : Formula 2)).close

def indexUniqueSentence : Source.Sentence := ((((omega 0).imp ((checkedAt 0 1 2 4).imp ((checkedAt 0 1 3 5).imp (Formula.equal 2 3)))) : Formula 6)).close

def valueUniqueSentence : Source.Sentence := ((((omega 0).imp ((checkValue 0 1 2).imp ((checkValue 0 1 3).imp (Formula.equal 2 3)))) : Formula 4)).close

def preservesStepSentence : Source.Sentence := ((((omega 0).imp (((terminal 0 1).neg).imp ((step false 0 1 2).imp ((valid 0 1).iff (valid 0 2))))) : Formula 3)).close

def invariantSentence : Source.Sentence := ((((omega 0).imp ((Formula.mem 2 0).imp (StructuralListCheckInvariantSyntax.invariant 0 1 2))) : Formula 3)).close

def acceptValueSentence : Source.Sentence := ((((omega 0).imp ((checkValue 0 1 2).imp ((valid 0 1).iff (nilCode 0 2)))) : Formula 3)).close

def rejectValueSentence : Source.Sentence := ((((omega 0).imp ((checkValue 0 1 2).imp ((empty 2).iff (valid 0 1).neg))) : Formula 3)).close

def acceptsIffSentence : Source.Sentence := ((((omega 0).imp ((Formula.mem 1 0).imp ((valid 0 1).iff (accepts 0 1)))) : Formula 2)).close

def rejectsIffSentence : Source.Sentence := ((((omega 0).imp ((Formula.mem 1 0).imp ((valid 0 1).neg.iff (rejects 0 1)))) : Formula 2)).close

def exclusiveSentence : Source.Sentence := ((((omega 0).imp ((accepts 0 1).imp ((rejects 0 1).imp (Formula.bot)))) : Formula 2)).close

def decodeAcceptedSentence : Source.Sentence := ((((omega 0).imp ((accepts 0 1).imp (StructuralListFieldGraphSyntax.decoded 0 1))) : Formula 2)).close

def nilAcceptsSentence : Source.Sentence := ((((omega 0).imp ((nilCode 0 1).imp (accepts 0 1))) : Formula 2)).close

def zeroRejectsSentence : Source.Sentence := ((((omega 0).imp ((empty 1).imp (rejects 0 1))) : Formula 2)).close

def classificationSentence : Source.Sentence := ((((omega 0).imp ((Formula.mem 1 0).imp ((accepts 0 1).disj (rejects 0 1)))) : Formula 2)).close

theorem source_termination : Derives (Source.SetLanguage.ZF.at 0) terminationSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 2 := (Context.add (Formula.mem 1 0) (Context.add (omega 0) (Source.SetLanguage.ZF.at 2)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 2
  exact StructuralListCheckTermination.at_code hZ 0 1 (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem termination_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence terminationSentence) := TheoryTransport.sentence source_termination

theorem native_termination : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence terminationSentence) := ZFReplay.replay termination_kernel_certificate

theorem source_exists : Derives (Source.SetLanguage.ZF.at 0) existsSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 2 := (Context.add (Formula.mem 1 0) (Context.add (omega 0) (Source.SetLanguage.ZF.at 2)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 2
  exact StructuralListCheckMinimal.exists_check hZ 0 1 (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem exists_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence existsSentence) := TheoryTransport.sentence source_exists

theorem native_exists : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence existsSentence) := ZFReplay.replay exists_kernel_certificate

theorem source_fiber : Derives (Source.SetLanguage.ZF.at 0) fiberSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 2 := (Context.add (Formula.mem 1 0) (Context.add (omega 0) (Source.SetLanguage.ZF.at 2)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 2
  exact StructuralListCheckUnique.exists_unique hZ 0 1 (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem fiber_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence fiberSentence) := TheoryTransport.sentence source_fiber

theorem native_fiber : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence fiberSentence) := ZFReplay.replay fiber_kernel_certificate

theorem source_indexUnique : Derives (Source.SetLanguage.ZF.at 0) indexUniqueSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 6 := (Context.add (checkedAt 0 1 3 5) (Context.add (checkedAt 0 1 2 4) (Context.add (omega 0) (Source.SetLanguage.ZF.at 6))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 6
  exact StructuralListCheckUnique.index_unique hZ 0 1 2 3 4 5 (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem indexUnique_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence indexUniqueSentence) := TheoryTransport.sentence source_indexUnique

theorem native_indexUnique : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence indexUniqueSentence) := ZFReplay.replay indexUnique_kernel_certificate

theorem source_valueUnique : Derives (Source.SetLanguage.ZF.at 0) valueUniqueSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 4 := (Context.add (checkValue 0 1 3) (Context.add (checkValue 0 1 2) (Context.add (omega 0) (Source.SetLanguage.ZF.at 4))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 4
  exact StructuralListCheckUnique.value_unique hZ 0 1 2 3 (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem valueUnique_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence valueUniqueSentence) := TheoryTransport.sentence source_valueUnique

theorem native_valueUnique : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence valueUniqueSentence) := ZFReplay.replay valueUnique_kernel_certificate

theorem source_preservesStep : Derives (Source.SetLanguage.ZF.at 0) preservesStepSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 3 := (Context.add (step false 0 1 2) (Context.add ((terminal 0 1).neg) (Context.add (omega 0) (Source.SetLanguage.ZF.at 3))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 3
  exact StructuralListCheckPreservationStep.preserve hZ 0 1 2 (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem preservesStep_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence preservesStepSentence) := TheoryTransport.sentence source_preservesStep

theorem native_preservesStep : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence preservesStepSentence) := ZFReplay.replay preservesStep_kernel_certificate

theorem source_invariant : Derives (Source.SetLanguage.ZF.at 0) invariantSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 3 := (Context.add (Formula.mem 2 0) (Context.add (omega 0) (Source.SetLanguage.ZF.at 3)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 3
  exact StructuralListCheckInvariant.at_index hZ 0 1 2 (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem invariant_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence invariantSentence) := TheoryTransport.sentence source_invariant

theorem native_invariant : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence invariantSentence) := ZFReplay.replay invariant_kernel_certificate

theorem source_acceptValue : Derives (Source.SetLanguage.ZF.at 0) acceptValueSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 3 := (Context.add (checkValue 0 1 2) (Context.add (omega 0) (Source.SetLanguage.ZF.at 3)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 3
  exact StructuralListCheckCorrectness.correct_value hZ 0 1 2 (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem acceptValue_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence acceptValueSentence) := TheoryTransport.sentence source_acceptValue

theorem native_acceptValue : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence acceptValueSentence) := ZFReplay.replay acceptValue_kernel_certificate

theorem source_rejectValue : Derives (Source.SetLanguage.ZF.at 0) rejectValueSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 3 := (Context.add (checkValue 0 1 2) (Context.add (omega 0) (Source.SetLanguage.ZF.at 3)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 3
  exact StructuralListCheckCorrectness.reject_value hZ 0 1 2 (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem rejectValue_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence rejectValueSentence) := TheoryTransport.sentence source_rejectValue

theorem native_rejectValue : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence rejectValueSentence) := ZFReplay.replay rejectValue_kernel_certificate

theorem source_acceptsIff : Derives (Source.SetLanguage.ZF.at 0) acceptsIffSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 2 := (Context.add (Formula.mem 1 0) (Context.add (omega 0) (Source.SetLanguage.ZF.at 2)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 2
  exact StructuralListCheckCorrectness.accepts_iff hZ 0 1 (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem acceptsIff_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence acceptsIffSentence) := TheoryTransport.sentence source_acceptsIff

theorem native_acceptsIff : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence acceptsIffSentence) := ZFReplay.replay acceptsIff_kernel_certificate

theorem source_rejectsIff : Derives (Source.SetLanguage.ZF.at 0) rejectsIffSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 2 := (Context.add (Formula.mem 1 0) (Context.add (omega 0) (Source.SetLanguage.ZF.at 2)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 2
  exact StructuralListCheckCorrectness.rejects_iff hZ 0 1 (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem rejectsIff_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence rejectsIffSentence) := TheoryTransport.sentence source_rejectsIff

theorem native_rejectsIff : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence rejectsIffSentence) := ZFReplay.replay rejectsIff_kernel_certificate

theorem source_exclusive : Derives (Source.SetLanguage.ZF.at 0) exclusiveSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 2 := (Context.add (rejects 0 1) (Context.add (accepts 0 1) (Context.add (omega 0) (Source.SetLanguage.ZF.at 2))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 2
  exact StructuralListCheckCorrectness.exclusive hZ 0 1 (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem exclusive_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence exclusiveSentence) := TheoryTransport.sentence source_exclusive

theorem native_exclusive : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence exclusiveSentence) := ZFReplay.replay exclusive_kernel_certificate

theorem source_decodeAccepted : Derives (Source.SetLanguage.ZF.at 0) decodeAcceptedSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 2 := (Context.add (accepts 0 1) (Context.add (omega 0) (Source.SetLanguage.ZF.at 2)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 2
  exact StructuralListCheckCorrectness.decode_accepted hZ 0 1 (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem decodeAccepted_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence decodeAcceptedSentence) := TheoryTransport.sentence source_decodeAccepted

theorem native_decodeAccepted : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence decodeAcceptedSentence) := ZFReplay.replay decodeAccepted_kernel_certificate

theorem source_nilAccepts : Derives (Source.SetLanguage.ZF.at 0) nilAcceptsSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 2 := (Context.add (nilCode 0 1) (Context.add (omega 0) (Source.SetLanguage.ZF.at 2)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 2
  exact StructuralListCheckCorrectness.nil_accepts hZ 0 1 (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem nilAccepts_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence nilAcceptsSentence) := TheoryTransport.sentence source_nilAccepts

theorem native_nilAccepts : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence nilAcceptsSentence) := ZFReplay.replay nilAccepts_kernel_certificate

theorem source_zeroRejects : Derives (Source.SetLanguage.ZF.at 0) zeroRejectsSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 2 := (Context.add (empty 1) (Context.add (omega 0) (Source.SetLanguage.ZF.at 2)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 2
  exact StructuralListCheckCorrectness.zero_rejects hZ 0 1 (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem zeroRejects_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence zeroRejectsSentence) := TheoryTransport.sentence source_zeroRejects

theorem native_zeroRejects : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence zeroRejectsSentence) := ZFReplay.replay zeroRejects_kernel_certificate

theorem source_classification : Derives (Source.SetLanguage.ZF.at 0) classificationSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 2 := (Context.add (Formula.mem 1 0) (Context.add (omega 0) (Source.SetLanguage.ZF.at 2)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 2
  exact StructuralListCheckCorrectness.classification hZ 0 1 (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem classification_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence classificationSentence) := TheoryTransport.sentence source_classification

theorem native_classification : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence classificationSentence) := ZFReplay.replay classification_kernel_certificate

end PPAC.Migration.Internal.ObjectStructuralListCheck
