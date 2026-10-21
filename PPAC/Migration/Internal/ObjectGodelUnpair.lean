import PPAC.Migration.Internal.GodelUnpairUnique

/-! 全内部自然码的解码总性、精确唯一性及范围界的原核闭句。 -/
namespace PPAC.Migration.Internal.ObjectGodelUnpair
open Source SourceAlgebra SourceLogic OmegaSyntax GodelUnpairSyntax

def zeroSentence : Source.Sentence := ((omega (0 : Fin 2)).imp ((empty 1).imp (preimage 0 1))).close

def successorSentence : Source.Sentence := ((omega (0 : Fin 3)).imp ((preimage 0 1).imp ((successor 2 1).imp (preimage 0 2)))).close

def totalSentence : Source.Sentence := ((omega (0 : Fin 2)).imp ((Formula.mem 1 0).imp (preimage 0 1))).close

def characterizationSentence : Source.Sentence := ((omega (0 : Fin 4)).imp ((witness 0 1 2 3).imp (exactAt 0 1 2 3))).close

def fiberSentence : Source.Sentence := ((omega (0 : Fin 2)).imp ((Formula.mem 1 0).imp (GodelUnpairSyntax.fiber 0 1))).close

def boundedSentence : Source.Sentence := ((omega (0 : Fin 2)).imp ((Formula.mem 1 0).imp (boundedFiber 0 1))).close

theorem source_zero : Derives (Source.SetLanguage.ZF.at 0) zeroSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 2 := (Context.add (empty 1) (Context.add (omega 0) (Source.SetLanguage.ZF.at 2)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 2
  exact GodelUnpairExistence.zero_preimage hZ 0 1
    (.hyp (Or.inr (Or.inl rfl)))
    (.hyp (Or.inl rfl))

theorem zero_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence zeroSentence) := TheoryTransport.sentence source_zero

theorem native_zero : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence zeroSentence) :=
  ZFReplay.replay zero_kernel_certificate

theorem source_successor : Derives (Source.SetLanguage.ZF.at 0) successorSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 3 := (Context.add (successor 2 1) (Context.add (preimage 0 1) (Context.add (omega 0) (Source.SetLanguage.ZF.at 3))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 3
  exact GodelUnpairStep.successor_preimage hZ 0 1 2
    (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inr (Or.inl rfl)))
    (.hyp (Or.inl rfl))

theorem successor_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence successorSentence) := TheoryTransport.sentence source_successor

theorem native_successor : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence successorSentence) :=
  ZFReplay.replay successor_kernel_certificate

theorem source_total : Derives (Source.SetLanguage.ZF.at 0) totalSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 2 := (Context.add (Formula.mem 1 0) (Context.add (omega 0) (Source.SetLanguage.ZF.at 2)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 2
  exact GodelUnpairExistence.preimage_exists hZ 0 1
    (.hyp (Or.inr (Or.inl rfl)))
    (.hyp (Or.inl rfl))

theorem total_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence totalSentence) := TheoryTransport.sentence source_total

theorem native_total : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence totalSentence) :=
  ZFReplay.replay total_kernel_certificate

theorem source_characterization : Derives (Source.SetLanguage.ZF.at 0) characterizationSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 4 := (Context.add (witness 0 1 2 3) (Context.add (omega 0) (Source.SetLanguage.ZF.at 4)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 4
  exact GodelUnpairUnique.exact_at hZ 0 1 2 3
    (.hyp (Or.inr (Or.inl rfl)))
    (.hyp (Or.inl rfl))

theorem characterization_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence characterizationSentence) := TheoryTransport.sentence source_characterization

theorem native_characterization : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence characterizationSentence) :=
  ZFReplay.replay characterization_kernel_certificate

theorem source_fiber : Derives (Source.SetLanguage.ZF.at 0) fiberSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 2 := (Context.add (Formula.mem 1 0) (Context.add (omega 0) (Source.SetLanguage.ZF.at 2)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 2
  exact GodelUnpairUnique.unique_fiber hZ 0 1
    (.hyp (Or.inr (Or.inl rfl)))
    (.hyp (Or.inl rfl))

theorem fiber_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence fiberSentence) := TheoryTransport.sentence source_fiber

theorem native_fiber : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence fiberSentence) :=
  ZFReplay.replay fiber_kernel_certificate

theorem source_bounded : Derives (Source.SetLanguage.ZF.at 0) boundedSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 2 := (Context.add (Formula.mem 1 0) (Context.add (omega 0) (Source.SetLanguage.ZF.at 2)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 2
  exact GodelUnpairUnique.bounded_fiber hZ 0 1
    (.hyp (Or.inr (Or.inl rfl)))
    (.hyp (Or.inl rfl))

theorem bounded_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence boundedSentence) := TheoryTransport.sentence source_bounded

theorem native_bounded : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence boundedSentence) :=
  ZFReplay.replay bounded_kernel_certificate

end PPAC.Migration.Internal.ObjectGodelUnpair
