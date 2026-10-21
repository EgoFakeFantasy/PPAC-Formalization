import PPAC.Migration.Internal.NaturalMultiplicationOrderLaws
import PPAC.Migration.Internal.ObjectNaturalAdditiveOrder

namespace PPAC.Migration.Internal.ObjectNaturalMultiplicativeOrder
open Source SourceAlgebra SourceLogic OmegaSyntax
open NaturalAdditionSyntax (sum)
open NaturalMultiplicationSyntax (product)
open NaturalAdditionBounds (below)

def zeroSentence : Source.Sentence := ((omega (0 : Fin 4)).imp
  ((Formula.mem 1 0).imp
  ((Formula.mem 2 0).imp
  ((product 0 1 2 3).imp
  (((empty 3).iff ((empty 1).disj (empty 2)))))))).close

def rightMonotoneSentence : Source.Sentence := ((omega (0 : Fin 6)).imp
  ((Formula.mem 1 0).imp
  ((Formula.mem 2 0).imp
  ((Formula.mem 3 0).imp
  ((product 0 1 3 4).imp
  ((product 0 2 3 5).imp
  ((below 1 2).imp
  ((below 4 5))))))))).close

def rightWeakSentence : Source.Sentence := ((omega (0 : Fin 6)).imp
  ((Formula.mem 1 0).imp
  ((Formula.mem 2 0).imp
  ((Formula.mem 3 0).imp
  (((empty 3).neg).imp
  ((product 0 1 3 4).imp
  ((product 0 2 3 5).imp
  (((below 1 2).iff (below 4 5)))))))))).close

def rightStrictSentence : Source.Sentence := ((omega (0 : Fin 6)).imp
  ((Formula.mem 1 0).imp
  ((Formula.mem 2 0).imp
  ((Formula.mem 3 0).imp
  (((empty 3).neg).imp
  ((product 0 1 3 4).imp
  ((product 0 2 3 5).imp
  (((Formula.mem 1 2).iff (.mem 4 5)))))))))).close

def rightCancelSentence : Source.Sentence := ((omega (0 : Fin 5)).imp
  ((Formula.mem 1 0).imp
  ((Formula.mem 2 0).imp
  ((Formula.mem 3 0).imp
  (((empty 3).neg).imp
  ((product 0 1 3 4).imp
  ((product 0 2 3 4).imp
  ((Formula.equal 1 2))))))))).close

def leftMonotoneSentence : Source.Sentence := ((omega (0 : Fin 6)).imp
  ((Formula.mem 1 0).imp
  ((Formula.mem 2 0).imp
  ((Formula.mem 3 0).imp
  ((product 0 3 1 4).imp
  ((product 0 3 2 5).imp
  ((below 1 2).imp
  ((below 4 5))))))))).close

def leftWeakSentence : Source.Sentence := ((omega (0 : Fin 6)).imp
  ((Formula.mem 1 0).imp
  ((Formula.mem 2 0).imp
  ((Formula.mem 3 0).imp
  (((empty 3).neg).imp
  ((product 0 3 1 4).imp
  ((product 0 3 2 5).imp
  (((below 1 2).iff (below 4 5)))))))))).close

def leftStrictSentence : Source.Sentence := ((omega (0 : Fin 6)).imp
  ((Formula.mem 1 0).imp
  ((Formula.mem 2 0).imp
  ((Formula.mem 3 0).imp
  (((empty 3).neg).imp
  ((product 0 3 1 4).imp
  ((product 0 3 2 5).imp
  (((Formula.mem 1 2).iff (.mem 4 5)))))))))).close

def leftCancelSentence : Source.Sentence := ((omega (0 : Fin 5)).imp
  ((Formula.mem 1 0).imp
  ((Formula.mem 2 0).imp
  ((Formula.mem 3 0).imp
  (((empty 3).neg).imp
  ((product 0 3 1 4).imp
  ((product 0 3 2 4).imp
  ((Formula.equal 1 2))))))))).close

theorem source_zero : Derives (Source.SetLanguage.ZF.at 0) zeroSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 4 :=
    (Context.add (product 0 1 2 3)
    (Context.add (Formula.mem 2 0)
    (Context.add (Formula.mem 1 0)
    (Context.add (omega 0)
    (Source.SetLanguage.ZF.at 4)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 4
  exact NaturalMultiplicationPositive.zero_iff hZ 0 1 2 3
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inr (Or.inl rfl)))
    (.hyp (Or.inl rfl))

theorem zero_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence zeroSentence) := TheoryTransport.sentence source_zero
theorem native_zero : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence zeroSentence) :=
  ZFReplay.replay zero_kernel_certificate

theorem source_rightMonotone : Derives (Source.SetLanguage.ZF.at 0) rightMonotoneSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 6 :=
    (Context.add (below 1 2)
    (Context.add (product 0 2 3 5)
    (Context.add (product 0 1 3 4)
    (Context.add (Formula.mem 3 0)
    (Context.add (Formula.mem 2 0)
    (Context.add (Formula.mem 1 0)
    (Context.add (omega 0)
    (Source.SetLanguage.ZF.at 6))))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 6
  exact NaturalMultiplicationMonotone.monotone hZ 0 1 2 3 4 5
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inr (Or.inl rfl)))
    (.hyp (Or.inl rfl))

theorem rightMonotone_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence rightMonotoneSentence) := TheoryTransport.sentence source_rightMonotone
theorem native_rightMonotone : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence rightMonotoneSentence) :=
  ZFReplay.replay rightMonotone_kernel_certificate

theorem source_rightWeak : Derives (Source.SetLanguage.ZF.at 0) rightWeakSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 6 :=
    (Context.add (product 0 2 3 5)
    (Context.add (product 0 1 3 4)
    (Context.add ((empty 3).neg)
    (Context.add (Formula.mem 3 0)
    (Context.add (Formula.mem 2 0)
    (Context.add (Formula.mem 1 0)
    (Context.add (omega 0)
    (Source.SetLanguage.ZF.at 6))))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 6
  exact NaturalMultiplicationOrderLaws.weak_iff hZ 0 1 2 3 4 5
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inr (Or.inl rfl)))
    (.hyp (Or.inl rfl))

theorem rightWeak_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence rightWeakSentence) := TheoryTransport.sentence source_rightWeak
theorem native_rightWeak : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence rightWeakSentence) :=
  ZFReplay.replay rightWeak_kernel_certificate

theorem source_rightStrict : Derives (Source.SetLanguage.ZF.at 0) rightStrictSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 6 :=
    (Context.add (product 0 2 3 5)
    (Context.add (product 0 1 3 4)
    (Context.add ((empty 3).neg)
    (Context.add (Formula.mem 3 0)
    (Context.add (Formula.mem 2 0)
    (Context.add (Formula.mem 1 0)
    (Context.add (omega 0)
    (Source.SetLanguage.ZF.at 6))))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 6
  exact NaturalMultiplicationOrderLaws.strict_iff hZ 0 1 2 3 4 5
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inr (Or.inl rfl)))
    (.hyp (Or.inl rfl))

theorem rightStrict_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence rightStrictSentence) := TheoryTransport.sentence source_rightStrict
theorem native_rightStrict : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence rightStrictSentence) :=
  ZFReplay.replay rightStrict_kernel_certificate

theorem source_rightCancel : Derives (Source.SetLanguage.ZF.at 0) rightCancelSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 5 :=
    (Context.add (product 0 2 3 4)
    (Context.add (product 0 1 3 4)
    (Context.add ((empty 3).neg)
    (Context.add (Formula.mem 3 0)
    (Context.add (Formula.mem 2 0)
    (Context.add (Formula.mem 1 0)
    (Context.add (omega 0)
    (Source.SetLanguage.ZF.at 5))))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 5
  exact NaturalMultiplicationOrderLaws.cancel hZ 0 1 2 3 4
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inr (Or.inl rfl)))
    (.hyp (Or.inl rfl))

theorem rightCancel_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence rightCancelSentence) := TheoryTransport.sentence source_rightCancel
theorem native_rightCancel : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence rightCancelSentence) :=
  ZFReplay.replay rightCancel_kernel_certificate

theorem source_leftMonotone : Derives (Source.SetLanguage.ZF.at 0) leftMonotoneSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 6 :=
    (Context.add (below 1 2)
    (Context.add (product 0 3 2 5)
    (Context.add (product 0 3 1 4)
    (Context.add (Formula.mem 3 0)
    (Context.add (Formula.mem 2 0)
    (Context.add (Formula.mem 1 0)
    (Context.add (omega 0)
    (Source.SetLanguage.ZF.at 6))))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 6
  exact NaturalMultiplicationOrderLaws.left_monotone hZ 0 1 2 3 4 5
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inr (Or.inl rfl)))
    (.hyp (Or.inl rfl))

theorem leftMonotone_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence leftMonotoneSentence) := TheoryTransport.sentence source_leftMonotone
theorem native_leftMonotone : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence leftMonotoneSentence) :=
  ZFReplay.replay leftMonotone_kernel_certificate

theorem source_leftWeak : Derives (Source.SetLanguage.ZF.at 0) leftWeakSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 6 :=
    (Context.add (product 0 3 2 5)
    (Context.add (product 0 3 1 4)
    (Context.add ((empty 3).neg)
    (Context.add (Formula.mem 3 0)
    (Context.add (Formula.mem 2 0)
    (Context.add (Formula.mem 1 0)
    (Context.add (omega 0)
    (Source.SetLanguage.ZF.at 6))))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 6
  exact NaturalMultiplicationOrderLaws.left_weak_iff hZ 0 1 2 3 4 5
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inr (Or.inl rfl)))
    (.hyp (Or.inl rfl))

theorem leftWeak_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence leftWeakSentence) := TheoryTransport.sentence source_leftWeak
theorem native_leftWeak : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence leftWeakSentence) :=
  ZFReplay.replay leftWeak_kernel_certificate

theorem source_leftStrict : Derives (Source.SetLanguage.ZF.at 0) leftStrictSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 6 :=
    (Context.add (product 0 3 2 5)
    (Context.add (product 0 3 1 4)
    (Context.add ((empty 3).neg)
    (Context.add (Formula.mem 3 0)
    (Context.add (Formula.mem 2 0)
    (Context.add (Formula.mem 1 0)
    (Context.add (omega 0)
    (Source.SetLanguage.ZF.at 6))))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 6
  exact NaturalMultiplicationOrderLaws.left_strict_iff hZ 0 1 2 3 4 5
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inr (Or.inl rfl)))
    (.hyp (Or.inl rfl))

theorem leftStrict_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence leftStrictSentence) := TheoryTransport.sentence source_leftStrict
theorem native_leftStrict : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence leftStrictSentence) :=
  ZFReplay.replay leftStrict_kernel_certificate

theorem source_leftCancel : Derives (Source.SetLanguage.ZF.at 0) leftCancelSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 5 :=
    (Context.add (product 0 3 2 4)
    (Context.add (product 0 3 1 4)
    (Context.add ((empty 3).neg)
    (Context.add (Formula.mem 3 0)
    (Context.add (Formula.mem 2 0)
    (Context.add (Formula.mem 1 0)
    (Context.add (omega 0)
    (Source.SetLanguage.ZF.at 5))))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 5
  exact NaturalMultiplicationOrderLaws.left_cancel hZ 0 1 2 3 4
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inr (Or.inl rfl)))
    (.hyp (Or.inl rfl))

theorem leftCancel_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence leftCancelSentence) := TheoryTransport.sentence source_leftCancel
theorem native_leftCancel : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence leftCancelSentence) :=
  ZFReplay.replay leftCancel_kernel_certificate

end PPAC.Migration.Internal.ObjectNaturalMultiplicativeOrder
