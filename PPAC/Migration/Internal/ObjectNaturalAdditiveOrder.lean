import PPAC.Migration.Internal.NaturalAdditionMonotone
import PPAC.Migration.Internal.ObjectNaturalDifference

namespace PPAC.Migration.Internal.ObjectNaturalAdditiveOrder
open Source SourceAlgebra SourceLogic OmegaSyntax
open NaturalAdditionSyntax (sum)
open NaturalMultiplicationSyntax (product)
open NaturalAdditionBounds (below)

def rightWeakSentence : Source.Sentence := ((omega (0 : Fin 6)).imp
  ((Formula.mem 1 0).imp
  ((Formula.mem 2 0).imp
  ((Formula.mem 3 0).imp
  ((sum 0 1 3 4).imp
  ((sum 0 2 3 5).imp
  (((below 1 2).iff (below 4 5))))))))).close

def rightStrictSentence : Source.Sentence := ((omega (0 : Fin 6)).imp
  ((Formula.mem 1 0).imp
  ((Formula.mem 2 0).imp
  ((Formula.mem 3 0).imp
  ((sum 0 1 3 4).imp
  ((sum 0 2 3 5).imp
  (((Formula.mem 1 2).iff (.mem 4 5))))))))).close

def leftWeakSentence : Source.Sentence := ((omega (0 : Fin 6)).imp
  ((Formula.mem 1 0).imp
  ((Formula.mem 2 0).imp
  ((Formula.mem 3 0).imp
  ((sum 0 3 1 4).imp
  ((sum 0 3 2 5).imp
  (((below 1 2).iff (below 4 5))))))))).close

def leftStrictSentence : Source.Sentence := ((omega (0 : Fin 6)).imp
  ((Formula.mem 1 0).imp
  ((Formula.mem 2 0).imp
  ((Formula.mem 3 0).imp
  ((sum 0 3 1 4).imp
  ((sum 0 3 2 5).imp
  (((Formula.mem 1 2).iff (.mem 4 5))))))))).close

theorem source_rightWeak : Derives (Source.SetLanguage.ZF.at 0) rightWeakSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 6 :=
    (Context.add (sum 0 2 3 5)
    (Context.add (sum 0 1 3 4)
    (Context.add (Formula.mem 3 0)
    (Context.add (Formula.mem 2 0)
    (Context.add (Formula.mem 1 0)
    (Context.add (omega 0)
    (Source.SetLanguage.ZF.at 6)))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 6
  exact NaturalAdditionMonotone.weak_iff hZ 0 1 2 3 4 5
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
  let Δ : Context 6 :=
    (Context.add (sum 0 2 3 5)
    (Context.add (sum 0 1 3 4)
    (Context.add (Formula.mem 3 0)
    (Context.add (Formula.mem 2 0)
    (Context.add (Formula.mem 1 0)
    (Context.add (omega 0)
    (Source.SetLanguage.ZF.at 6)))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 6
  exact NaturalAdditionMonotone.strict_iff hZ 0 1 2 3 4 5
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

theorem source_leftWeak : Derives (Source.SetLanguage.ZF.at 0) leftWeakSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 6 :=
    (Context.add (sum 0 3 2 5)
    (Context.add (sum 0 3 1 4)
    (Context.add (Formula.mem 3 0)
    (Context.add (Formula.mem 2 0)
    (Context.add (Formula.mem 1 0)
    (Context.add (omega 0)
    (Source.SetLanguage.ZF.at 6)))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 6
  exact NaturalAdditionMonotone.left_weak_iff hZ 0 1 2 3 4 5
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
  let Δ : Context 6 :=
    (Context.add (sum 0 3 2 5)
    (Context.add (sum 0 3 1 4)
    (Context.add (Formula.mem 3 0)
    (Context.add (Formula.mem 2 0)
    (Context.add (Formula.mem 1 0)
    (Context.add (omega 0)
    (Source.SetLanguage.ZF.at 6)))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 6
  exact NaturalAdditionMonotone.left_strict_iff hZ 0 1 2 3 4 5
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

end PPAC.Migration.Internal.ObjectNaturalAdditiveOrder
