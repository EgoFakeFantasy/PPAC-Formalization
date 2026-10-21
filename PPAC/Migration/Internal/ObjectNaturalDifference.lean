import PPAC.Migration.Internal.NaturalDifferencePositive
import PPAC.Migration.Internal.ObjectNaturalOrder

namespace PPAC.Migration.Internal.ObjectNaturalDifference
open Source SourceAlgebra SourceLogic OmegaSyntax
open NaturalAdditionSyntax (sum)
open NaturalMultiplicationSyntax (product)
open NaturalAdditionBounds (below)

def orderSentence : Source.Sentence := ((omega (0 : Fin 3)).imp
  ((Formula.mem 1 0).imp
  ((Formula.mem 2 0).imp
  (((below 1 2).iff (NaturalDifferenceSyntax.existsDifference 0 1 2)))))).close

def fiberSentence : Source.Sentence := ((omega (0 : Fin 3)).imp
  ((Formula.mem 1 0).imp
  ((Formula.mem 2 0).imp
  ((below 1 2).imp
  ((NaturalDifferenceSyntax.fiber 0 1 2)))))).close

def strictSentence : Source.Sentence := ((omega (0 : Fin 3)).imp
  ((Formula.mem 1 0).imp
  ((Formula.mem 2 0).imp
  (((Formula.mem 1 2).iff (NaturalDifferenceSyntax.positiveExists 0 1 2)))))).close

def zeroSentence : Source.Sentence := ((omega (0 : Fin 4)).imp
  ((Formula.mem 1 0).imp
  ((Formula.mem 2 0).imp
  ((Formula.mem 3 0).imp
  ((sum 0 1 3 2).imp
  (((empty 3).iff (.equal 1 2)))))))).close

theorem source_order : Derives (Source.SetLanguage.ZF.at 0) orderSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 3 :=
    (Context.add (Formula.mem 2 0)
    (Context.add (Formula.mem 1 0)
    (Context.add (omega 0)
    (Source.SetLanguage.ZF.at 3))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 3
  exact NaturalDifference.difference_iff hZ 0 1 2
    (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inr (Or.inl rfl)))
    (.hyp (Or.inl rfl))

theorem order_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence orderSentence) := TheoryTransport.sentence source_order
theorem native_order : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence orderSentence) :=
  ZFReplay.replay order_kernel_certificate

theorem source_fiber : Derives (Source.SetLanguage.ZF.at 0) fiberSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 3 :=
    (Context.add (below 1 2)
    (Context.add (Formula.mem 2 0)
    (Context.add (Formula.mem 1 0)
    (Context.add (omega 0)
    (Source.SetLanguage.ZF.at 3)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 3
  exact NaturalDifference.exists_unique hZ 0 1 2
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inr (Or.inl rfl)))
    (.hyp (Or.inl rfl))

theorem fiber_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence fiberSentence) := TheoryTransport.sentence source_fiber
theorem native_fiber : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence fiberSentence) :=
  ZFReplay.replay fiber_kernel_certificate

theorem source_strict : Derives (Source.SetLanguage.ZF.at 0) strictSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 3 :=
    (Context.add (Formula.mem 2 0)
    (Context.add (Formula.mem 1 0)
    (Context.add (omega 0)
    (Source.SetLanguage.ZF.at 3))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 3
  exact NaturalDifferencePositive.strict_iff hZ 0 1 2
    (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inr (Or.inl rfl)))
    (.hyp (Or.inl rfl))

theorem strict_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence strictSentence) := TheoryTransport.sentence source_strict
theorem native_strict : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence strictSentence) :=
  ZFReplay.replay strict_kernel_certificate

theorem source_zero : Derives (Source.SetLanguage.ZF.at 0) zeroSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 4 :=
    (Context.add (sum 0 1 3 2)
    (Context.add (Formula.mem 3 0)
    (Context.add (Formula.mem 2 0)
    (Context.add (Formula.mem 1 0)
    (Context.add (omega 0)
    (Source.SetLanguage.ZF.at 4))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 4
  exact NaturalDifferencePositive.zero_iff hZ 0 1 2 3
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    (.hyp (Or.inr (Or.inl rfl)))
    (.hyp (Or.inl rfl))

theorem zero_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence zeroSentence) := TheoryTransport.sentence source_zero
theorem native_zero : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence zeroSentence) :=
  ZFReplay.replay zero_kernel_certificate

end PPAC.Migration.Internal.ObjectNaturalDifference
