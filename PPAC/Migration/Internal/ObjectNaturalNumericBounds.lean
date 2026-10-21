import PPAC.Migration.Internal.NaturalArithmeticBounds
import PPAC.Migration.Internal.ObjectNaturalMultiplicativeOrder

namespace PPAC.Migration.Internal.ObjectNaturalNumericBounds
open Source SourceAlgebra SourceLogic OmegaSyntax
open NaturalAdditionSyntax (sum)
open NaturalMultiplicationSyntax (product)
open NaturalAdditionBounds (below)

def unitSentence : Source.Sentence := ((omega (0 : Fin 4)).imp
  ((empty 1).imp
  ((successor 2 1).imp
  ((Formula.mem 3 0).imp
  (((empty 3).neg.iff (below 2 3))))))).close

def factorsSentence : Source.Sentence := ((omega (0 : Fin 4)).imp
  ((Formula.mem 1 0).imp
  ((Formula.mem 2 0).imp
  ((product 0 1 2 3).imp
  (((empty 1).neg).imp
  (((empty 2).neg).imp
  (((below 1 3).conj (below 2 3))))))))).close

def squareSentence : Source.Sentence := ((omega (0 : Fin 3)).imp
  ((Formula.mem 1 0).imp
  ((product 0 1 1 2).imp
  ((below 1 2))))).close

def squareStrictSentence : Source.Sentence := ((omega (0 : Fin 5)).imp
  ((Formula.mem 1 0).imp
  ((Formula.mem 2 0).imp
  ((product 0 1 1 3).imp
  ((product 0 2 2 4).imp
  ((Formula.mem 1 2).imp
  ((Formula.mem 3 4)))))))).close

def squareInjectiveSentence : Source.Sentence := ((omega (0 : Fin 4)).imp
  ((Formula.mem 1 0).imp
  ((Formula.mem 2 0).imp
  ((product 0 1 1 3).imp
  ((product 0 2 2 3).imp
  ((Formula.equal 1 2))))))).close

theorem source_unit : Derives (Source.SetLanguage.ZF.at 0) unitSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 4 :=
    (Context.add (Formula.mem 3 0)
    (Context.add (successor 2 1)
    (Context.add (empty 1)
    (Context.add (omega 0)
    (Source.SetLanguage.ZF.at 4)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 4
  exact NaturalArithmeticBounds.unit_bound_iff hZ 0 1 2 3
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inr (Or.inl rfl)))
    (.hyp (Or.inl rfl))

theorem unit_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence unitSentence) := TheoryTransport.sentence source_unit
theorem native_unit : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence unitSentence) :=
  ZFReplay.replay unit_kernel_certificate

theorem source_factors : Derives (Source.SetLanguage.ZF.at 0) factorsSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 4 :=
    (Context.add ((empty 2).neg)
    (Context.add ((empty 1).neg)
    (Context.add (product 0 1 2 3)
    (Context.add (Formula.mem 2 0)
    (Context.add (Formula.mem 1 0)
    (Context.add (omega 0)
    (Source.SetLanguage.ZF.at 4)))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 4
  have hl := NaturalArithmeticBounds.factor_bound hZ 0 1 2 3
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    (.hyp (Or.inl rfl))
    (.hyp (Or.inr (Or.inr (Or.inl rfl))))
  have hr := NaturalArithmeticBounds.other_factor_bound hZ 0 1 2 3
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    (.hyp (Or.inr (Or.inl rfl)))
    (.hyp (Or.inr (Or.inr (Or.inl rfl))))
  exact .conjI hl hr

theorem factors_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence factorsSentence) := TheoryTransport.sentence source_factors
theorem native_factors : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence factorsSentence) :=
  ZFReplay.replay factors_kernel_certificate

theorem source_square : Derives (Source.SetLanguage.ZF.at 0) squareSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 3 :=
    (Context.add (product 0 1 1 2)
    (Context.add (Formula.mem 1 0)
    (Context.add (omega 0)
    (Source.SetLanguage.ZF.at 3))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 3
  exact NaturalArithmeticBounds.square_bound hZ 0 1 2
    (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inr (Or.inl rfl)))
    (.hyp (Or.inl rfl))

theorem square_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence squareSentence) := TheoryTransport.sentence source_square
theorem native_square : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence squareSentence) :=
  ZFReplay.replay square_kernel_certificate

theorem source_squareStrict : Derives (Source.SetLanguage.ZF.at 0) squareStrictSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 5 :=
    (Context.add (Formula.mem 1 2)
    (Context.add (product 0 2 2 4)
    (Context.add (product 0 1 1 3)
    (Context.add (Formula.mem 2 0)
    (Context.add (Formula.mem 1 0)
    (Context.add (omega 0)
    (Source.SetLanguage.ZF.at 5)))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 5
  exact NaturalArithmeticBounds.square_strict hZ 0 1 2 3 4
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inr (Or.inl rfl)))
    (.hyp (Or.inl rfl))

theorem squareStrict_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence squareStrictSentence) := TheoryTransport.sentence source_squareStrict
theorem native_squareStrict : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence squareStrictSentence) :=
  ZFReplay.replay squareStrict_kernel_certificate

theorem source_squareInjective : Derives (Source.SetLanguage.ZF.at 0) squareInjectiveSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 4 :=
    (Context.add (product 0 2 2 3)
    (Context.add (product 0 1 1 3)
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
  exact NaturalArithmeticBounds.square_injective hZ 0 1 2 3
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inr (Or.inl rfl)))
    (.hyp (Or.inl rfl))

theorem squareInjective_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence squareInjectiveSentence) := TheoryTransport.sentence source_squareInjective
theorem native_squareInjective : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence squareInjectiveSentence) :=
  ZFReplay.replay squareInjective_kernel_certificate

end PPAC.Migration.Internal.ObjectNaturalNumericBounds
