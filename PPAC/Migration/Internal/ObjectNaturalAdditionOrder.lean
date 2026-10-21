import PPAC.Migration.Internal.NaturalAdditionOrderLaws

/-! 加法下界、正加数严格界及零刻画的原nativeZF闭句。 -/
namespace PPAC.Migration.Internal.ObjectNaturalAdditionOrder
open Source SourceAlgebra SourceLogic GraphSyntax OmegaSyntax NaturalAdditionSyntax

def boundsSentence : Source.Sentence := ((omega (0 : Fin 4)).imp
  ((Formula.mem 1 0).imp
  ((Formula.mem 2 0).imp
  ((sum 0 1 2 3).imp
  (((NaturalAdditionBounds.below 1 3).conj (NaturalAdditionBounds.below 2 3))))))).close

def zeroSentence : Source.Sentence := ((omega (0 : Fin 4)).imp
  ((Formula.mem 1 0).imp
  ((Formula.mem 2 0).imp
  ((sum 0 1 2 3).imp
  (((empty 3).iff ((empty 1).conj (empty 2)))))))).close

def strictRightSentence : Source.Sentence := ((omega (0 : Fin 4)).imp
  ((Formula.mem 1 0).imp
  ((Formula.mem 2 0).imp
  ((sum 0 1 2 3).imp
  (((empty 2).neg).imp
  ((Formula.mem 1 3))))))).close

def strictLeftSentence : Source.Sentence := ((omega (0 : Fin 4)).imp
  ((Formula.mem 1 0).imp
  ((Formula.mem 2 0).imp
  ((sum 0 1 2 3).imp
  (((empty 1).neg).imp
  ((Formula.mem 2 3))))))).close

theorem source_bounds : Derives (Source.SetLanguage.ZF.at 0) boundsSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 4 :=
    (Context.add (sum 0 1 2 3)
    (Context.add (Formula.mem 2 0)
    (Context.add (Formula.mem 1 0)
    (Context.add (omega 0) (Source.SetLanguage.ZF.at 4)))))
  have hA : ArithmeticContext.Evidence Δ := by
    apply ArithmeticContext.add
    apply ArithmeticContext.add
    apply ArithmeticContext.add
    apply ArithmeticContext.add
    exact ArithmeticContext.source_ZF 4
  have lift {q : Formula 4} (h : Derives (Source.SetLanguage.ZF.at 4) q) : Derives Δ q := by
    apply add
    apply add
    apply add
    apply add
    exact h
  exact NaturalAdditionOrderLaws.bounds hA 0 1 2 3
    (lift (ObjectNaturalAddition.recursor_certificate_at 4))
    (lift (ObjectNaturalAdditionAlgebra.separation_at NaturalAdditionBounds.matrix 4))
    (lift (ObjectNaturalAdditionAlgebra.separation_at NaturalAdditionCommutative.matrix 4))
    (lift (ObjectNaturalAdditionAlgebra.separation_at NaturalAdditionShift.matrix 4))
    (lift (ObjectNaturalAdditionAlgebra.separation_at NaturalAdditionZero.matrix 4))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inr (Or.inl rfl)))
    (.hyp (Or.inl rfl))

theorem bounds_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence boundsSentence) := TheoryTransport.sentence source_bounds
theorem native_bounds : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence boundsSentence) :=
  ZFReplay.replay bounds_kernel_certificate

theorem source_zero : Derives (Source.SetLanguage.ZF.at 0) zeroSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 4 :=
    (Context.add (sum 0 1 2 3)
    (Context.add (Formula.mem 2 0)
    (Context.add (Formula.mem 1 0)
    (Context.add (omega 0) (Source.SetLanguage.ZF.at 4)))))
  have hA : ArithmeticContext.Evidence Δ := by
    apply ArithmeticContext.add
    apply ArithmeticContext.add
    apply ArithmeticContext.add
    apply ArithmeticContext.add
    exact ArithmeticContext.source_ZF 4
  have lift {q : Formula 4} (h : Derives (Source.SetLanguage.ZF.at 4) q) : Derives Δ q := by
    apply add
    apply add
    apply add
    apply add
    exact h
  exact NaturalAdditionOrderLaws.empty_sum_iff hA 0 1 2 3
    (lift (ObjectNaturalAddition.recursor_certificate_at 4))
    (lift (ObjectNaturalAdditionAlgebra.separation_at NaturalAdditionBounds.matrix 4))
    (lift (ObjectNaturalAdditionAlgebra.separation_at NaturalAdditionCommutative.matrix 4))
    (lift (ObjectNaturalAdditionAlgebra.separation_at NaturalAdditionShift.matrix 4))
    (lift (ObjectNaturalAdditionAlgebra.separation_at NaturalAdditionZero.matrix 4))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inr (Or.inl rfl)))
    (.hyp (Or.inl rfl))

theorem zero_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence zeroSentence) := TheoryTransport.sentence source_zero
theorem native_zero : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence zeroSentence) :=
  ZFReplay.replay zero_kernel_certificate

theorem source_strictRight : Derives (Source.SetLanguage.ZF.at 0) strictRightSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 4 :=
    (Context.add ((empty 2).neg)
    (Context.add (sum 0 1 2 3)
    (Context.add (Formula.mem 2 0)
    (Context.add (Formula.mem 1 0)
    (Context.add (omega 0) (Source.SetLanguage.ZF.at 4))))))
  have hA : ArithmeticContext.Evidence Δ := by
    apply ArithmeticContext.add
    apply ArithmeticContext.add
    apply ArithmeticContext.add
    apply ArithmeticContext.add
    apply ArithmeticContext.add
    exact ArithmeticContext.source_ZF 4
  have lift {q : Formula 4} (h : Derives (Source.SetLanguage.ZF.at 4) q) : Derives Δ q := by
    apply add
    apply add
    apply add
    apply add
    apply add
    exact h
  exact NaturalAdditionOrderLaws.strict_right hA 0 1 2 3
    (lift (ObjectNaturalAddition.recursor_certificate_at 4))
    (lift (ObjectNaturalAdditionAlgebra.separation_at NaturalAdditionBounds.matrix 4))
    (lift (ObjectNaturalAdditionAlgebra.separation_at OmegaStructureSyntax.splitMatrix 4))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inr (Or.inl rfl)))
    (.hyp (Or.inl rfl))

theorem strictRight_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence strictRightSentence) := TheoryTransport.sentence source_strictRight
theorem native_strictRight : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence strictRightSentence) :=
  ZFReplay.replay strictRight_kernel_certificate

theorem source_strictLeft : Derives (Source.SetLanguage.ZF.at 0) strictLeftSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 4 :=
    (Context.add ((empty 1).neg)
    (Context.add (sum 0 1 2 3)
    (Context.add (Formula.mem 2 0)
    (Context.add (Formula.mem 1 0)
    (Context.add (omega 0) (Source.SetLanguage.ZF.at 4))))))
  have hA : ArithmeticContext.Evidence Δ := by
    apply ArithmeticContext.add
    apply ArithmeticContext.add
    apply ArithmeticContext.add
    apply ArithmeticContext.add
    apply ArithmeticContext.add
    exact ArithmeticContext.source_ZF 4
  have lift {q : Formula 4} (h : Derives (Source.SetLanguage.ZF.at 4) q) : Derives Δ q := by
    apply add
    apply add
    apply add
    apply add
    apply add
    exact h
  have hc := (lift (ObjectNaturalAddition.recursor_certificate_at 4))
  have hswap := NaturalAdditionCommutative.commute hA 0 1 2 3 hc
    (lift (ObjectNaturalAdditionAlgebra.separation_at NaturalAdditionCommutative.matrix 4))
    (lift (ObjectNaturalAdditionAlgebra.separation_at NaturalAdditionShift.matrix 4))
    (lift (ObjectNaturalAdditionAlgebra.separation_at NaturalAdditionZero.matrix 4))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inr (Or.inl rfl)))
  exact NaturalAdditionOrderLaws.strict_right hA 0 2 1 3 hc
    (lift (ObjectNaturalAdditionAlgebra.separation_at NaturalAdditionBounds.matrix 4))
    (lift (ObjectNaturalAdditionAlgebra.separation_at OmegaStructureSyntax.splitMatrix 4))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
    (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) hswap
    (.hyp (Or.inl rfl))

theorem strictLeft_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence strictLeftSentence) := TheoryTransport.sentence source_strictLeft
theorem native_strictLeft : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence strictLeftSentence) :=
  ZFReplay.replay strictLeft_kernel_certificate

end PPAC.Migration.Internal.ObjectNaturalAdditionOrder
