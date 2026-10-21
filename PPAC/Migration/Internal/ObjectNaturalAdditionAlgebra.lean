import PPAC.Migration.Internal.NaturalAdditionAlgebraLaws

/-! 加法左后继、交换、结合和两侧抵消的实际原ZF闭句证书。 -/
namespace PPAC.Migration.Internal.ObjectNaturalAdditionAlgebra
open Source SourceAlgebra SourceLogic GraphSyntax OmegaSyntax NaturalAdditionSyntax

def leftSuccessorSentence : Source.Sentence := ((omega (0 : Fin 6)).imp
  ((Formula.mem 1 0).imp
  ((Formula.mem 3 0).imp
  ((successor 2 1).imp
  ((sum 0 1 3 4).imp
  (((sum 0 2 3 5).iff (successor 5 4)))))))).close

def commutativeSentence : Source.Sentence := ((omega (0 : Fin 4)).imp
  ((Formula.mem 1 0).imp
  ((Formula.mem 2 0).imp
  (((sum 0 1 2 3).iff (sum 0 2 1 3)))))).close

def associativeSentence : Source.Sentence := ((omega (0 : Fin 7)).imp
  ((Formula.mem 1 0).imp
  ((Formula.mem 2 0).imp
  ((Formula.mem 3 0).imp
  ((sum 0 1 2 4).imp
  ((sum 0 2 3 5).imp
  (((sum 0 4 3 6).iff (sum 0 1 5 6))))))))).close

def cancelRightSentence : Source.Sentence := ((omega (0 : Fin 5)).imp
  ((Formula.mem 1 0).imp
  ((Formula.mem 2 0).imp
  ((Formula.mem 3 0).imp
  ((sum 0 1 3 4).imp
  ((sum 0 2 3 4).imp
  ((Formula.equal 1 2)))))))).close

def cancelLeftSentence : Source.Sentence := ((omega (0 : Fin 5)).imp
  ((Formula.mem 1 0).imp
  ((Formula.mem 2 0).imp
  ((Formula.mem 3 0).imp
  ((sum 0 3 1 4).imp
  ((sum 0 3 2 4).imp
  ((Formula.equal 1 2)))))))).close

theorem separation_at {n} (p : Formula (n+1)) (m : Nat) : Derives (Source.SetLanguage.ZF.at m)
    ((Source.SetLanguage.separation p).rename Fin.elim0) :=
  .hyp ⟨_, Source.SetLanguage.IsZFAxiom.separation p, rfl⟩

theorem source_leftSuccessor : Derives (Source.SetLanguage.ZF.at 0) leftSuccessorSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 6 :=
    (Context.add (sum 0 1 3 4)
    (Context.add (successor 2 1)
    (Context.add (Formula.mem 3 0)
    (Context.add (Formula.mem 1 0)
    (Context.add (omega 0) (Source.SetLanguage.ZF.at 6))))))
  have hA : ArithmeticContext.Evidence Δ := by
    apply ArithmeticContext.add
    apply ArithmeticContext.add
    apply ArithmeticContext.add
    apply ArithmeticContext.add
    apply ArithmeticContext.add
    exact ArithmeticContext.source_ZF 6
  have lift {q : Formula 6} (h : Derives (Source.SetLanguage.ZF.at 6) q) : Derives Δ q := by
    apply add
    apply add
    apply add
    apply add
    apply add
    exact h
  exact NaturalAdditionAlgebraLaws.shift_iff hA 0 1 2 3 4 5
    (lift (ObjectNaturalAddition.recursor_certificate_at 6))
    (lift (separation_at NaturalAdditionShift.matrix 6))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    (.hyp (Or.inr (Or.inl rfl)))
    (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inl rfl))

theorem leftSuccessor_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence leftSuccessorSentence) := TheoryTransport.sentence source_leftSuccessor
theorem native_leftSuccessor : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence leftSuccessorSentence) :=
  ZFReplay.replay leftSuccessor_kernel_certificate

theorem source_commutative : Derives (Source.SetLanguage.ZF.at 0) commutativeSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 4 :=
    (Context.add (Formula.mem 2 0)
    (Context.add (Formula.mem 1 0)
    (Context.add (omega 0) (Source.SetLanguage.ZF.at 4))))
  have hA : ArithmeticContext.Evidence Δ := by
    apply ArithmeticContext.add
    apply ArithmeticContext.add
    apply ArithmeticContext.add
    exact ArithmeticContext.source_ZF 4
  have lift {q : Formula 4} (h : Derives (Source.SetLanguage.ZF.at 4) q) : Derives Δ q := by
    apply add
    apply add
    apply add
    exact h
  exact NaturalAdditionCommutative.commutative_iff hA 0 1 2 3
    (lift (ObjectNaturalAddition.recursor_certificate_at 4))
    (lift (separation_at NaturalAdditionCommutative.matrix 4))
    (lift (separation_at NaturalAdditionShift.matrix 4))
    (lift (separation_at NaturalAdditionZero.matrix 4))
    (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inr (Or.inl rfl)))
    (.hyp (Or.inl rfl))

theorem commutative_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence commutativeSentence) := TheoryTransport.sentence source_commutative
theorem native_commutative : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence commutativeSentence) :=
  ZFReplay.replay commutative_kernel_certificate

theorem source_associative : Derives (Source.SetLanguage.ZF.at 0) associativeSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 7 :=
    (Context.add (sum 0 2 3 5)
    (Context.add (sum 0 1 2 4)
    (Context.add (Formula.mem 3 0)
    (Context.add (Formula.mem 2 0)
    (Context.add (Formula.mem 1 0)
    (Context.add (omega 0) (Source.SetLanguage.ZF.at 7)))))))
  have hA : ArithmeticContext.Evidence Δ := by
    apply ArithmeticContext.add
    apply ArithmeticContext.add
    apply ArithmeticContext.add
    apply ArithmeticContext.add
    apply ArithmeticContext.add
    apply ArithmeticContext.add
    exact ArithmeticContext.source_ZF 7
  have lift {q : Formula 7} (h : Derives (Source.SetLanguage.ZF.at 7) q) : Derives Δ q := by
    apply add
    apply add
    apply add
    apply add
    apply add
    apply add
    exact h
  exact NaturalAdditionAlgebraLaws.associative_iff hA 0 1 2 4 3 5 6
    (lift (ObjectNaturalAddition.recursor_certificate_at 7))
    (lift (separation_at NaturalAdditionAssociative.matrix 7))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inr (Or.inl rfl)))
    (.hyp (Or.inl rfl))

theorem associative_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence associativeSentence) := TheoryTransport.sentence source_associative
theorem native_associative : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence associativeSentence) :=
  ZFReplay.replay associative_kernel_certificate

theorem source_cancelRight : Derives (Source.SetLanguage.ZF.at 0) cancelRightSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 5 :=
    (Context.add (sum 0 2 3 4)
    (Context.add (sum 0 1 3 4)
    (Context.add (Formula.mem 3 0)
    (Context.add (Formula.mem 2 0)
    (Context.add (Formula.mem 1 0)
    (Context.add (omega 0) (Source.SetLanguage.ZF.at 5)))))))
  have hA : ArithmeticContext.Evidence Δ := by
    apply ArithmeticContext.add
    apply ArithmeticContext.add
    apply ArithmeticContext.add
    apply ArithmeticContext.add
    apply ArithmeticContext.add
    apply ArithmeticContext.add
    exact ArithmeticContext.source_ZF 5
  have lift {q : Formula 5} (h : Derives (Source.SetLanguage.ZF.at 5) q) : Derives Δ q := by
    apply add
    apply add
    apply add
    apply add
    apply add
    apply add
    exact h
  exact NaturalAdditionCancellation.cancel_right hA 0 1 2 3 4
    (lift (ObjectNaturalAddition.recursor_certificate_at 5))
    (lift (separation_at NaturalAdditionCancellation.matrix 5))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inr (Or.inl rfl)))
    (.hyp (Or.inl rfl))

theorem cancelRight_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence cancelRightSentence) := TheoryTransport.sentence source_cancelRight
theorem native_cancelRight : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence cancelRightSentence) :=
  ZFReplay.replay cancelRight_kernel_certificate

theorem source_cancelLeft : Derives (Source.SetLanguage.ZF.at 0) cancelLeftSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 5 :=
    (Context.add (sum 0 3 2 4)
    (Context.add (sum 0 3 1 4)
    (Context.add (Formula.mem 3 0)
    (Context.add (Formula.mem 2 0)
    (Context.add (Formula.mem 1 0)
    (Context.add (omega 0) (Source.SetLanguage.ZF.at 5)))))))
  have hA : ArithmeticContext.Evidence Δ := by
    apply ArithmeticContext.add
    apply ArithmeticContext.add
    apply ArithmeticContext.add
    apply ArithmeticContext.add
    apply ArithmeticContext.add
    apply ArithmeticContext.add
    exact ArithmeticContext.source_ZF 5
  have lift {q : Formula 5} (h : Derives (Source.SetLanguage.ZF.at 5) q) : Derives Δ q := by
    apply add
    apply add
    apply add
    apply add
    apply add
    apply add
    exact h
  exact NaturalAdditionAlgebraLaws.cancel_left hA 0 1 2 3 4
    (lift (ObjectNaturalAddition.recursor_certificate_at 5))
    (lift (separation_at NaturalAdditionCancellation.matrix 5))
    (lift (separation_at NaturalAdditionCommutative.matrix 5))
    (lift (separation_at NaturalAdditionShift.matrix 5))
    (lift (separation_at NaturalAdditionZero.matrix 5))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inr (Or.inl rfl)))
    (.hyp (Or.inl rfl))

theorem cancelLeft_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence cancelLeftSentence) := TheoryTransport.sentence source_cancelLeft
theorem native_cancelLeft : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence cancelLeftSentence) :=
  ZFReplay.replay cancelLeft_kernel_certificate

end PPAC.Migration.Internal.ObjectNaturalAdditionAlgebra
