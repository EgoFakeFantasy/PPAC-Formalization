import PPAC.Migration.Internal.NaturalMultiplicationAlgebraLaws
import PPAC.Migration.Internal.ObjectNaturalAdditionReassociation

namespace PPAC.Migration.Internal.ObjectNaturalMultiplicationAlgebra
open Source SourceAlgebra SourceLogic OmegaSyntax NaturalAdditionSyntax
open NaturalMultiplicationSyntax (product)

def sumRightSentence : Source.Sentence := ((omega (0 : Fin 8)).imp
  ((Formula.mem 1 0).imp
  ((Formula.mem 2 0).imp
  ((Formula.mem 3 0).imp
  ((product 0 1 2 4).imp
  ((sum 0 2 3 5).imp
  ((product 0 1 3 6).imp
  (((product 0 1 5 7).iff (sum 0 4 6 7)))))))))).close

def sumLeftSentence : Source.Sentence := ((omega (0 : Fin 8)).imp
  ((Formula.mem 1 0).imp
  ((Formula.mem 2 0).imp
  ((Formula.mem 3 0).imp
  ((sum 0 1 2 4).imp
  ((product 0 1 3 5).imp
  ((product 0 2 3 6).imp
  (((product 0 4 3 7).iff (sum 0 5 6 7)))))))))).close

def leftSuccessorSentence : Source.Sentence := ((omega (0 : Fin 6)).imp
  ((Formula.mem 1 0).imp
  ((Formula.mem 3 0).imp
  ((successor 2 1).imp
  ((product 0 1 3 4).imp
  (((product 0 2 3 5).iff (sum 0 4 3 5)))))))).close

def commutativeSentence : Source.Sentence := ((omega (0 : Fin 4)).imp
  ((Formula.mem 1 0).imp
  ((Formula.mem 2 0).imp
  (((product 0 1 2 3).iff (product 0 2 1 3)))))).close

def associativeSentence : Source.Sentence := ((omega (0 : Fin 7)).imp
  ((Formula.mem 1 0).imp
  ((Formula.mem 2 0).imp
  ((Formula.mem 3 0).imp
  ((product 0 1 2 4).imp
  ((product 0 2 3 5).imp
  (((product 0 4 3 6).iff (product 0 1 5 6))))))))).close

def unitSentence : Source.Sentence := ((omega (0 : Fin 5)).imp
  ((Formula.mem 1 0).imp
  ((empty 2).imp
  ((successor 3 2).imp
  ((((product 0 1 3 4).iff (.equal 4 1)).conj ((product 0 3 1 4).iff (.equal 4 1)))))))).close

theorem source_sumRight : Derives (Source.SetLanguage.ZF.at 0) sumRightSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 8 :=
    (Context.add (product 0 1 3 6)
    (Context.add (sum 0 2 3 5)
    (Context.add (product 0 1 2 4)
    (Context.add (Formula.mem 3 0)
    (Context.add (Formula.mem 2 0)
    (Context.add (Formula.mem 1 0)
    (Context.add (omega 0)
    (Source.SetLanguage.ZF.at 8))))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 8
  exact NaturalMultiplicationDistributive.distributive_iff hZ 0 1 2 4 3 5 6 7
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inr (Or.inl rfl)))
    (.hyp (Or.inl rfl))

theorem sumRight_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence sumRightSentence) := TheoryTransport.sentence source_sumRight
theorem native_sumRight : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence sumRightSentence) :=
  ZFReplay.replay sumRight_kernel_certificate

theorem source_sumLeft : Derives (Source.SetLanguage.ZF.at 0) sumLeftSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 8 :=
    (Context.add (product 0 2 3 6)
    (Context.add (product 0 1 3 5)
    (Context.add (sum 0 1 2 4)
    (Context.add (Formula.mem 3 0)
    (Context.add (Formula.mem 2 0)
    (Context.add (Formula.mem 1 0)
    (Context.add (omega 0)
    (Source.SetLanguage.ZF.at 8))))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 8
  exact NaturalMultiplicationAlgebraLaws.left_distributive_iff hZ 0 1 2 3 4 5 6 7
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inr (Or.inl rfl)))
    (.hyp (Or.inl rfl))

theorem sumLeft_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence sumLeftSentence) := TheoryTransport.sentence source_sumLeft
theorem native_sumLeft : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence sumLeftSentence) :=
  ZFReplay.replay sumLeft_kernel_certificate

theorem source_leftSuccessor : Derives (Source.SetLanguage.ZF.at 0) leftSuccessorSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 6 :=
    (Context.add (product 0 1 3 4)
    (Context.add (successor 2 1)
    (Context.add (Formula.mem 3 0)
    (Context.add (Formula.mem 1 0)
    (Context.add (omega 0)
    (Source.SetLanguage.ZF.at 6))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 6
  exact NaturalMultiplicationShift.shift_iff hZ 0 1 2 3 4 5
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
    (Context.add (omega 0)
    (Source.SetLanguage.ZF.at 4))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 4
  exact NaturalMultiplicationCommutative.commutative_iff hZ 0 1 2 3
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
    (Context.add (product 0 2 3 5)
    (Context.add (product 0 1 2 4)
    (Context.add (Formula.mem 3 0)
    (Context.add (Formula.mem 2 0)
    (Context.add (Formula.mem 1 0)
    (Context.add (omega 0)
    (Source.SetLanguage.ZF.at 7)))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 7
  exact NaturalMultiplicationAssociative.associative_iff hZ 0 1 2 4 3 5 6
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

theorem source_unit : Derives (Source.SetLanguage.ZF.at 0) unitSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 5 :=
    (Context.add (successor 3 2)
    (Context.add (empty 2)
    (Context.add (Formula.mem 1 0)
    (Context.add (omega 0)
    (Source.SetLanguage.ZF.at 5)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 5
  exact NaturalMultiplicationAlgebraLaws.unit_iff hZ 0 1 2 3 4
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inr (Or.inl rfl)))
    (.hyp (Or.inl rfl))

theorem unit_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence unitSentence) := TheoryTransport.sentence source_unit
theorem native_unit : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence unitSentence) :=
  ZFReplay.replay unit_kernel_certificate

end PPAC.Migration.Internal.ObjectNaturalMultiplicationAlgebra
