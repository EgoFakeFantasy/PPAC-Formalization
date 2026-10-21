import PPAC.Migration.Internal.NaturalAdditionReassociation

namespace PPAC.Migration.Internal.ObjectNaturalAdditionReassociation
open Source SourceAlgebra SourceLogic OmegaSyntax NaturalAdditionSyntax
open NaturalMultiplicationSyntax (product)

def swapSentence : Source.Sentence := ((omega (0 : Fin 7)).imp
  ((Formula.mem 1 0).imp
  ((Formula.mem 2 0).imp
  ((Formula.mem 3 0).imp
  ((sum 0 1 2 4).imp
  ((sum 0 1 3 5).imp
  ((sum 0 4 3 6).imp
  ((sum 0 5 2 6))))))))).close

def interchangeSentence : Source.Sentence := ((omega (0 : Fin 10)).imp
  ((Formula.mem 1 0).imp
  ((Formula.mem 2 0).imp
  ((Formula.mem 3 0).imp
  ((Formula.mem 4 0).imp
  ((sum 0 1 2 5).imp
  ((sum 0 3 4 6).imp
  ((sum 0 1 3 7).imp
  ((sum 0 2 4 8).imp
  ((sum 0 5 6 9).imp
  ((sum 0 7 8 9)))))))))))).close

theorem source_swap : Derives (Source.SetLanguage.ZF.at 0) swapSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 7 :=
    (Context.add (sum 0 4 3 6)
    (Context.add (sum 0 1 3 5)
    (Context.add (sum 0 1 2 4)
    (Context.add (Formula.mem 3 0)
    (Context.add (Formula.mem 2 0)
    (Context.add (Formula.mem 1 0)
    (Context.add (omega 0)
    (Source.SetLanguage.ZF.at 7))))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 7
  exact NaturalAdditionReassociation.swap_middle hZ 0 1 2 3 4 5 6
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inr (Or.inl rfl)))
    (.hyp (Or.inl rfl))

theorem swap_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence swapSentence) := TheoryTransport.sentence source_swap
theorem native_swap : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence swapSentence) :=
  ZFReplay.replay swap_kernel_certificate

theorem source_interchange : Derives (Source.SetLanguage.ZF.at 0) interchangeSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 10 :=
    (Context.add (sum 0 5 6 9)
    (Context.add (sum 0 2 4 8)
    (Context.add (sum 0 1 3 7)
    (Context.add (sum 0 3 4 6)
    (Context.add (sum 0 1 2 5)
    (Context.add (Formula.mem 4 0)
    (Context.add (Formula.mem 3 0)
    (Context.add (Formula.mem 2 0)
    (Context.add (Formula.mem 1 0)
    (Context.add (omega 0)
    (Source.SetLanguage.ZF.at 10)))))))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 10
  exact NaturalAdditionReassociation.interchange hZ 0 1 2 3 4 5 6 7 8 9
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inr (Or.inl rfl)))
    (.hyp (Or.inl rfl))

theorem interchange_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence interchangeSentence) := TheoryTransport.sentence source_interchange
theorem native_interchange : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence interchangeSentence) :=
  ZFReplay.replay interchange_kernel_certificate

end PPAC.Migration.Internal.ObjectNaturalAdditionReassociation
