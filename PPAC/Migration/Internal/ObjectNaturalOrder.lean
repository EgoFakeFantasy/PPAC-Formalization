import PPAC.Migration.Internal.NaturalOrderBasic

namespace PPAC.Migration.Internal.ObjectNaturalOrder
open Source SourceAlgebra SourceLogic OmegaSyntax
open NaturalAdditionSyntax (sum)
open NaturalMultiplicationSyntax (product)
open NaturalAdditionBounds (below)

def totalSentence : Source.Sentence := ((omega (0 : Fin 3)).imp
  ((Formula.mem 1 0).imp
  ((Formula.mem 2 0).imp
  (((below 1 2).disj (below 2 1)))))).close

def transitiveSentence : Source.Sentence := ((omega (0 : Fin 4)).imp
  ((Formula.mem 1 0).imp
  ((Formula.mem 2 0).imp
  ((Formula.mem 3 0).imp
  ((below 1 2).imp
  ((below 2 3).imp
  ((below 1 3)))))))).close

def antisymmetricSentence : Source.Sentence := ((omega (0 : Fin 3)).imp
  ((Formula.mem 1 0).imp
  ((Formula.mem 2 0).imp
  ((below 1 2).imp
  ((below 2 1).imp
  ((Formula.equal 1 2))))))).close

def successorSentence : Source.Sentence := ((successor (2 : Fin 3) 1).imp
  (((Formula.mem 0 2).iff (below 0 1)))).close

theorem source_total : Derives (Source.SetLanguage.ZF.at 0) totalSentence := by
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
  exact NaturalOrderBasic.total hZ 0 1 2
    (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inr (Or.inl rfl)))
    (.hyp (Or.inl rfl))

theorem total_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence totalSentence) := TheoryTransport.sentence source_total
theorem native_total : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence totalSentence) :=
  ZFReplay.replay total_kernel_certificate

theorem source_transitive : Derives (Source.SetLanguage.ZF.at 0) transitiveSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 4 :=
    (Context.add (below 2 3)
    (Context.add (below 1 2)
    (Context.add (Formula.mem 3 0)
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
  exact NaturalOrderBasic.transitive hZ 0 1 2 3
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
    (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inr (Or.inl rfl)))
    (.hyp (Or.inl rfl))

theorem transitive_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence transitiveSentence) := TheoryTransport.sentence source_transitive
theorem native_transitive : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence transitiveSentence) :=
  ZFReplay.replay transitive_kernel_certificate

theorem source_antisymmetric : Derives (Source.SetLanguage.ZF.at 0) antisymmetricSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 3 :=
    (Context.add (below 2 1)
    (Context.add (below 1 2)
    (Context.add (Formula.mem 2 0)
    (Context.add (Formula.mem 1 0)
    (Context.add (omega 0)
    (Source.SetLanguage.ZF.at 3))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 3
  exact NaturalOrderBasic.antisymmetric hZ 0 1 2
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    (.hyp (Or.inr (Or.inl rfl)))
    (.hyp (Or.inl rfl))

theorem antisymmetric_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence antisymmetricSentence) := TheoryTransport.sentence source_antisymmetric
theorem native_antisymmetric : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence antisymmetricSentence) :=
  ZFReplay.replay antisymmetric_kernel_certificate

theorem source_successor : Derives (Source.SetLanguage.ZF.at 0) successorSentence := by
  apply close_derives
  apply Derives.impI
  exact NaturalOrderBasic.successor_iff 0 1 2
    (.hyp (Or.inl rfl))

theorem successor_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence successorSentence) := TheoryTransport.sentence source_successor
theorem native_successor : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence successorSentence) :=
  ZFReplay.replay successor_kernel_certificate

end PPAC.Migration.Internal.ObjectNaturalOrder
