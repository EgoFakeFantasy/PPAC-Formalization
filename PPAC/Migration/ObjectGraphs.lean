import PPAC.Migration.SingletonMap
import PPAC.Migration.GraphProperties

/-! 对象函数图的实际全量词闭句，原PP/AC的edge与functionOn定义保持不变。 -/
namespace PPAC.Migration.ObjectGraphs
open Source SourceAlgebra SourceLogic PairSyntax GraphSyntax

abbrev assumptions := ObjectPairs.assumptions

def singletonSentence : Source.Sentence := (SingletonMap.existsMap (0 : Fin 2) 1).close

def evaluationSentence : Source.Sentence :=
  ((pair (0 : Fin 6) 1 1).imp ((ordered 1 2 3).imp
    ((edge 0 4 5).iff ((Formula.equal 4 2).conj (.equal 5 3))))).close

def domainSentence : Source.Sentence :=
  ((functionOn (0 : Fin 4) 1).imp ((edge 0 2 3).imp (.mem 2 1))).close

def singleValuedSentence : Source.Sentence :=
  ((functionOn (0 : Fin 5) 1).imp ((edge 0 2 3).imp ((edge 0 2 4).imp (.equal 3 4)))).close

def totalSentence : Source.Sentence :=
  ((functionOn (0 : Fin 3) 1).imp ((Formula.mem 2 1).imp (hasEdge 0 2))).close

theorem source_total : Derives (assumptions.at 0) totalSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  exact GraphProperties.output_exists 0 1 2 (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem source_singleton : Derives (assumptions.at 0) singletonSentence := by
  apply close_derives
  exact SingletonMap.exists_map 0 1 (.hyp ⟨_, Or.inl rfl, rfl⟩) (.hyp ⟨_, Or.inr rfl, rfl⟩)

theorem source_evaluation : Derives (assumptions.at 0) evaluationSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  have he : Derives (assumptions.at 6) (Source.SetLanguage.extensionality.rename Fin.elim0) :=
    .hyp ⟨_, Or.inr rfl, rfl⟩
  exact SingletonGraphLogic.edge_iff 0 1 2 3 4 5 (add (add he _) _)
    (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem source_domain : Derives (assumptions.at 0) domainSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  have he : Derives (assumptions.at 4) (Source.SetLanguage.extensionality.rename Fin.elim0) :=
    .hyp ⟨_, Or.inr rfl, rfl⟩
  exact GraphProperties.domain_of_edge 0 1 2 3 (add (add he _) _)
    (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem source_single_valued : Derives (assumptions.at 0) singleValuedSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  have he : Derives (assumptions.at 5) (Source.SetLanguage.extensionality.rename Fin.elim0) :=
    .hyp ⟨_, Or.inr rfl, rfl⟩
  exact GraphProperties.single_valued 0 1 2 3 4 (add (add (add he _) _) _)
    (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem singleton_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives
    (TheoryTransport.theory assumptions) [] (Translation.sentence singletonSentence) :=
  TheoryTransport.sentence source_singleton

theorem source_ZF_singleton : Derives (Source.SetLanguage.ZF.at 0) singletonSentence :=
  ObjectPairs.source_ZF_replay source_singleton

theorem native_singleton : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence singletonSentence) :=
  ObjectPairs.native_replay singleton_kernel_certificate

theorem evaluation_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives
    (TheoryTransport.theory assumptions) [] (Translation.sentence evaluationSentence) :=
  TheoryTransport.sentence source_evaluation

theorem source_ZF_evaluation : Derives (Source.SetLanguage.ZF.at 0) evaluationSentence :=
  ObjectPairs.source_ZF_replay source_evaluation

theorem native_evaluation : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence evaluationSentence) :=
  ObjectPairs.native_replay evaluation_kernel_certificate

theorem domain_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives
    (TheoryTransport.theory assumptions) [] (Translation.sentence domainSentence) :=
  TheoryTransport.sentence source_domain

theorem source_ZF_domain : Derives (Source.SetLanguage.ZF.at 0) domainSentence :=
  ObjectPairs.source_ZF_replay source_domain

theorem native_domain : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence domainSentence) :=
  ObjectPairs.native_replay domain_kernel_certificate

theorem single_valued_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives
    (TheoryTransport.theory assumptions) [] (Translation.sentence singleValuedSentence) :=
  TheoryTransport.sentence source_single_valued

theorem source_ZF_single_valued : Derives (Source.SetLanguage.ZF.at 0) singleValuedSentence :=
  ObjectPairs.source_ZF_replay source_single_valued

theorem native_single_valued : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence singleValuedSentence) :=
  ObjectPairs.native_replay single_valued_kernel_certificate
theorem total_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives
    (TheoryTransport.theory assumptions) [] (Translation.sentence totalSentence) := TheoryTransport.sentence source_total

theorem source_ZF_total : Derives (Source.SetLanguage.ZF.at 0) totalSentence := ObjectPairs.source_ZF_replay source_total

theorem native_total : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence totalSentence) := ObjectPairs.native_replay total_kernel_certificate
end PPAC.Migration.ObjectGraphs
