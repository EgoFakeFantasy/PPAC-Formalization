import PPAC.Migration.Internal.StructuralTreeRecursors

/-! 严格较小子码上的具体树二值算子及其实际唯一内部递归图的原核闭句。 -/
namespace PPAC.Migration.Internal.ObjectStructuralTreeOperator
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax StructuralTreeOperatorSyntax

def shapeBoundSentence : Source.Sentence := ((((omega 0).imp ((shape 0 1 2 3 4 5).imp ((edge 5 6 7).imp (Formula.mem 7 1)))) : Formula 8)).close

def childrenIffSentence : Source.Sentence := ((((omega 0).imp ((shape 0 1 2 3 4 5).imp ((marks 6 5 7).iff (children 6 1 5 7)))) : Formula 8)).close

def leafGoodSentence : Source.Sentence := ((((omega 0).imp ((shape 0 2 4 5 6 7).imp ((empty 6).imp (good 0 1 2 3)))) : Formula 8)).close

def positiveGoodSentence : Source.Sentence := ((((good 0 1 2 3).imp ((empty 2).neg)) : Formula 4)).close

def rangeSentence : Source.Sentence := ((((omega 0).imp ((empty 1).imp ((successor 2 1).imp ((step 0 1 2 3 4 5).imp ((Formula.mem 5 0).conj ((Formula.equal 5 1).disj (.equal 5 2))))))) : Formula 6)).close

def zeroSentence : Source.Sentence := ((((empty 3).imp ((step 0 1 2 3 4 5).imp (Formula.equal 5 1))) : Formula 6)).close

def functionalSentence : Source.Sentence := ((((step 0 1 2 3 4 5).imp ((step 0 1 2 3 4 6).imp (Formula.equal 5 6))) : Formula 7)).close

def recursorsSentence : Source.Sentence := (((recursors 0 1 2) : Formula 3)).close

def ordinalFiberSentence : Source.Sentence := ((((OrdinalSyntax.ordinal 3).imp (OrdinalRecursionExistenceSyntax.fiber StructuralTreeOperatorSyntax.matrix (NaturalAdditionTransport.params3 0 1 2) 3)) : Formula 4)).close

def actualUnitsSentence : Source.Sentence := ((((omega 0).imp (actualRecursors 0)) : Formula 1)).close

theorem source_shapeBound : Derives (Source.SetLanguage.ZF.at 0) shapeBoundSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 8 := (Context.add (edge 5 6 7) (Context.add (shape 0 1 2 3 4 5) (Context.add (omega 0) (Source.SetLanguage.ZF.at 8))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 8
  exact StructuralTreeOperatorLogic.shape_edge_bound hZ 0 1 2 3 4 5 6 7 (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem shapeBound_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence shapeBoundSentence) := TheoryTransport.sentence source_shapeBound

theorem native_shapeBound : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence shapeBoundSentence) := ZFReplay.replay shapeBound_kernel_certificate

theorem source_childrenIff : Derives (Source.SetLanguage.ZF.at 0) childrenIffSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 8 := (Context.add (shape 0 1 2 3 4 5) (Context.add (omega 0) (Source.SetLanguage.ZF.at 8)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 8
  exact StructuralTreeOperatorLogic.children_iff hZ 0 1 2 3 4 5 6 7 (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem childrenIff_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence childrenIffSentence) := TheoryTransport.sentence source_childrenIff

theorem native_childrenIff : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence childrenIffSentence) := ZFReplay.replay childrenIff_kernel_certificate

theorem source_leafGood : Derives (Source.SetLanguage.ZF.at 0) leafGoodSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 8 := (Context.add (empty 6) (Context.add (shape 0 2 4 5 6 7) (Context.add (omega 0) (Source.SetLanguage.ZF.at 8))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 8
  exact StructuralTreeOperatorLogic.leaf_good hZ 0 1 2 3 4 5 6 7 (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem leafGood_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence leafGoodSentence) := TheoryTransport.sentence source_leafGood

theorem native_leafGood : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence leafGoodSentence) := ZFReplay.replay leafGood_kernel_certificate

theorem source_positiveGood : Derives (Source.SetLanguage.ZF.at 0) positiveGoodSentence := by
  apply close_derives
  apply Derives.impI
  exact StructuralTreeOperatorLogic.positive_good 0 1 2 3 (.hyp (Or.inl rfl))

theorem positiveGood_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence positiveGoodSentence) := TheoryTransport.sentence source_positiveGood

theorem native_positiveGood : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence positiveGoodSentence) := ZFReplay.replay positiveGood_kernel_certificate

theorem source_range : Derives (Source.SetLanguage.ZF.at 0) rangeSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 6 := (Context.add (step 0 1 2 3 4 5) (Context.add (successor 2 1) (Context.add (empty 1) (Context.add (omega 0) (Source.SetLanguage.ZF.at 6)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 6
  exact StructuralTreeOperatorStep.range hZ 0 1 2 3 4 5 (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem range_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence rangeSentence) := TheoryTransport.sentence source_range

theorem native_range : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence rangeSentence) := ZFReplay.replay range_kernel_certificate

theorem source_zero : Derives (Source.SetLanguage.ZF.at 0) zeroSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  exact StructuralTreeOperatorStep.on_zero 0 1 2 3 4 5 (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem zero_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence zeroSentence) := TheoryTransport.sentence source_zero

theorem native_zero : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence zeroSentence) := ZFReplay.replay zero_kernel_certificate

theorem source_functional : Derives (Source.SetLanguage.ZF.at 0) functionalSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  exact StructuralTreeOperatorStep.functional_point 0 1 2 3 4 5 6 (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem functional_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence functionalSentence) := TheoryTransport.sentence source_functional

theorem native_functional : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence functionalSentence) := ZFReplay.replay functional_kernel_certificate

theorem source_recursors : Derives (Source.SetLanguage.ZF.at 0) recursorsSentence := by
  apply close_derives
  let Δ : Context 3 := (Source.SetLanguage.ZF.at 3)
  have hZ : ZFContext.Evidence Δ := by
    exact ZFContext.source_ZF 3
  exact StructuralTreeRecursors.all_unique hZ 0 1 2

theorem recursors_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence recursorsSentence) := TheoryTransport.sentence source_recursors

theorem native_recursors : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence recursorsSentence) := ZFReplay.replay recursors_kernel_certificate

theorem source_ordinalFiber : Derives (Source.SetLanguage.ZF.at 0) ordinalFiberSentence := by
  apply close_derives
  apply Derives.impI
  let Δ : Context 4 := (Context.add (OrdinalSyntax.ordinal 3) (Source.SetLanguage.ZF.at 4))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF 4
  exact StructuralTreeRecursors.at_ordinal hZ 0 1 2 3 (.hyp (Or.inl rfl))

theorem ordinalFiber_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence ordinalFiberSentence) := TheoryTransport.sentence source_ordinalFiber

theorem native_ordinalFiber : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence ordinalFiberSentence) := ZFReplay.replay ordinalFiber_kernel_certificate

theorem source_actualUnits : Derives (Source.SetLanguage.ZF.at 0) actualUnitsSentence := by
  apply close_derives
  apply Derives.impI
  let Δ : Context 1 := (Context.add (omega 0) (Source.SetLanguage.ZF.at 1))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF 1
  exact StructuralTreeRecursors.actual_units_recursors hZ 0 (.hyp (Or.inl rfl))

theorem actualUnits_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence actualUnitsSentence) := TheoryTransport.sentence source_actualUnits

theorem native_actualUnits : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence actualUnitsSentence) := ZFReplay.replay actualUnits_kernel_certificate

end PPAC.Migration.Internal.ObjectStructuralTreeOperator
