import PPAC.Migration.Internal.StructuralTreeDecode

/-! 实际树求值、全内部递归判定与唯一节点解码的原YesMetaZFC核闭句。 -/
namespace PPAC.Migration.Internal.ObjectStructuralTreeCheck
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax OrdinalSyntax StructuralTreeEvaluationSyntax StructuralTreeRecursiveSyntax StructuralTreeValiditySyntax

def fiberSentence : Source.Sentence := (((ordinal 3).imp (fiber 0 1 2 3)) : Formula 4).close

def naturalValueSentence : Source.Sentence := (((omega 0).imp ((Formula.mem 3 0).imp (existsValue 0 1 2 3))) : Formula 4).close

def valueUniqueSentence : Source.Sentence := (((ordinal 3).imp ((evaluation 0 1 2 3 4).imp ((evaluation 0 1 2 3 5).imp (Formula.equal 4 5)))) : Formula 6).close

def edgeIffSentence : Source.Sentence := (((ordinal 4).imp ((Formula.mem 5 4).imp ((graph 0 1 2 3 4).imp ((edge 3 5 6).iff (evaluation 0 1 2 5 6))))) : Formula 7).close

def historySentence : Source.Sentence := (((ordinal 3).imp ((evaluation 0 1 2 3 4).imp (StructuralTreeHistory.stepHistory 0 1 2 3 4))) : Formula 5).close

def rangeSentence : Source.Sentence := (((omega 0).imp ((empty 1).imp ((successor 2 1).imp ((ordinal 3).imp ((evaluation 0 1 2 3 4).imp ((Formula.mem 4 0).conj ((Formula.equal 4 1).disj (.equal 4 2)))))))) : Formula 5).close

def goodIffSentence : Source.Sentence := (((omega 0).imp ((ordinal 3).imp ((graph 0 1 2 4 3).imp ((StructuralTreeOperatorSyntax.good 0 2 3 4).iff (branch 0 1 2 3))))) : Formula 5).close

def acceptsIffSentence : Source.Sentence := (((omega 0).imp ((empty 1).imp ((successor 2 1).imp ((ordinal 3).imp ((accepts 0 1 2 3).iff (branch 0 1 2 3)))))) : Formula 4).close

def rejectsIffSentence : Source.Sentence := (((omega 0).imp ((empty 1).imp ((successor 2 1).imp ((ordinal 3).imp ((rejects 0 1 2 3).iff (branch 0 1 2 3).neg))))) : Formula 4).close

def fixedClassificationSentence : Source.Sentence := (((omega 0).imp ((empty 1).imp ((successor 2 1).imp ((ordinal 3).imp ((accepts 0 1 2 3).disj (rejects 0 1 2 3)))))) : Formula 4).close

def validAcceptsSentence : Source.Sentence := (((Formula.mem 3 0).imp ((empty 1).imp ((successor 2 1).imp ((valid 0 3).iff (accepts 0 1 2 3))))) : Formula 4).close

def invalidRejectsSentence : Source.Sentence := (((Formula.mem 3 0).imp ((empty 1).imp ((successor 2 1).imp ((invalid 0 3).iff (rejects 0 1 2 3))))) : Formula 4).close

def markerTransportSentence : Source.Sentence := (((Formula.equal 1 4).imp ((Formula.equal 2 5).imp ((accepts 0 1 2 3).imp (accepts 0 4 5 3)))) : Formula 6).close

def classificationSentence : Source.Sentence := (((omega 0).imp ((Formula.mem 1 0).imp ((valid 0 1).disj (invalid 0 1)))) : Formula 2).close

def exclusiveSentence : Source.Sentence := (((omega 0).imp ((valid 0 1).imp ((invalid 0 1).imp (Formula.bot)))) : Formula 2).close

def invalidIffNotSentence : Source.Sentence := (((omega 0).imp ((Formula.mem 1 0).imp ((invalid 0 1).iff (valid 0 1).neg))) : Formula 2).close

def recursiveIffSentence : Source.Sentence := (((omega 0).imp ((recursive 0 1).iff (valid 0 1))) : Formula 2).close

def decodedFiberSentence : Source.Sentence := (((omega 0).imp ((valid 0 1).imp (decodedFiber 0 1))) : Formula 2).close

def decodedIffSentence : Source.Sentence := (((omega 0).imp ((decodedFiber 0 1).iff (valid 0 1))) : Formula 2).close

def decodeUniqueSentence : Source.Sentence := (((omega 0).imp ((nodeData 0 1 2 3 4 5).imp ((nodeData 0 1 6 7 8 9).imp (((Formula.equal 2 6).conj (.equal 3 7)).conj ((Formula.equal 4 8).conj (.equal 5 9)))))) : Formula 10).close

theorem source_fiber : Derives (Source.SetLanguage.ZF.at 0) fiberSentence := by
  apply close_derives
  apply Derives.impI
  let Δ : Context 4 := Context.add (ordinal 3) (Source.SetLanguage.ZF.at 4)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF 4
  exact StructuralTreeEvaluationUnique.exists_unique hZ 0 1 2 3 (.hyp (Or.inl rfl))

theorem fiber_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence fiberSentence) := TheoryTransport.sentence source_fiber

theorem native_fiber : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence fiberSentence) := ZFReplay.replay fiber_kernel_certificate

theorem source_naturalValue : Derives (Source.SetLanguage.ZF.at 0) naturalValueSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 4 := Context.add (Formula.mem 3 0) (Context.add (omega 0) (Source.SetLanguage.ZF.at 4))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 4
  exact StructuralTreeEvaluationExistence.at_natural hZ 0 1 2 3 (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem naturalValue_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence naturalValueSentence) := TheoryTransport.sentence source_naturalValue

theorem native_naturalValue : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence naturalValueSentence) := ZFReplay.replay naturalValue_kernel_certificate

theorem source_valueUnique : Derives (Source.SetLanguage.ZF.at 0) valueUniqueSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 6 := Context.add (evaluation 0 1 2 3 5) (Context.add (evaluation 0 1 2 3 4) (Context.add (ordinal 3) (Source.SetLanguage.ZF.at 6)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 6
  exact StructuralTreeEvaluationUnique.unique hZ 0 1 2 3 4 5 (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem valueUnique_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence valueUniqueSentence) := TheoryTransport.sentence source_valueUnique

theorem native_valueUnique : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence valueUniqueSentence) := ZFReplay.replay valueUnique_kernel_certificate

theorem source_edgeIff : Derives (Source.SetLanguage.ZF.at 0) edgeIffSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 7 := Context.add (graph 0 1 2 3 4) (Context.add (Formula.mem 5 4) (Context.add (ordinal 4) (Source.SetLanguage.ZF.at 7)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 7
  exact StructuralTreeGraphValues.edge_iff_value hZ 0 1 2 3 4 5 6 (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem edgeIff_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence edgeIffSentence) := TheoryTransport.sentence source_edgeIff

theorem native_edgeIff : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence edgeIffSentence) := ZFReplay.replay edgeIff_kernel_certificate

theorem source_history : Derives (Source.SetLanguage.ZF.at 0) historySentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 5 := Context.add (evaluation 0 1 2 3 4) (Context.add (ordinal 3) (Source.SetLanguage.ZF.at 5))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 5
  exact StructuralTreeHistory.from_value hZ 0 1 2 3 4 (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem history_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence historySentence) := TheoryTransport.sentence source_history

theorem native_history : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence historySentence) := ZFReplay.replay history_kernel_certificate

theorem source_range : Derives (Source.SetLanguage.ZF.at 0) rangeSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 5 := Context.add (evaluation 0 1 2 3 4) (Context.add (ordinal 3) (Context.add (successor 2 1) (Context.add (empty 1) (Context.add (omega 0) (Source.SetLanguage.ZF.at 5)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 5
  exact StructuralTreeHistory.range hZ 0 1 2 3 4 (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem range_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence rangeSentence) := TheoryTransport.sentence source_range

theorem native_range : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence rangeSentence) := ZFReplay.replay range_kernel_certificate

theorem source_goodIff : Derives (Source.SetLanguage.ZF.at 0) goodIffSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 5 := Context.add (graph 0 1 2 4 3) (Context.add (ordinal 3) (Context.add (omega 0) (Source.SetLanguage.ZF.at 5)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 5
  exact StructuralTreeRecursiveCorrespondence.good_iff_branch hZ 0 1 2 3 4 (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem goodIff_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence goodIffSentence) := TheoryTransport.sentence source_goodIff

theorem native_goodIff : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence goodIffSentence) := ZFReplay.replay goodIff_kernel_certificate

theorem source_acceptsIff : Derives (Source.SetLanguage.ZF.at 0) acceptsIffSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 4 := Context.add (ordinal 3) (Context.add (successor 2 1) (Context.add (empty 1) (Context.add (omega 0) (Source.SetLanguage.ZF.at 4))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 4
  exact StructuralTreeCheck.accepts_iff_branch hZ 0 1 2 3 (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem acceptsIff_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence acceptsIffSentence) := TheoryTransport.sentence source_acceptsIff

theorem native_acceptsIff : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence acceptsIffSentence) := ZFReplay.replay acceptsIff_kernel_certificate

theorem source_rejectsIff : Derives (Source.SetLanguage.ZF.at 0) rejectsIffSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 4 := Context.add (ordinal 3) (Context.add (successor 2 1) (Context.add (empty 1) (Context.add (omega 0) (Source.SetLanguage.ZF.at 4))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 4
  exact StructuralTreeCheck.rejects_iff_not_branch hZ 0 1 2 3 (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem rejectsIff_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence rejectsIffSentence) := TheoryTransport.sentence source_rejectsIff

theorem native_rejectsIff : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence rejectsIffSentence) := ZFReplay.replay rejectsIff_kernel_certificate

theorem source_fixedClassification : Derives (Source.SetLanguage.ZF.at 0) fixedClassificationSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 4 := Context.add (ordinal 3) (Context.add (successor 2 1) (Context.add (empty 1) (Context.add (omega 0) (Source.SetLanguage.ZF.at 4))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 4
  exact StructuralTreeCheck.classification hZ 0 1 2 3 (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem fixedClassification_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence fixedClassificationSentence) := TheoryTransport.sentence source_fixedClassification

theorem native_fixedClassification : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence fixedClassificationSentence) := ZFReplay.replay fixedClassification_kernel_certificate

theorem source_validAccepts : Derives (Source.SetLanguage.ZF.at 0) validAcceptsSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 4 := Context.add (successor 2 1) (Context.add (empty 1) (Context.add (Formula.mem 3 0) (Source.SetLanguage.ZF.at 4)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 4
  exact StructuralTreeCanonical.valid_iff_accepts hZ 0 1 2 3 (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem validAccepts_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence validAcceptsSentence) := TheoryTransport.sentence source_validAccepts

theorem native_validAccepts : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence validAcceptsSentence) := ZFReplay.replay validAccepts_kernel_certificate

theorem source_invalidRejects : Derives (Source.SetLanguage.ZF.at 0) invalidRejectsSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 4 := Context.add (successor 2 1) (Context.add (empty 1) (Context.add (Formula.mem 3 0) (Source.SetLanguage.ZF.at 4)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 4
  exact StructuralTreeCanonical.invalid_iff_rejects hZ 0 1 2 3 (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem invalidRejects_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence invalidRejectsSentence) := TheoryTransport.sentence source_invalidRejects

theorem native_invalidRejects : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence invalidRejectsSentence) := ZFReplay.replay invalidRejects_kernel_certificate

theorem source_markerTransport : Derives (Source.SetLanguage.ZF.at 0) markerTransportSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact StructuralTreeMarkerTransport.accepts_transport 0 1 2 4 5 3 (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem markerTransport_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence markerTransportSentence) := TheoryTransport.sentence source_markerTransport

theorem native_markerTransport : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence markerTransportSentence) := ZFReplay.replay markerTransport_kernel_certificate

theorem source_classification : Derives (Source.SetLanguage.ZF.at 0) classificationSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 2 := Context.add (Formula.mem 1 0) (Context.add (omega 0) (Source.SetLanguage.ZF.at 2))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 2
  exact StructuralTreeCanonical.classification hZ 0 1 (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem classification_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence classificationSentence) := TheoryTransport.sentence source_classification

theorem native_classification : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence classificationSentence) := ZFReplay.replay classification_kernel_certificate

theorem source_exclusive : Derives (Source.SetLanguage.ZF.at 0) exclusiveSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 2 := Context.add (invalid 0 1) (Context.add (valid 0 1) (Context.add (omega 0) (Source.SetLanguage.ZF.at 2)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 2
  exact StructuralTreeCanonical.exclusive hZ 0 1 (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem exclusive_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence exclusiveSentence) := TheoryTransport.sentence source_exclusive

theorem native_exclusive : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence exclusiveSentence) := ZFReplay.replay exclusive_kernel_certificate

theorem source_invalidIffNot : Derives (Source.SetLanguage.ZF.at 0) invalidIffNotSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 2 := Context.add (Formula.mem 1 0) (Context.add (omega 0) (Source.SetLanguage.ZF.at 2))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 2
  exact StructuralTreeCanonical.invalid_iff_not_valid hZ 0 1 (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem invalidIffNot_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence invalidIffNotSentence) := TheoryTransport.sentence source_invalidIffNot

theorem native_invalidIffNot : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence invalidIffNotSentence) := ZFReplay.replay invalidIffNot_kernel_certificate

theorem source_recursiveIff : Derives (Source.SetLanguage.ZF.at 0) recursiveIffSentence := by
  apply close_derives
  apply Derives.impI
  let Δ : Context 2 := Context.add (omega 0) (Source.SetLanguage.ZF.at 2)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF 2
  exact StructuralTreeDecode.recursive_iff_valid hZ 0 1 (.hyp (Or.inl rfl))

theorem recursiveIff_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence recursiveIffSentence) := TheoryTransport.sentence source_recursiveIff

theorem native_recursiveIff : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence recursiveIffSentence) := ZFReplay.replay recursiveIff_kernel_certificate

theorem source_decodedFiber : Derives (Source.SetLanguage.ZF.at 0) decodedFiberSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 2 := Context.add (valid 0 1) (Context.add (omega 0) (Source.SetLanguage.ZF.at 2))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 2
  exact StructuralTreeDecode.exists_unique hZ 0 1 (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem decodedFiber_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence decodedFiberSentence) := TheoryTransport.sentence source_decodedFiber

theorem native_decodedFiber : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence decodedFiberSentence) := ZFReplay.replay decodedFiber_kernel_certificate

theorem source_decodedIff : Derives (Source.SetLanguage.ZF.at 0) decodedIffSentence := by
  apply close_derives
  apply Derives.impI
  let Δ : Context 2 := Context.add (omega 0) (Source.SetLanguage.ZF.at 2)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF 2
  exact StructuralTreeDecode.decoded_iff_valid hZ 0 1 (.hyp (Or.inl rfl))

theorem decodedIff_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence decodedIffSentence) := TheoryTransport.sentence source_decodedIff

theorem native_decodedIff : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence decodedIffSentence) := ZFReplay.replay decodedIff_kernel_certificate

theorem source_decodeUnique : Derives (Source.SetLanguage.ZF.at 0) decodeUniqueSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 10 := Context.add (nodeData 0 1 6 7 8 9) (Context.add (nodeData 0 1 2 3 4 5) (Context.add (omega 0) (Source.SetLanguage.ZF.at 10)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 10
  exact StructuralTreeDecode.unique_pair hZ 0 1 2 3 4 5 6 7 8 9 (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem decodeUnique_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence decodeUniqueSentence) := TheoryTransport.sentence source_decodeUnique

theorem native_decodeUnique : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence decodeUniqueSentence) := ZFReplay.replay decodeUnique_kernel_certificate

end PPAC.Migration.Internal.ObjectStructuralTreeCheck
