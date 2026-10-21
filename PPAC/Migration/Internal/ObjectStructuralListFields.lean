import PPAC.Migration.Internal.StructuralListFieldTrace

/-! 实际完整有序字段图和唯一列表解码的原核闭句；不宣称逆编码往返已完成。 -/
namespace PPAC.Migration.Internal.ObjectStructuralListFields
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax NaturalAdditionSyntax StructuralListSyntax StructuralListLengthSyntax StructuralListFieldSyntax StructuralListFieldPairSyntax StructuralListFieldGraphSyntax
open StructuralListTraceSyntax (valid)

def valueFiberSentence : Source.Sentence := ((((omega 0).imp ((Formula.mem 2 0).imp (StructuralListFieldSyntax.fiber 0 1 2))) : Formula 3)).close

def valueRangeSentence : Source.Sentence := ((((omega 0).imp ((field 0 1 2 3).imp (Formula.mem 3 0))) : Formula 4)).close

def zeroSentence : Source.Sentence := ((((omega 0).imp ((Formula.mem 1 0).imp ((Formula.mem 2 0).imp ((consCode 0 1 2 3).imp ((empty 4).imp ((field 0 3 4 5).iff (.equal 5 1))))))) : Formula 6)).close

def successorSentence : Source.Sentence := ((((omega 0).imp ((Formula.mem 1 0).imp ((Formula.mem 2 0).imp ((Formula.mem 4 0).imp ((successor 5 4).imp ((consCode 0 1 2 3).imp ((field 0 3 5 6).iff (field 0 2 4 6)))))))) : Formula 7)).close

def pairFiberSentence : Source.Sentence := ((((omega 0).imp ((Formula.mem 2 0).imp (pairFiber 0 1 2))) : Formula 3)).close

def rawExistsSentence : Source.Sentence := ((((omega 0).imp ((Formula.mem 2 0).imp (existsGraph 0 1 2))) : Formula 3)).close

def edgeLawSentence : Source.Sentence := ((((graph 0 1 2 3).imp (edgeLaw 0 1 2 3)) : Formula 4)).close

def completeSentence : Source.Sentence := ((((omega 0).imp ((Formula.mem 2 0).imp ((graph 0 1 2 3).imp (fields 0 1 2 3)))) : Formula 4)).close

def graphUniqueSentence : Source.Sentence := ((((graph 0 1 2 3).imp ((graph 0 1 2 4).imp (Formula.equal 3 4))) : Formula 5)).close

def fiberSentence : Source.Sentence := ((((omega 0).imp ((Formula.mem 2 0).imp (fieldsFiber 0 1 2))) : Formula 3)).close

def atLengthSentence : Source.Sentence := ((((omega 0).imp ((hasLength 0 1 2).imp (fieldsFiber 0 1 2))) : Formula 3)).close

def decodeSentence : Source.Sentence := ((((omega 0).imp ((valid 0 1).imp (decoded 0 1))) : Formula 2)).close

def decodeIffSentence : Source.Sentence := ((((omega 0).imp ((valid 0 1).iff (decoded 0 1))) : Formula 2)).close

def decodeUniqueSentence : Source.Sentence := ((((omega 0).imp ((hasLength 0 1 2).imp ((hasLength 0 1 3).imp ((fields 0 1 2 4).imp ((fields 0 1 3 5).imp ((Formula.equal 2 3).conj (.equal 4 5))))))) : Formula 6)).close

def traceHeadSentence : Source.Sentence := ((((omega 0).imp ((StructuralListTraceSyntax.trace 0 1 2 3 4 5 6).imp ((Formula.mem 7 0).imp ((Formula.mem 8 0).imp ((Formula.mem 10 0).imp ((Formula.mem 11 0).imp ((sum 0 7 8 3).imp ((edge 5 8 9).imp ((consCode 0 11 10 9).imp ((field 0 6 7 12).iff (.equal 12 11))))))))))) : Formula 13)).close

theorem source_valueFiber : Derives (Source.SetLanguage.ZF.at 0) valueFiberSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI

  let Δ : Context 3 := Context.add (Formula.mem 2 0) (Context.add (omega 0) (Source.SetLanguage.ZF.at 3))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 3

  exact StructuralListFieldValues.exists_unique hZ 0 1 2 (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem valueFiber_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence valueFiberSentence) := TheoryTransport.sentence source_valueFiber

theorem native_valueFiber : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence valueFiberSentence) := ZFReplay.replay valueFiber_kernel_certificate

theorem source_valueRange : Derives (Source.SetLanguage.ZF.at 0) valueRangeSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI

  let Δ : Context 4 := Context.add (field 0 1 2 3) (Context.add (omega 0) (Source.SetLanguage.ZF.at 4))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 4

  exact StructuralListFieldValues.range hZ 0 1 2 3 (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem valueRange_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence valueRangeSentence) := TheoryTransport.sentence source_valueRange

theorem native_valueRange : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence valueRangeSentence) := ZFReplay.replay valueRange_kernel_certificate

theorem source_zero : Derives (Source.SetLanguage.ZF.at 0) zeroSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI

  let Δ : Context 6 := Context.add (empty 4) (Context.add (consCode 0 1 2 3) (Context.add (Formula.mem 2 0) (Context.add (Formula.mem 1 0) (Context.add (omega 0) (Source.SetLanguage.ZF.at 6)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 6

  exact StructuralListFieldCons.zero_iff hZ 0 1 2 3 4 5 (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem zero_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence zeroSentence) := TheoryTransport.sentence source_zero

theorem native_zero : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence zeroSentence) := ZFReplay.replay zero_kernel_certificate

theorem source_successor : Derives (Source.SetLanguage.ZF.at 0) successorSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI

  let Δ : Context 7 := Context.add (consCode 0 1 2 3) (Context.add (successor 5 4) (Context.add (Formula.mem 4 0) (Context.add (Formula.mem 2 0) (Context.add (Formula.mem 1 0) (Context.add (omega 0) (Source.SetLanguage.ZF.at 7))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 7

  exact StructuralListFieldCons.successor_iff hZ 0 1 2 3 4 5 6 (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))) (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem successor_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence successorSentence) := TheoryTransport.sentence source_successor

theorem native_successor : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence successorSentence) := ZFReplay.replay successor_kernel_certificate

theorem source_pairFiber : Derives (Source.SetLanguage.ZF.at 0) pairFiberSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI

  let Δ : Context 3 := Context.add (Formula.mem 2 0) (Context.add (omega 0) (Source.SetLanguage.ZF.at 3))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 3

  exact StructuralListFieldPairs.exists_unique hZ 0 1 2 (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem pairFiber_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence pairFiberSentence) := TheoryTransport.sentence source_pairFiber

theorem native_pairFiber : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence pairFiberSentence) := ZFReplay.replay pairFiber_kernel_certificate

theorem source_rawExists : Derives (Source.SetLanguage.ZF.at 0) rawExistsSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI

  let Δ : Context 3 := Context.add (Formula.mem 2 0) (Context.add (omega 0) (Source.SetLanguage.ZF.at 3))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 3

  exact StructuralListFieldPairs.exists_graph hZ 0 1 2 (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem rawExists_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence rawExistsSentence) := TheoryTransport.sentence source_rawExists

theorem native_rawExists : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence rawExistsSentence) := ZFReplay.replay rawExists_kernel_certificate

theorem source_edgeLaw : Derives (Source.SetLanguage.ZF.at 0) edgeLawSentence := by
  apply close_derives
  apply Derives.impI

  let Δ : Context 4 := Context.add (graph 0 1 2 3) (Source.SetLanguage.ZF.at 4)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF 4

  exact StructuralListFieldGraphEdges.full_law hZ 0 1 2 3 (.hyp (Or.inl rfl))

theorem edgeLaw_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence edgeLawSentence) := TheoryTransport.sentence source_edgeLaw

theorem native_edgeLaw : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence edgeLawSentence) := ZFReplay.replay edgeLaw_kernel_certificate

theorem source_complete : Derives (Source.SetLanguage.ZF.at 0) completeSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI

  let Δ : Context 4 := Context.add (graph 0 1 2 3) (Context.add (Formula.mem 2 0) (Context.add (omega 0) (Source.SetLanguage.ZF.at 4)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 4

  exact StructuralListFieldGraphFunction.complete hZ 0 1 2 3 (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem complete_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence completeSentence) := TheoryTransport.sentence source_complete

theorem native_complete : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence completeSentence) := ZFReplay.replay complete_kernel_certificate

theorem source_graphUnique : Derives (Source.SetLanguage.ZF.at 0) graphUniqueSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI

  let Δ : Context 5 := Context.add (graph 0 1 2 4) (Context.add (graph 0 1 2 3) (Source.SetLanguage.ZF.at 5))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 5

  exact StructuralListFieldGraphFiber.unique hZ 0 1 2 3 4 (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem graphUnique_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence graphUniqueSentence) := TheoryTransport.sentence source_graphUnique

theorem native_graphUnique : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence graphUniqueSentence) := ZFReplay.replay graphUnique_kernel_certificate

theorem source_fiber : Derives (Source.SetLanguage.ZF.at 0) fiberSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI

  let Δ : Context 3 := Context.add (Formula.mem 2 0) (Context.add (omega 0) (Source.SetLanguage.ZF.at 3))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 3

  exact StructuralListFieldGraphFiber.exists_unique hZ 0 1 2 (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem fiber_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence fiberSentence) := TheoryTransport.sentence source_fiber

theorem native_fiber : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence fiberSentence) := ZFReplay.replay fiber_kernel_certificate

theorem source_atLength : Derives (Source.SetLanguage.ZF.at 0) atLengthSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI

  let Δ : Context 3 := Context.add (hasLength 0 1 2) (Context.add (omega 0) (Source.SetLanguage.ZF.at 3))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 3

  exact StructuralListFieldDecode.at_length hZ 0 1 2 (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem atLength_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence atLengthSentence) := TheoryTransport.sentence source_atLength

theorem native_atLength : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence atLengthSentence) := ZFReplay.replay atLength_kernel_certificate

theorem source_decode : Derives (Source.SetLanguage.ZF.at 0) decodeSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI

  let Δ : Context 2 := Context.add (valid 0 1) (Context.add (omega 0) (Source.SetLanguage.ZF.at 2))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 2

  exact StructuralListFieldDecode.exists_decoded hZ 0 1 (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem decode_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence decodeSentence) := TheoryTransport.sentence source_decode

theorem native_decode : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence decodeSentence) := ZFReplay.replay decode_kernel_certificate

theorem source_decodeIff : Derives (Source.SetLanguage.ZF.at 0) decodeIffSentence := by
  apply close_derives
  apply Derives.impI

  let Δ : Context 2 := Context.add (omega 0) (Source.SetLanguage.ZF.at 2)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF 2

  exact StructuralListFieldDecode.decoded_iff hZ 0 1 (.hyp (Or.inl rfl))

theorem decodeIff_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence decodeIffSentence) := TheoryTransport.sentence source_decodeIff

theorem native_decodeIff : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence decodeIffSentence) := ZFReplay.replay decodeIff_kernel_certificate

theorem source_decodeUnique : Derives (Source.SetLanguage.ZF.at 0) decodeUniqueSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI

  let Δ : Context 6 := Context.add (fields 0 1 3 5) (Context.add (fields 0 1 2 4) (Context.add (hasLength 0 1 3) (Context.add (hasLength 0 1 2) (Context.add (omega 0) (Source.SetLanguage.ZF.at 6)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 6

  exact StructuralListFieldDecode.unique_pair hZ 0 1 2 3 4 5 (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem decodeUnique_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence decodeUniqueSentence) := TheoryTransport.sentence source_decodeUnique

theorem native_decodeUnique : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence decodeUniqueSentence) := ZFReplay.replay decodeUnique_kernel_certificate

theorem source_traceHead : Derives (Source.SetLanguage.ZF.at 0) traceHeadSentence := by
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

  let Δ : Context 13 := Context.add (consCode 0 11 10 9) (Context.add (edge 5 8 9) (Context.add (sum 0 7 8 3) (Context.add (Formula.mem 11 0) (Context.add (Formula.mem 10 0) (Context.add (Formula.mem 8 0) (Context.add (Formula.mem 7 0) (Context.add (StructuralListTraceSyntax.trace 0 1 2 3 4 5 6) (Context.add (omega 0) (Source.SetLanguage.ZF.at 13)))))))))
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
    exact ZFContext.source_ZF 13

  exact StructuralListFieldTrace.head_iff hZ 0 1 2 3 4 5 6 7 8 9 10 11 12 (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))) (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))) (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))) (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))) (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem traceHead_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence traceHeadSentence) := TheoryTransport.sentence source_traceHead

theorem native_traceHead : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence traceHeadSentence) := ZFReplay.replay traceHead_kernel_certificate

end PPAC.Migration.Internal.ObjectStructuralListFields
