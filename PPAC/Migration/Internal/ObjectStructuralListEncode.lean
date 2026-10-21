import PPAC.Migration.Internal.StructuralListEncodeReadback

/-! 任意内部完整ω值序列的实际原列表逆编码及字段图读回的原核闭句。 -/
namespace PPAC.Migration.Internal.ObjectStructuralListEncode
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax SequenceSyntax NaturalAdditionSyntax StructuralListSyntax StructuralListLengthSyntax StructuralListFieldPairSyntax StructuralListFieldGraphSyntax StructuralListSuffixSyntax StructuralListEncodeSyntax
open StructuralListTraceSyntax (valid)

def nilLengthSentence : Source.Sentence := ((((omega 0).imp ((nilCode 0 1).imp ((empty 2).imp (hasLength 0 1 2)))) : Formula 3)).close

def consLengthSentence : Source.Sentence := ((((omega 0).imp ((Formula.mem 1 0).imp ((consCode 0 1 2 3).imp ((hasLength 0 2 4).imp ((successor 5 4).imp (hasLength 0 3 5)))))) : Formula 6)).close

def emptyLengthSentence : Source.Sentence := ((((hasLength 0 1 2).imp ((empty 2).imp (nilCode 0 1))) : Formula 3)).close

def offsetSentence : Source.Sentence := ((((omega 0).imp ((Formula.mem 1 0).imp ((Formula.mem 3 0).imp ((successor 2 1).imp ((successor 4 3).imp ((sum 0 1 4 5).imp (sum 0 2 3 5))))))) : Formula 6)).close

def suffixZeroSentence : Source.Sentence := ((((omega 0).imp ((empty 3).imp (existsCode 0 1 2 3))) : Formula 4)).close

def suffixConsSentence : Source.Sentence := ((((omega 0).imp ((sequence 1 2 0).imp ((Formula.mem 5 0).imp ((Formula.mem 3 0).imp ((successor 6 5).imp ((successor 4 3).imp ((Formula.mem 7 0).imp ((Formula.mem 8 0).imp ((consCode 0 7 8 9).imp ((edge 1 3 7).imp ((aligned 0 1 4 5 8).imp (aligned 0 1 3 6 9)))))))))))) : Formula 10)).close

def suffixSentence : Source.Sentence := ((((omega 0).imp ((sequence 1 2 0).imp ((Formula.mem 3 0).imp ((Formula.mem 4 0).imp ((sum 0 3 4 2).imp (existsCode 0 1 4 3)))))) : Formula 5)).close

def fullSuffixSentence : Source.Sentence := ((((omega 0).imp ((sequence 1 2 0).imp ((Formula.mem 2 0).imp ((empty 3).imp (existsCode 0 1 3 2))))) : Formula 4)).close

def graphRecoverySentence : Source.Sentence := ((((functionOn 1 2).imp ((reading 0 1 2 3).imp (graph 0 3 2 1))) : Formula 4)).close

def zeroFieldsSentence : Source.Sentence := ((((omega 0).imp ((sequence 1 2 0).imp ((Formula.mem 2 0).imp ((empty 3).imp ((aligned 0 1 3 2 4).imp (fields 0 4 2 1)))))) : Formula 5)).close

def existsSentence : Source.Sentence := ((((omega 0).imp ((sequence 1 2 0).imp ((Formula.mem 2 0).imp (existsEncoding 0 1 2)))) : Formula 3)).close

def validSentence : Source.Sentence := ((((encoding 0 1 2 3).imp (valid 0 3)) : Formula 4)).close

def readbackSentence : Source.Sentence := ((((omega 0).imp ((encoding 0 1 2 3).imp ((hasLength 0 3 4).imp ((fields 0 3 4 5).imp ((Formula.equal 4 2).conj (.equal 5 1)))))) : Formula 6)).close

theorem source_nilLength : Derives (Source.SetLanguage.ZF.at 0) nilLengthSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI

  let Δ : Context 3 := Context.add (empty 2) (Context.add (nilCode 0 1) (Context.add (omega 0) (Source.SetLanguage.ZF.at 3)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 3

  exact StructuralListLengthConstruct.nil_length hZ 0 1 2 (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem nilLength_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence nilLengthSentence) := TheoryTransport.sentence source_nilLength

theorem native_nilLength : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence nilLengthSentence) := ZFReplay.replay nilLength_kernel_certificate

theorem source_consLength : Derives (Source.SetLanguage.ZF.at 0) consLengthSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI

  let Δ : Context 6 := Context.add (successor 5 4) (Context.add (hasLength 0 2 4) (Context.add (consCode 0 1 2 3) (Context.add (Formula.mem 1 0) (Context.add (omega 0) (Source.SetLanguage.ZF.at 6)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 6

  exact StructuralListLengthConstruct.cons_length hZ 0 1 2 3 4 5 (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem consLength_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence consLengthSentence) := TheoryTransport.sentence source_consLength

theorem native_consLength : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence consLengthSentence) := ZFReplay.replay consLength_kernel_certificate

theorem source_emptyLength : Derives (Source.SetLanguage.ZF.at 0) emptyLengthSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI

  let Δ : Context 3 := Context.add (empty 2) (Context.add (hasLength 0 1 2) (Source.SetLanguage.ZF.at 3))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 3

  exact StructuralListLengthConstruct.nil_of_empty_length hZ 0 1 2 (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem emptyLength_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence emptyLengthSentence) := TheoryTransport.sentence source_emptyLength

theorem native_emptyLength : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence emptyLengthSentence) := ZFReplay.replay emptyLength_kernel_certificate

theorem source_offset : Derives (Source.SetLanguage.ZF.at 0) offsetSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI

  let Δ : Context 6 := Context.add (sum 0 1 4 5) (Context.add (successor 4 3) (Context.add (successor 2 1) (Context.add (Formula.mem 3 0) (Context.add (Formula.mem 1 0) (Context.add (omega 0) (Source.SetLanguage.ZF.at 6))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 6

  exact StructuralListSuffixArithmetic.offset_successor hZ 0 1 2 3 4 5 (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))) (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem offset_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence offsetSentence) := TheoryTransport.sentence source_offset

theorem native_offset : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence offsetSentence) := ZFReplay.replay offset_kernel_certificate

theorem source_suffixZero : Derives (Source.SetLanguage.ZF.at 0) suffixZeroSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI

  let Δ : Context 4 := Context.add (empty 3) (Context.add (omega 0) (Source.SetLanguage.ZF.at 4))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 4

  exact StructuralListSuffixBase.empty_code hZ 0 1 2 3 (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem suffixZero_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence suffixZeroSentence) := TheoryTransport.sentence source_suffixZero

theorem native_suffixZero : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence suffixZeroSentence) := ZFReplay.replay suffixZero_kernel_certificate

theorem source_suffixCons : Derives (Source.SetLanguage.ZF.at 0) suffixConsSentence := by
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
  apply Derives.impI

  let Δ : Context 10 := Context.add (aligned 0 1 4 5 8) (Context.add (edge 1 3 7) (Context.add (consCode 0 7 8 9) (Context.add (Formula.mem 8 0) (Context.add (Formula.mem 7 0) (Context.add (successor 4 3) (Context.add (successor 6 5) (Context.add (Formula.mem 3 0) (Context.add (Formula.mem 5 0) (Context.add (sequence 1 2 0) (Context.add (omega 0) (Source.SetLanguage.ZF.at 10)))))))))))
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
    apply ZFContext.add
    exact ZFContext.source_ZF 10

  exact StructuralListSuffixMatch.aligned_cons hZ 0 1 2 3 4 5 6 7 8 9 (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))) (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))) (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))) (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))) (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))) (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))) (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem suffixCons_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence suffixConsSentence) := TheoryTransport.sentence source_suffixCons

theorem native_suffixCons : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence suffixConsSentence) := ZFReplay.replay suffixCons_kernel_certificate

theorem source_suffix : Derives (Source.SetLanguage.ZF.at 0) suffixSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI

  let Δ : Context 5 := Context.add (sum 0 3 4 2) (Context.add (Formula.mem 4 0) (Context.add (Formula.mem 3 0) (Context.add (sequence 1 2 0) (Context.add (omega 0) (Source.SetLanguage.ZF.at 5)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 5

  exact StructuralListSuffixInduction.at_suffix hZ 0 1 2 3 4 (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem suffix_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence suffixSentence) := TheoryTransport.sentence source_suffix

theorem native_suffix : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence suffixSentence) := ZFReplay.replay suffix_kernel_certificate

theorem source_fullSuffix : Derives (Source.SetLanguage.ZF.at 0) fullSuffixSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI

  let Δ : Context 4 := Context.add (empty 3) (Context.add (Formula.mem 2 0) (Context.add (sequence 1 2 0) (Context.add (omega 0) (Source.SetLanguage.ZF.at 4))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 4

  exact StructuralListSuffixInduction.full_suffix hZ 0 1 2 3 (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem fullSuffix_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence fullSuffixSentence) := TheoryTransport.sentence source_fullSuffix

theorem native_fullSuffix : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence fullSuffixSentence) := ZFReplay.replay fullSuffix_kernel_certificate

theorem source_graphRecovery : Derives (Source.SetLanguage.ZF.at 0) graphRecoverySentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI

  let Δ : Context 4 := Context.add (reading 0 1 2 3) (Context.add (functionOn 1 2) (Source.SetLanguage.ZF.at 4))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 4

  exact StructuralListEncodeGraph.graph_from_reading hZ 0 1 2 3 (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem graphRecovery_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence graphRecoverySentence) := TheoryTransport.sentence source_graphRecovery

theorem native_graphRecovery : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence graphRecoverySentence) := ZFReplay.replay graphRecovery_kernel_certificate

theorem source_zeroFields : Derives (Source.SetLanguage.ZF.at 0) zeroFieldsSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI

  let Δ : Context 5 := Context.add (aligned 0 1 3 2 4) (Context.add (empty 3) (Context.add (Formula.mem 2 0) (Context.add (sequence 1 2 0) (Context.add (omega 0) (Source.SetLanguage.ZF.at 5)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 5

  exact StructuralListEncodeGraph.fields_from_zero hZ 0 1 2 3 4 (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem zeroFields_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence zeroFieldsSentence) := TheoryTransport.sentence source_zeroFields

theorem native_zeroFields : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence zeroFieldsSentence) := ZFReplay.replay zeroFields_kernel_certificate

theorem source_exists : Derives (Source.SetLanguage.ZF.at 0) existsSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI

  let Δ : Context 3 := Context.add (Formula.mem 2 0) (Context.add (sequence 1 2 0) (Context.add (omega 0) (Source.SetLanguage.ZF.at 3)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 3

  exact StructuralListEncodeExistence.exists_encoding hZ 0 1 2 (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem exists_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence existsSentence) := TheoryTransport.sentence source_exists

theorem native_exists : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence existsSentence) := ZFReplay.replay exists_kernel_certificate

theorem source_valid : Derives (Source.SetLanguage.ZF.at 0) validSentence := by
  apply close_derives
  apply Derives.impI

  exact StructuralListEncodeReadback.encoding_valid 0 1 2 3 (.hyp (Or.inl rfl))

theorem valid_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence validSentence) := TheoryTransport.sentence source_valid

theorem native_valid : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence validSentence) := ZFReplay.replay valid_kernel_certificate

theorem source_readback : Derives (Source.SetLanguage.ZF.at 0) readbackSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI

  let Δ : Context 6 := Context.add (fields 0 3 4 5) (Context.add (hasLength 0 3 4) (Context.add (encoding 0 1 2 3) (Context.add (omega 0) (Source.SetLanguage.ZF.at 6))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 6

  exact StructuralListEncodeReadback.decode_after_encode hZ 0 1 2 3 4 5 (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem readback_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence readbackSentence) := TheoryTransport.sentence source_readback

theorem native_readback : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence readbackSentence) := ZFReplay.replay readback_kernel_certificate

end PPAC.Migration.Internal.ObjectStructuralListEncode
