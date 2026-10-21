import PPAC.Migration.Internal.StructuralListRoundTrip

/-! 原列表编码单射、实际唯一编码纤维及双向往返的源ZF与原nativeZF完整闭句。 -/
namespace PPAC.Migration.Internal.ObjectStructuralListRoundTrip
open Source SourceAlgebra SourceLogic OmegaSyntax SequenceSyntax StructuralListSyntax StructuralListCodeSyntax StructuralListFieldGraphSyntax StructuralListEncodeSyntax
open StructuralListLengthSyntax (hasLength)
open StructuralListTraceSyntax (valid)

def predecessorSentence : Source.Sentence := ((((omega 0).imp ((Formula.mem 2 0).imp ((successor 1 2).imp ((successor 1 3).imp (Formula.equal 2 3))))) : Formula 4)).close

def consViewSentence : Source.Sentence := ((((omega 0).imp ((Formula.mem 2 0).imp ((successor 3 2).imp ((hasLength 0 1 3).imp (StructuralListCodeSyntax.consView 0 1 2))))) : Formula 4)).close

def headsSentence : Source.Sentence := ((((omega 0).imp ((Formula.mem 1 0).imp ((successor 2 1).imp ((Formula.mem 3 0).imp ((Formula.mem 4 0).imp ((Formula.mem 6 0).imp ((Formula.mem 7 0).imp ((consCode 0 3 4 5).imp ((consCode 0 6 7 8).imp ((agree 0 2 5 8).imp (Formula.equal 3 6))))))))))) : Formula 9)).close

def tailsSentence : Source.Sentence := ((((omega 0).imp ((Formula.mem 1 0).imp ((successor 2 1).imp ((Formula.mem 3 0).imp ((Formula.mem 4 0).imp ((Formula.mem 6 0).imp ((Formula.mem 7 0).imp ((consCode 0 3 4 5).imp ((consCode 0 6 7 8).imp ((agree 0 2 5 8).imp (agree 0 1 4 7))))))))))) : Formula 9)).close

def codeUniqueSentence : Source.Sentence := ((((omega 0).imp ((hasLength 0 2 1).imp ((hasLength 0 3 1).imp ((agree 0 1 2 3).imp (Formula.equal 2 3))))) : Formula 4)).close

def sameGraphSentence : Source.Sentence := ((((omega 0).imp ((hasLength 0 2 1).imp ((hasLength 0 3 1).imp ((fields 0 2 1 4).imp ((fields 0 3 1 4).imp (Formula.equal 2 3)))))) : Formula 5)).close

def encodedUniqueSentence : Source.Sentence := ((((omega 0).imp ((encoding 0 1 2 3).imp ((encoding 0 1 2 4).imp (Formula.equal 3 4)))) : Formula 5)).close

def encodingFiberSentence : Source.Sentence := ((((omega 0).imp ((sequence 1 2 0).imp ((Formula.mem 2 0).imp (StructuralListRoundTripSyntax.encodingFiber 0 1 2)))) : Formula 3)).close

def decodeThenEncodeSentence : Source.Sentence := ((((omega 0).imp ((hasLength 0 1 2).imp ((fields 0 1 2 3).imp ((encoding 0 3 2 4).imp (Formula.equal 4 1))))) : Formula 5)).close

def roundTripSentence : Source.Sentence := ((((omega 0).imp ((valid 0 1).imp (StructuralListRoundTripSyntax.roundTrip 0 1))) : Formula 2)).close

theorem source_predecessor : Derives (Source.SetLanguage.ZF.at 0) predecessorSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 4 := (Context.add (successor 1 3) (Context.add (successor 1 2) (Context.add (Formula.mem 2 0) (Context.add (omega 0) (Source.SetLanguage.ZF.at 4)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 4
  exact StructuralListCodeLength.predecessor_unique hZ 0 1 2 3 (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem predecessor_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence predecessorSentence) := TheoryTransport.sentence source_predecessor

theorem native_predecessor : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence predecessorSentence) := ZFReplay.replay predecessor_kernel_certificate

theorem source_consView : Derives (Source.SetLanguage.ZF.at 0) consViewSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 4 := (Context.add (hasLength 0 1 3) (Context.add (successor 3 2) (Context.add (Formula.mem 2 0) (Context.add (omega 0) (Source.SetLanguage.ZF.at 4)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 4
  exact StructuralListCodeLength.successor_view hZ 0 1 2 3 (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem consView_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence consViewSentence) := TheoryTransport.sentence source_consView

theorem native_consView : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence consViewSentence) := ZFReplay.replay consView_kernel_certificate

theorem source_heads : Derives (Source.SetLanguage.ZF.at 0) headsSentence := by
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
  let Δ : Context 9 := (Context.add (agree 0 2 5 8) (Context.add (consCode 0 6 7 8) (Context.add (consCode 0 3 4 5) (Context.add (Formula.mem 7 0) (Context.add (Formula.mem 6 0) (Context.add (Formula.mem 4 0) (Context.add (Formula.mem 3 0) (Context.add (successor 2 1) (Context.add (Formula.mem 1 0) (Context.add (omega 0) (Source.SetLanguage.ZF.at 9)))))))))))
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
    exact ZFContext.source_ZF 9
  exact StructuralListCodeFields.heads_equal hZ 0 1 2 3 4 5 6 7 8 (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))) (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))) (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))) (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))) (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))) (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem heads_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence headsSentence) := TheoryTransport.sentence source_heads

theorem native_heads : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence headsSentence) := ZFReplay.replay heads_kernel_certificate

theorem source_tails : Derives (Source.SetLanguage.ZF.at 0) tailsSentence := by
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
  let Δ : Context 9 := (Context.add (agree 0 2 5 8) (Context.add (consCode 0 6 7 8) (Context.add (consCode 0 3 4 5) (Context.add (Formula.mem 7 0) (Context.add (Formula.mem 6 0) (Context.add (Formula.mem 4 0) (Context.add (Formula.mem 3 0) (Context.add (successor 2 1) (Context.add (Formula.mem 1 0) (Context.add (omega 0) (Source.SetLanguage.ZF.at 9)))))))))))
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
    exact ZFContext.source_ZF 9
  exact StructuralListCodeFields.agree_tails hZ 0 1 2 3 4 5 6 7 8 (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))) (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))) (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))) (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))) (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))) (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem tails_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence tailsSentence) := TheoryTransport.sentence source_tails

theorem native_tails : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence tailsSentence) := ZFReplay.replay tails_kernel_certificate

theorem source_codeUnique : Derives (Source.SetLanguage.ZF.at 0) codeUniqueSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 4 := (Context.add (agree 0 1 2 3) (Context.add (hasLength 0 3 1) (Context.add (hasLength 0 2 1) (Context.add (omega 0) (Source.SetLanguage.ZF.at 4)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 4
  exact StructuralListCodeInduction.unique hZ 0 1 2 3 (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem codeUnique_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence codeUniqueSentence) := TheoryTransport.sentence source_codeUnique

theorem native_codeUnique : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence codeUniqueSentence) := ZFReplay.replay codeUnique_kernel_certificate

theorem source_sameGraph : Derives (Source.SetLanguage.ZF.at 0) sameGraphSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 5 := (Context.add (fields 0 3 1 4) (Context.add (fields 0 2 1 4) (Context.add (hasLength 0 3 1) (Context.add (hasLength 0 2 1) (Context.add (omega 0) (Source.SetLanguage.ZF.at 5))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 5
  exact StructuralListCodeGraph.same_fields_unique hZ 0 1 2 3 4 (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem sameGraph_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence sameGraphSentence) := TheoryTransport.sentence source_sameGraph

theorem native_sameGraph : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence sameGraphSentence) := ZFReplay.replay sameGraph_kernel_certificate

theorem source_encodedUnique : Derives (Source.SetLanguage.ZF.at 0) encodedUniqueSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 5 := (Context.add (encoding 0 1 2 4) (Context.add (encoding 0 1 2 3) (Context.add (omega 0) (Source.SetLanguage.ZF.at 5))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 5
  exact StructuralListCodeGraph.encoded_unique hZ 0 1 2 3 4 (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem encodedUnique_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence encodedUniqueSentence) := TheoryTransport.sentence source_encodedUnique

theorem native_encodedUnique : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence encodedUniqueSentence) := ZFReplay.replay encodedUnique_kernel_certificate

theorem source_encodingFiber : Derives (Source.SetLanguage.ZF.at 0) encodingFiberSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 3 := (Context.add (Formula.mem 2 0) (Context.add (sequence 1 2 0) (Context.add (omega 0) (Source.SetLanguage.ZF.at 3))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 3
  exact StructuralListRoundTrip.exists_unique_encoding hZ 0 1 2 (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem encodingFiber_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence encodingFiberSentence) := TheoryTransport.sentence source_encodingFiber

theorem native_encodingFiber : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence encodingFiberSentence) := ZFReplay.replay encodingFiber_kernel_certificate

theorem source_decodeThenEncode : Derives (Source.SetLanguage.ZF.at 0) decodeThenEncodeSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 5 := (Context.add (encoding 0 3 2 4) (Context.add (fields 0 1 2 3) (Context.add (hasLength 0 1 2) (Context.add (omega 0) (Source.SetLanguage.ZF.at 5)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 5
  exact StructuralListRoundTrip.decode_then_encode hZ 0 1 2 3 4 (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem decodeThenEncode_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence decodeThenEncodeSentence) := TheoryTransport.sentence source_decodeThenEncode

theorem native_decodeThenEncode : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence decodeThenEncodeSentence) := ZFReplay.replay decodeThenEncode_kernel_certificate

theorem source_roundTrip : Derives (Source.SetLanguage.ZF.at 0) roundTripSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 2 := (Context.add (valid 0 1) (Context.add (omega 0) (Source.SetLanguage.ZF.at 2)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 2
  exact StructuralListRoundTrip.reencode_exists hZ 0 1 (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem roundTrip_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence roundTripSentence) := TheoryTransport.sentence source_roundTrip

theorem native_roundTrip : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence roundTripSentence) := ZFReplay.replay roundTrip_kernel_certificate

end PPAC.Migration.Internal.ObjectStructuralListRoundTrip
