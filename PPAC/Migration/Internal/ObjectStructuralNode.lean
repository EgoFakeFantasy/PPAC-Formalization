import PPAC.Migration.Internal.StructuralNodeDecodeUnique

/-! 原始节点编码与全部正内部自然码解码的完整原核闭句。 -/
namespace PPAC.Migration.Internal.ObjectStructuralNode
open Source SourceAlgebra SourceLogic OmegaSyntax StructuralNodeSyntax

def encodeFiberSentence : Source.Sentence := ((omega (0 : Fin 3)).imp ((Formula.mem 1 0).imp ((Formula.mem 2 0).imp (encodeFiber 0 1 2)))).close

def closureSentence : Source.Sentence := ((omega (0 : Fin 4)).imp ((raw 0 1 2 3).imp (Formula.mem 3 0))).close

def positiveSentence : Source.Sentence := ((raw (0 : Fin 4) 1 2 3).imp ((empty 3).neg)).close

def componentsSentence : Source.Sentence := ((omega (0 : Fin 4)).imp ((Formula.mem 1 0).imp ((Formula.mem 2 0).imp ((raw 0 1 2 3).imp ((Formula.mem 1 3).conj (.mem 2 3)))))).close

def injectiveSentence : Source.Sentence := ((omega (0 : Fin 6)).imp ((Formula.mem 1 0).imp ((Formula.mem 2 0).imp ((Formula.mem 3 0).imp ((Formula.mem 4 0).imp ((raw 0 1 2 5).imp ((raw 0 3 4 5).imp ((Formula.equal 1 3).conj (.equal 2 4))))))))).close

def positiveIffSentence : Source.Sentence := ((omega (0 : Fin 2)).imp ((Formula.mem 1 0).imp ((empty 1).neg.iff (StructuralNodeDecodeSyntax.preimage 0 1)))).close

def decodeTotalSentence : Source.Sentence := ((omega (0 : Fin 2)).imp ((Formula.mem 1 0).imp (((empty 1).neg).imp (StructuralNodeDecodeSyntax.preimage 0 1)))).close

def decodeFiberSentence : Source.Sentence := ((omega (0 : Fin 2)).imp ((Formula.mem 1 0).imp (((empty 1).neg).imp (StructuralNodeDecodeSyntax.fiber 0 1)))).close

def decodeBoundsSentence : Source.Sentence := ((omega (0 : Fin 2)).imp ((Formula.mem 1 0).imp (((empty 1).neg).imp (StructuralNodeDecodeSyntax.boundedFiber 0 1)))).close

theorem source_encodeFiber : Derives (Source.SetLanguage.ZF.at 0) encodeFiberSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 3 := (Context.add (Formula.mem 2 0) (Context.add (Formula.mem 1 0) (Context.add (omega 0) (Source.SetLanguage.ZF.at 3))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 3
  exact StructuralNodeCore.unique_fiber hZ 0 1 2
    (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inr (Or.inl rfl)))
    (.hyp (Or.inl rfl))

theorem encodeFiber_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence encodeFiberSentence) := TheoryTransport.sentence source_encodeFiber

theorem native_encodeFiber : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence encodeFiberSentence) :=
  ZFReplay.replay encodeFiber_kernel_certificate

theorem source_closure : Derives (Source.SetLanguage.ZF.at 0) closureSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 4 := (Context.add (raw 0 1 2 3) (Context.add (omega 0) (Source.SetLanguage.ZF.at 4)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 4
  exact StructuralNodeProperties.range hZ 0 1 2 3
    (.hyp (Or.inr (Or.inl rfl)))
    (.hyp (Or.inl rfl))

theorem closure_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence closureSentence) := TheoryTransport.sentence source_closure

theorem native_closure : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence closureSentence) :=
  ZFReplay.replay closure_kernel_certificate

theorem source_positive : Derives (Source.SetLanguage.ZF.at 0) positiveSentence := by
  apply close_derives
  apply Derives.impI
  exact StructuralNodeProperties.positive 0 1 2 3
    (.hyp (Or.inl rfl))

theorem positive_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence positiveSentence) := TheoryTransport.sentence source_positive

theorem native_positive : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence positiveSentence) :=
  ZFReplay.replay positive_kernel_certificate

theorem source_components : Derives (Source.SetLanguage.ZF.at 0) componentsSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 4 := (Context.add (raw 0 1 2 3) (Context.add (Formula.mem 2 0) (Context.add (Formula.mem 1 0) (Context.add (omega 0) (Source.SetLanguage.ZF.at 4)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 4
  exact StructuralNodeProperties.components hZ 0 1 2 3
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inr (Or.inl rfl)))
    (.hyp (Or.inl rfl))

theorem components_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence componentsSentence) := TheoryTransport.sentence source_components

theorem native_components : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence componentsSentence) :=
  ZFReplay.replay components_kernel_certificate

theorem source_injective : Derives (Source.SetLanguage.ZF.at 0) injectiveSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 6 := (Context.add (raw 0 3 4 5) (Context.add (raw 0 1 2 5) (Context.add (Formula.mem 4 0) (Context.add (Formula.mem 3 0) (Context.add (Formula.mem 2 0) (Context.add (Formula.mem 1 0) (Context.add (omega 0) (Source.SetLanguage.ZF.at 6))))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 6
  exact StructuralNodeCore.injective hZ 0 1 2 3 4 5
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inr (Or.inl rfl)))
    (.hyp (Or.inl rfl))

theorem injective_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence injectiveSentence) := TheoryTransport.sentence source_injective

theorem native_injective : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence injectiveSentence) :=
  ZFReplay.replay injective_kernel_certificate

theorem source_positiveIff : Derives (Source.SetLanguage.ZF.at 0) positiveIffSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 2 := (Context.add (Formula.mem 1 0) (Context.add (omega 0) (Source.SetLanguage.ZF.at 2)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 2
  exact StructuralNodeDecodeExistence.positive_iff hZ 0 1
    (.hyp (Or.inr (Or.inl rfl)))
    (.hyp (Or.inl rfl))

theorem positiveIff_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence positiveIffSentence) := TheoryTransport.sentence source_positiveIff

theorem native_positiveIff : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence positiveIffSentence) :=
  ZFReplay.replay positiveIff_kernel_certificate

theorem source_decodeTotal : Derives (Source.SetLanguage.ZF.at 0) decodeTotalSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 2 := (Context.add ((empty 1).neg) (Context.add (Formula.mem 1 0) (Context.add (omega 0) (Source.SetLanguage.ZF.at 2))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 2
  exact StructuralNodeDecodeExistence.preimage_exists hZ 0 1
    (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inr (Or.inl rfl)))
    (.hyp (Or.inl rfl))

theorem decodeTotal_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence decodeTotalSentence) := TheoryTransport.sentence source_decodeTotal

theorem native_decodeTotal : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence decodeTotalSentence) :=
  ZFReplay.replay decodeTotal_kernel_certificate

theorem source_decodeFiber : Derives (Source.SetLanguage.ZF.at 0) decodeFiberSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 2 := (Context.add ((empty 1).neg) (Context.add (Formula.mem 1 0) (Context.add (omega 0) (Source.SetLanguage.ZF.at 2))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 2
  exact StructuralNodeDecodeUnique.unique_fiber hZ 0 1
    (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inr (Or.inl rfl)))
    (.hyp (Or.inl rfl))

theorem decodeFiber_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence decodeFiberSentence) := TheoryTransport.sentence source_decodeFiber

theorem native_decodeFiber : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence decodeFiberSentence) :=
  ZFReplay.replay decodeFiber_kernel_certificate

theorem source_decodeBounds : Derives (Source.SetLanguage.ZF.at 0) decodeBoundsSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 2 := (Context.add ((empty 1).neg) (Context.add (Formula.mem 1 0) (Context.add (omega 0) (Source.SetLanguage.ZF.at 2))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 2
  exact StructuralNodeDecodeUnique.bounded_fiber hZ 0 1
    (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inr (Or.inl rfl)))
    (.hyp (Or.inl rfl))

theorem decodeBounds_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence decodeBoundsSentence) := TheoryTransport.sentence source_decodeBounds

theorem native_decodeBounds : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence decodeBoundsSentence) :=
  ZFReplay.replay decodeBounds_kernel_certificate

end PPAC.Migration.Internal.ObjectStructuralNode
