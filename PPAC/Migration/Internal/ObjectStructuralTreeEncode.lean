import PPAC.Migration.Internal.StructuralTreeEncodeReadback

/-! 任意内部有限字段序列的唯一原树构造及编解码恢复的原核完整闭句。 -/
namespace PPAC.Migration.Internal.ObjectStructuralTreeEncode
open Source SourceAlgebra SourceLogic OmegaSyntax StructuralTreeOperatorSyntax StructuralTreeEncodeSyntax StructuralTreeValiditySyntax

def existsSentence : Source.Sentence := (((omega 0).imp ((Formula.mem 1 0).imp ((Formula.mem 2 0).imp ((SequenceSyntax.sequence 3 2 0).imp (existsEncoding 0 1 2 3))))) : Formula 4).close

def fiberSentence : Source.Sentence := (((omega 0).imp ((Formula.mem 1 0).imp ((Formula.mem 2 0).imp ((SequenceSyntax.sequence 3 2 0).imp (encodingFiber 0 1 2 3))))) : Formula 4).close

def rangeSentence : Source.Sentence := (((omega 0).imp ((encoding 0 1 2 3 4).imp (Formula.mem 4 0))) : Formula 5).close

def uniqueSentence : Source.Sentence := (((omega 0).imp ((encoding 0 1 2 3 4).imp ((encoding 0 1 2 3 5).imp (Formula.equal 4 5)))) : Formula 6).close

def shapeUniqueSentence : Source.Sentence := (((omega 0).imp ((shape 0 1 2 3 4 5).imp ((shape 0 1 6 7 8 9).imp (((Formula.equal 2 6).conj (.equal 3 7)).conj ((Formula.equal 4 8).conj (.equal 5 9)))))) : Formula 10).close

def validitySentence : Source.Sentence := (((omega 0).imp ((encoding 0 1 2 3 4).imp ((valid 0 4).iff (validChildren 0 3)))) : Formula 5).close

def readbackSentence : Source.Sentence := (((omega 0).imp ((encoding 0 1 2 3 4).imp ((shape 0 4 5 6 7 8).imp (((Formula.equal 5 1).conj (.equal 7 2)).conj (.equal 8 3))))) : Formula 9).close

def codeRecoverySentence : Source.Sentence := (((omega 0).imp ((shape 0 1 2 3 4 5).imp ((encoding 0 2 4 5 6).imp (Formula.equal 6 1)))) : Formula 7).close

theorem source_exists : Derives (Source.SetLanguage.ZF.at 0) existsSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 4 := Context.add (SequenceSyntax.sequence 3 2 0) (Context.add (Formula.mem 2 0) (Context.add (Formula.mem 1 0) (Context.add (omega 0) (Source.SetLanguage.ZF.at 4))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 4
  exact StructuralTreeEncode.exists_encoding hZ 0 1 2 3 (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem exists_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence existsSentence) := TheoryTransport.sentence source_exists

theorem native_exists : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence existsSentence) := ZFReplay.replay exists_kernel_certificate

theorem source_fiber : Derives (Source.SetLanguage.ZF.at 0) fiberSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 4 := Context.add (SequenceSyntax.sequence 3 2 0) (Context.add (Formula.mem 2 0) (Context.add (Formula.mem 1 0) (Context.add (omega 0) (Source.SetLanguage.ZF.at 4))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 4
  exact StructuralTreeEncode.exists_unique hZ 0 1 2 3 (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem fiber_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence fiberSentence) := TheoryTransport.sentence source_fiber

theorem native_fiber : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence fiberSentence) := ZFReplay.replay fiber_kernel_certificate

theorem source_range : Derives (Source.SetLanguage.ZF.at 0) rangeSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 5 := Context.add (encoding 0 1 2 3 4) (Context.add (omega 0) (Source.SetLanguage.ZF.at 5))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 5
  exact StructuralTreeEncode.range hZ 0 1 2 3 4 (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem range_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence rangeSentence) := TheoryTransport.sentence source_range

theorem native_range : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence rangeSentence) := ZFReplay.replay range_kernel_certificate

theorem source_unique : Derives (Source.SetLanguage.ZF.at 0) uniqueSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 6 := Context.add (encoding 0 1 2 3 5) (Context.add (encoding 0 1 2 3 4) (Context.add (omega 0) (Source.SetLanguage.ZF.at 6)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 6
  exact StructuralTreeEncode.unique hZ 0 1 2 3 4 5 (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem unique_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence uniqueSentence) := TheoryTransport.sentence source_unique

theorem native_unique : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence uniqueSentence) := ZFReplay.replay unique_kernel_certificate

theorem source_shapeUnique : Derives (Source.SetLanguage.ZF.at 0) shapeUniqueSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 10 := Context.add (shape 0 1 6 7 8 9) (Context.add (shape 0 1 2 3 4 5) (Context.add (omega 0) (Source.SetLanguage.ZF.at 10)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 10
  exact StructuralTreeShapeUnique.unique hZ 0 1 2 3 4 5 6 7 8 9 (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem shapeUnique_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence shapeUniqueSentence) := TheoryTransport.sentence source_shapeUnique

theorem native_shapeUnique : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence shapeUniqueSentence) := ZFReplay.replay shapeUnique_kernel_certificate

theorem source_validity : Derives (Source.SetLanguage.ZF.at 0) validitySentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 5 := Context.add (encoding 0 1 2 3 4) (Context.add (omega 0) (Source.SetLanguage.ZF.at 5))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 5
  exact StructuralTreeEncodeReadback.valid_iff_children hZ 0 1 2 3 4 (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem validity_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence validitySentence) := TheoryTransport.sentence source_validity

theorem native_validity : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence validitySentence) := ZFReplay.replay validity_kernel_certificate

theorem source_readback : Derives (Source.SetLanguage.ZF.at 0) readbackSentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 9 := Context.add (shape 0 4 5 6 7 8) (Context.add (encoding 0 1 2 3 4) (Context.add (omega 0) (Source.SetLanguage.ZF.at 9)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 9
  exact StructuralTreeEncodeReadback.decode_after_encode hZ 0 1 2 3 4 5 6 7 8 (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem readback_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence readbackSentence) := TheoryTransport.sentence source_readback

theorem native_readback : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence readbackSentence) := ZFReplay.replay readback_kernel_certificate

theorem source_codeRecovery : Derives (Source.SetLanguage.ZF.at 0) codeRecoverySentence := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context 7 := Context.add (encoding 0 2 4 5 6) (Context.add (shape 0 1 2 3 4 5) (Context.add (omega 0) (Source.SetLanguage.ZF.at 7)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF 7
  exact StructuralTreeEncodeReadback.decode_then_encode hZ 0 1 2 3 4 5 6 (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem codeRecovery_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence codeRecoverySentence) := TheoryTransport.sentence source_codeRecovery

theorem native_codeRecovery : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence codeRecoverySentence) := ZFReplay.replay codeRecovery_kernel_certificate

end PPAC.Migration.Internal.ObjectStructuralTreeEncode
