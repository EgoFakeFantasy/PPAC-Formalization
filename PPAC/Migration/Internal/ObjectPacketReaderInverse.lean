import PPAC.Migration.Internal.PacketReaderInverseAccepted

/-! Whole successful bounded reader runs reconstruct an independent token encoding and exact output order. Original initialization witnesses are eliminated and bounded acceptance is exactly independent encoding. Complete packet grammar, Proof and Con remain unproved -/
namespace PPAC.Migration.Internal.ObjectPacketReaderInverse
open Source SourceAlgebra SourceLogic OmegaSyntax

def readerInverseActualNilSuccessHasIndependentTokenEncodingSentence {m} (w B z o L A O p : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 128 B).imp ((empty z).imp ((successor o z).imp ((StructuralListSyntax.nilCode w L).imp ((PacketReaderEvalSyntax.eval w B z o L z o A p).imp ((PacketReaderReturnSyntax.some w O p).imp ((PacketReaderInverseSyntax.result w L A O))))))))).close

theorem source_readerInverseActualNilSuccessHasIndependentTokenEncoding {m} (w B z o L A O p : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (readerInverseActualNilSuccessHasIndependentTokenEncodingSentence w B z o L A O p) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderReturnSyntax.some w O p) (Context.add (PacketReaderEvalSyntax.eval w B z o L z o A p) (Context.add (StructuralListSyntax.nilCode w L) (Context.add (successor o z) (Context.add (empty z) (Context.add (SyntaxNumeralSyntax.numeral 128 B) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 128 B) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h2 : Derives Δ (empty z) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h3 : Derives Δ (successor o z) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : Derives Δ (StructuralListSyntax.nilCode w L) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h5 : Derives Δ (PacketReaderEvalSyntax.eval w B z o L z o A p) := .hyp (Or.inr (Or.inl rfl))
  have h6 : Derives Δ (PacketReaderReturnSyntax.some w O p) := .hyp (Or.inl rfl)
  exact PacketReaderInverseNil.nil_case hZ w B z o L A O p h0 h1 h2 h3 h4 h5 h6

theorem readerInverseActualNilSuccessHasIndependentTokenEncoding_kernel_certificate {m} (w B z o L A O p : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (readerInverseActualNilSuccessHasIndependentTokenEncodingSentence w B z o L A O p)) := TheoryTransport.sentence (source_readerInverseActualNilSuccessHasIndependentTokenEncoding w B z o L A O p)

theorem native_readerInverseActualNilSuccessHasIndependentTokenEncoding {m} (w B z o L A O p : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (readerInverseActualNilSuccessHasIndependentTokenEncodingSentence w B z o L A O p)) := ZFReplay.replay (readerInverseActualNilSuccessHasIndependentTokenEncoding_kernel_certificate w B z o L A O p)

def readerInverseAllInternalBoundedInputPropertiesSentence {m} (w B z o : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 128 B).imp ((empty z).imp ((successor o z).imp ((PacketReaderInverseSyntax.allProperties w B z o)))))).close

theorem source_readerInverseAllInternalBoundedInputProperties {m} (w B z o : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (readerInverseAllInternalBoundedInputPropertiesSentence w B z o) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor o z) (Context.add (empty z) (Context.add (SyntaxNumeralSyntax.numeral 128 B) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 128 B) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (empty z) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (successor o z) := .hyp (Or.inl rfl)
  exact PacketReaderInverseInduction.all_properties hZ w B z o h0 h1 h2 h3

theorem readerInverseAllInternalBoundedInputProperties_kernel_certificate {m} (w B z o : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (readerInverseAllInternalBoundedInputPropertiesSentence w B z o)) := TheoryTransport.sentence (source_readerInverseAllInternalBoundedInputProperties w B z o)

theorem native_readerInverseAllInternalBoundedInputProperties {m} (w B z o : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (readerInverseAllInternalBoundedInputPropertiesSentence w B z o)) := ZFReplay.replay (readerInverseAllInternalBoundedInputProperties_kernel_certificate w B z o)

def readerInverseEverySuccessfulBoundedInputReconstructsActualTokensSentence {m} (w B z o L A O p : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 128 B).imp ((empty z).imp ((successor o z).imp ((PacketByteInputSyntax.byteList w L).imp ((PacketReaderEvalSyntax.eval w B z o L z o A p).imp ((PacketReaderReturnSyntax.some w O p).imp ((PacketReaderInverseSyntax.result w L A O))))))))).close

theorem source_readerInverseEverySuccessfulBoundedInputReconstructsActualTokens {m} (w B z o L A O p : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (readerInverseEverySuccessfulBoundedInputReconstructsActualTokensSentence w B z o L A O p) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderReturnSyntax.some w O p) (Context.add (PacketReaderEvalSyntax.eval w B z o L z o A p) (Context.add (PacketByteInputSyntax.byteList w L) (Context.add (successor o z) (Context.add (empty z) (Context.add (SyntaxNumeralSyntax.numeral 128 B) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 128 B) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h2 : Derives Δ (empty z) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h3 : Derives Δ (successor o z) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : Derives Δ (PacketByteInputSyntax.byteList w L) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h5 : Derives Δ (PacketReaderEvalSyntax.eval w B z o L z o A p) := .hyp (Or.inr (Or.inl rfl))
  have h6 : Derives Δ (PacketReaderReturnSyntax.some w O p) := .hyp (Or.inl rfl)
  exact PacketReaderInverseInduction.inverse hZ w B z o L A O p h0 h1 h2 h3 h4 h5 h6

theorem readerInverseEverySuccessfulBoundedInputReconstructsActualTokens_kernel_certificate {m} (w B z o L A O p : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (readerInverseEverySuccessfulBoundedInputReconstructsActualTokensSentence w B z o L A O p)) := TheoryTransport.sentence (source_readerInverseEverySuccessfulBoundedInputReconstructsActualTokens w B z o L A O p)

theorem native_readerInverseEverySuccessfulBoundedInputReconstructsActualTokens {m} (w B z o L A O p : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (readerInverseEverySuccessfulBoundedInputReconstructsActualTokensSentence w B z o L A O p)) := ZFReplay.replay (readerInverseEverySuccessfulBoundedInputReconstructsActualTokens_kernel_certificate w B z o L A O p)

def readerInverseInitializedSuccessExactAtActualLiteralsSentence {m} (w B z o tokens bytes p : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 128 B).imp ((empty z).imp ((successor o z).imp ((PacketByteInputSyntax.byteList w bytes).imp ((PacketReaderReturnSyntax.some w tokens p).imp (((PacketReaderInitSyntax.parse w bytes p).iff (PacketTokensBytes.encoded w tokens bytes))))))))).close

theorem source_readerInverseInitializedSuccessExactAtActualLiterals {m} (w B z o tokens bytes p : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (readerInverseInitializedSuccessExactAtActualLiteralsSentence w B z o tokens bytes p) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderReturnSyntax.some w tokens p) (Context.add (PacketByteInputSyntax.byteList w bytes) (Context.add (successor o z) (Context.add (empty z) (Context.add (SyntaxNumeralSyntax.numeral 128 B) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 128 B) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (empty z) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (successor o z) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (PacketByteInputSyntax.byteList w bytes) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (PacketReaderReturnSyntax.some w tokens p) := .hyp (Or.inl rfl)
  exact PacketReaderInverseInitialized.at_literals hZ w B z o tokens bytes p h0 h1 h2 h3 h4 h5

theorem readerInverseInitializedSuccessExactAtActualLiterals_kernel_certificate {m} (w B z o tokens bytes p : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (readerInverseInitializedSuccessExactAtActualLiteralsSentence w B z o tokens bytes p)) := TheoryTransport.sentence (source_readerInverseInitializedSuccessExactAtActualLiterals w B z o tokens bytes p)

theorem native_readerInverseInitializedSuccessExactAtActualLiterals {m} (w B z o tokens bytes p : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (readerInverseInitializedSuccessExactAtActualLiteralsSentence w B z o tokens bytes p)) := ZFReplay.replay (readerInverseInitializedSuccessExactAtActualLiterals_kernel_certificate w B z o tokens bytes p)

def readerInverseInitializedSuccessExactWithoutLiteralParametersSentence {m} (w tokens bytes p : Fin m) : Source.Sentence := ((omega w).imp ((PacketByteInputSyntax.byteList w bytes).imp ((PacketReaderReturnSyntax.some w tokens p).imp (((PacketReaderInitSyntax.parse w bytes p).iff (PacketTokensBytes.encoded w tokens bytes)))))).close

theorem source_readerInverseInitializedSuccessExactWithoutLiteralParameters {m} (w tokens bytes p : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (readerInverseInitializedSuccessExactWithoutLiteralParametersSentence w tokens bytes p) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderReturnSyntax.some w tokens p) (Context.add (PacketByteInputSyntax.byteList w bytes) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (PacketByteInputSyntax.byteList w bytes) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (PacketReaderReturnSyntax.some w tokens p) := .hyp (Or.inl rfl)
  exact PacketReaderInverseInitialized.at_success hZ w tokens bytes p h0 h1 h2

theorem readerInverseInitializedSuccessExactWithoutLiteralParameters_kernel_certificate {m} (w tokens bytes p : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (readerInverseInitializedSuccessExactWithoutLiteralParametersSentence w tokens bytes p)) := TheoryTransport.sentence (source_readerInverseInitializedSuccessExactWithoutLiteralParameters w tokens bytes p)

theorem native_readerInverseInitializedSuccessExactWithoutLiteralParameters {m} (w tokens bytes p : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (readerInverseInitializedSuccessExactWithoutLiteralParametersSentence w tokens bytes p)) := ZFReplay.replay (readerInverseInitializedSuccessExactWithoutLiteralParameters_kernel_certificate w tokens bytes p)

def readerInverseBoundedActualAcceptanceImpliesIndependentEncodingSentence {m} (w tokens bytes : Fin m) : Source.Sentence := ((omega w).imp ((PacketByteInputSyntax.byteList w bytes).imp ((PacketReaderInverseAccepted.accepted w tokens bytes).imp ((PacketTokensBytes.encoded w tokens bytes))))).close

theorem source_readerInverseBoundedActualAcceptanceImpliesIndependentEncoding {m} (w tokens bytes : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (readerInverseBoundedActualAcceptanceImpliesIndependentEncodingSentence w tokens bytes) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderInverseAccepted.accepted w tokens bytes) (Context.add (PacketByteInputSyntax.byteList w bytes) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (PacketByteInputSyntax.byteList w bytes) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (PacketReaderInverseAccepted.accepted w tokens bytes) := .hyp (Or.inl rfl)
  exact PacketReaderInverseAccepted.from_accepted hZ w tokens bytes h0 h1 h2

theorem readerInverseBoundedActualAcceptanceImpliesIndependentEncoding_kernel_certificate {m} (w tokens bytes : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (readerInverseBoundedActualAcceptanceImpliesIndependentEncodingSentence w tokens bytes)) := TheoryTransport.sentence (source_readerInverseBoundedActualAcceptanceImpliesIndependentEncoding w tokens bytes)

theorem native_readerInverseBoundedActualAcceptanceImpliesIndependentEncoding {m} (w tokens bytes : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (readerInverseBoundedActualAcceptanceImpliesIndependentEncodingSentence w tokens bytes)) := ZFReplay.replay (readerInverseBoundedActualAcceptanceImpliesIndependentEncoding_kernel_certificate w tokens bytes)

def readerInverseIndependentEncodingConstructsActualAcceptanceSentence {m} (w tokens bytes : Fin m) : Source.Sentence := ((omega w).imp ((PacketTokensBytes.encoded w tokens bytes).imp ((PacketReaderInverseAccepted.accepted w tokens bytes)))).close

theorem source_readerInverseIndependentEncodingConstructsActualAcceptance {m} (w tokens bytes : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (readerInverseIndependentEncodingConstructsActualAcceptanceSentence w tokens bytes) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketTokensBytes.encoded w tokens bytes) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PacketTokensBytes.encoded w tokens bytes) := .hyp (Or.inl rfl)
  exact PacketReaderInverseAccepted.to_accepted hZ w tokens bytes h0 h1

theorem readerInverseIndependentEncodingConstructsActualAcceptance_kernel_certificate {m} (w tokens bytes : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (readerInverseIndependentEncodingConstructsActualAcceptanceSentence w tokens bytes)) := TheoryTransport.sentence (source_readerInverseIndependentEncodingConstructsActualAcceptance w tokens bytes)

theorem native_readerInverseIndependentEncodingConstructsActualAcceptance {m} (w tokens bytes : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (readerInverseIndependentEncodingConstructsActualAcceptanceSentence w tokens bytes)) := ZFReplay.replay (readerInverseIndependentEncodingConstructsActualAcceptance_kernel_certificate w tokens bytes)

def readerInverseActualAcceptanceExactOnBoundedInputSentence {m} (w tokens bytes : Fin m) : Source.Sentence := ((omega w).imp ((PacketByteInputSyntax.byteList w bytes).imp (((PacketReaderInverseAccepted.accepted w tokens bytes).iff (PacketTokensBytes.encoded w tokens bytes))))).close

theorem source_readerInverseActualAcceptanceExactOnBoundedInput {m} (w tokens bytes : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (readerInverseActualAcceptanceExactOnBoundedInputSentence w tokens bytes) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketByteInputSyntax.byteList w bytes) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PacketByteInputSyntax.byteList w bytes) := .hyp (Or.inl rfl)
  exact PacketReaderInverseAccepted.accepted_iff hZ w tokens bytes h0 h1

theorem readerInverseActualAcceptanceExactOnBoundedInput_kernel_certificate {m} (w tokens bytes : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (readerInverseActualAcceptanceExactOnBoundedInputSentence w tokens bytes)) := TheoryTransport.sentence (source_readerInverseActualAcceptanceExactOnBoundedInput w tokens bytes)

theorem native_readerInverseActualAcceptanceExactOnBoundedInput {m} (w tokens bytes : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (readerInverseActualAcceptanceExactOnBoundedInputSentence w tokens bytes)) := ZFReplay.replay (readerInverseActualAcceptanceExactOnBoundedInput_kernel_certificate w tokens bytes)

def readerInverseBoundedActualAcceptanceExactlyIndependentEncodingSentence {m} (w tokens bytes : Fin m) : Source.Sentence := ((omega w).imp (((PacketReaderInverseAccepted.boundedAccepted w tokens bytes).iff (PacketTokensBytes.encoded w tokens bytes)))).close

theorem source_readerInverseBoundedActualAcceptanceExactlyIndependentEncoding {m} (w tokens bytes : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (readerInverseBoundedActualAcceptanceExactlyIndependentEncodingSentence w tokens bytes) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact PacketReaderInverseAccepted.bounded_iff hZ w tokens bytes h0

theorem readerInverseBoundedActualAcceptanceExactlyIndependentEncoding_kernel_certificate {m} (w tokens bytes : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (readerInverseBoundedActualAcceptanceExactlyIndependentEncodingSentence w tokens bytes)) := TheoryTransport.sentence (source_readerInverseBoundedActualAcceptanceExactlyIndependentEncoding w tokens bytes)

theorem native_readerInverseBoundedActualAcceptanceExactlyIndependentEncoding {m} (w tokens bytes : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (readerInverseBoundedActualAcceptanceExactlyIndependentEncodingSentence w tokens bytes)) := ZFReplay.replay (readerInverseBoundedActualAcceptanceExactlyIndependentEncoding_kernel_certificate w tokens bytes)

end PPAC.Migration.Internal.ObjectPacketReaderInverse
