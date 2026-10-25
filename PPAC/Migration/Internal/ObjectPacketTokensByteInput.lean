import PPAC.Migration.Internal.PacketTokensBytesByteConsequences
import PPAC.Migration.Internal.PacketReaderInverseArithmetic

/-! Actual splice and independent token encodings preserve the original complete ByteList guard and every actual internal field bound. Bounded inverse, full reader bridge, Proof and Con remain unproved -/
namespace PPAC.Migration.Internal.ObjectPacketTokensByteInput
open Source SourceAlgebra SourceLogic OmegaSyntax

def tokensByteSpliceAllInternalPropertiesSentence {m} (w : Fin m) : Source.Sentence := ((omega w).imp ((StructuralListSpliceByteSyntax.allProperties w))).close

theorem source_tokensByteSpliceAllInternalProperties {m} (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (tokensByteSpliceAllInternalPropertiesSentence w) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact StructuralListSpliceByteInduction.all_properties hZ w h0

theorem tokensByteSpliceAllInternalProperties_kernel_certificate {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (tokensByteSpliceAllInternalPropertiesSentence w)) := TheoryTransport.sentence (source_tokensByteSpliceAllInternalProperties w)

theorem native_tokensByteSpliceAllInternalProperties {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (tokensByteSpliceAllInternalPropertiesSentence w)) := ZFReplay.replay (tokensByteSpliceAllInternalProperties_kernel_certificate w)

def tokensByteActualSplicePreservesFullByteGuardSentence {m} (w C T L : Fin m) : Source.Sentence := ((omega w).imp ((PacketByteInputSyntax.byteList w C).imp ((PacketByteInputSyntax.byteList w T).imp ((StructuralListSpliceSyntax.splice w C T L).imp ((PacketByteInputSyntax.byteList w L)))))).close

theorem source_tokensByteActualSplicePreservesFullByteGuard {m} (w C T L : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (tokensByteActualSplicePreservesFullByteGuardSentence w C T L) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralListSpliceSyntax.splice w C T L) (Context.add (PacketByteInputSyntax.byteList w T) (Context.add (PacketByteInputSyntax.byteList w C) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (PacketByteInputSyntax.byteList w C) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (PacketByteInputSyntax.byteList w T) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (StructuralListSpliceSyntax.splice w C T L) := .hyp (Or.inl rfl)
  exact StructuralListSpliceByte.byte_input hZ w C T L h0 h1 h2 h3

theorem tokensByteActualSplicePreservesFullByteGuard_kernel_certificate {m} (w C T L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (tokensByteActualSplicePreservesFullByteGuardSentence w C T L)) := TheoryTransport.sentence (source_tokensByteActualSplicePreservesFullByteGuard w C T L)

theorem native_tokensByteActualSplicePreservesFullByteGuard {m} (w C T L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (tokensByteActualSplicePreservesFullByteGuardSentence w C T L)) := ZFReplay.replay (tokensByteActualSplicePreservesFullByteGuard_kernel_certificate w C T L)

def tokensByteEncodingAllInternalPropertiesSentence {m} (w : Fin m) : Source.Sentence := ((omega w).imp ((Formula.all ((Formula.mem (Fin.last m) w.castSucc).imp (PacketTokensBytesByteSyntax.property w.castSucc (Fin.last m)))))).close

theorem source_tokensByteEncodingAllInternalProperties {m} (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (tokensByteEncodingAllInternalPropertiesSentence w) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact PacketTokensBytesByteInduction.all_properties hZ w h0

theorem tokensByteEncodingAllInternalProperties_kernel_certificate {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (tokensByteEncodingAllInternalPropertiesSentence w)) := TheoryTransport.sentence (source_tokensByteEncodingAllInternalProperties w)

theorem native_tokensByteEncodingAllInternalProperties {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (tokensByteEncodingAllInternalPropertiesSentence w)) := ZFReplay.replay (tokensByteEncodingAllInternalProperties_kernel_certificate w)

def tokensByteEveryEncodedInputHasFullByteGuardSentence {m} (w n bytes : Fin m) : Source.Sentence := ((omega w).imp ((PacketTokensBytes.encoded w n bytes).imp ((PacketByteInputSyntax.byteList w bytes)))).close

theorem source_tokensByteEveryEncodedInputHasFullByteGuard {m} (w n bytes : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (tokensByteEveryEncodedInputHasFullByteGuardSentence w n bytes) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketTokensBytes.encoded w n bytes) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PacketTokensBytes.encoded w n bytes) := .hyp (Or.inl rfl)
  exact PacketTokensBytesByte.byte_input hZ w n bytes h0 h1

theorem tokensByteEveryEncodedInputHasFullByteGuard_kernel_certificate {m} (w n bytes : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (tokensByteEveryEncodedInputHasFullByteGuardSentence w n bytes)) := TheoryTransport.sentence (source_tokensByteEveryEncodedInputHasFullByteGuard w n bytes)

theorem native_tokensByteEveryEncodedInputHasFullByteGuard {m} (w n bytes : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (tokensByteEveryEncodedInputHasFullByteGuardSentence w n bytes)) := ZFReplay.replay (tokensByteEveryEncodedInputHasFullByteGuard_kernel_certificate w n bytes)

def tokensByteGuardAllActualFieldsAtAnyLengthSentence {m} (w C n l : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 256 C).imp ((PacketByteInputSyntax.byteList w n).imp ((StructuralListLengthSyntax.hasLength w n l).imp ((PacketByteInputSyntax.bounds w C n l)))))).close

theorem source_tokensByteGuardAllActualFieldsAtAnyLength {m} (w C n l : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (tokensByteGuardAllActualFieldsAtAnyLengthSentence w C n l) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralListLengthSyntax.hasLength w n l) (Context.add (PacketByteInputSyntax.byteList w n) (Context.add (SyntaxNumeralSyntax.numeral 256 C) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 256 C) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (PacketByteInputSyntax.byteList w n) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (StructuralListLengthSyntax.hasLength w n l) := .hyp (Or.inl rfl)
  exact PacketByteInputFields.bounds_at_length hZ w C n l h0 h1 h2 h3

theorem tokensByteGuardAllActualFieldsAtAnyLength_kernel_certificate {m} (w C n l : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (tokensByteGuardAllActualFieldsAtAnyLengthSentence w C n l)) := TheoryTransport.sentence (source_tokensByteGuardAllActualFieldsAtAnyLength w C n l)

theorem native_tokensByteGuardAllActualFieldsAtAnyLength {m} (w C n l : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (tokensByteGuardAllActualFieldsAtAnyLengthSentence w C n l)) := ZFReplay.replay (tokensByteGuardAllActualFieldsAtAnyLength_kernel_certificate w C n l)

def tokensByteGuardAllActualFieldsBelowActual256Sentence {m} (w C n l i y : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 256 C).imp ((PacketByteInputSyntax.byteList w n).imp ((StructuralListLengthSyntax.hasLength w n l).imp ((Formula.mem i l).imp ((StructuralListFieldSyntax.field w n i y).imp ((Formula.mem y C)))))))).close

theorem source_tokensByteGuardAllActualFieldsBelowActual256 {m} (w C n l i y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (tokensByteGuardAllActualFieldsBelowActual256Sentence w C n l i y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralListFieldSyntax.field w n i y) (Context.add (Formula.mem i l) (Context.add (StructuralListLengthSyntax.hasLength w n l) (Context.add (PacketByteInputSyntax.byteList w n) (Context.add (SyntaxNumeralSyntax.numeral 256 C) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 256 C) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (PacketByteInputSyntax.byteList w n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (StructuralListLengthSyntax.hasLength w n l) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (Formula.mem i l) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (StructuralListFieldSyntax.field w n i y) := .hyp (Or.inl rfl)
  exact PacketByteInputFields.at_radix hZ w C n l i y h0 h1 h2 h3 h4 h5

theorem tokensByteGuardAllActualFieldsBelowActual256_kernel_certificate {m} (w C n l i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (tokensByteGuardAllActualFieldsBelowActual256Sentence w C n l i y)) := TheoryTransport.sentence (source_tokensByteGuardAllActualFieldsBelowActual256 w C n l i y)

theorem native_tokensByteGuardAllActualFieldsBelowActual256 {m} (w C n l i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (tokensByteGuardAllActualFieldsBelowActual256Sentence w C n l i y)) := ZFReplay.replay (tokensByteGuardAllActualFieldsBelowActual256_kernel_certificate w C n l i y)

def tokensByteGuardAllActualFieldValuesAreBytesSentence {m} (w n l i y : Fin m) : Source.Sentence := ((omega w).imp ((PacketByteInputSyntax.byteList w n).imp ((StructuralListLengthSyntax.hasLength w n l).imp ((Formula.mem i l).imp ((StructuralListFieldSyntax.field w n i y).imp ((PacketByteInputSyntax.byte y))))))).close

theorem source_tokensByteGuardAllActualFieldValuesAreBytes {m} (w n l i y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (tokensByteGuardAllActualFieldValuesAreBytesSentence w n l i y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralListFieldSyntax.field w n i y) (Context.add (Formula.mem i l) (Context.add (StructuralListLengthSyntax.hasLength w n l) (Context.add (PacketByteInputSyntax.byteList w n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (PacketByteInputSyntax.byteList w n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (StructuralListLengthSyntax.hasLength w n l) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (Formula.mem i l) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (StructuralListFieldSyntax.field w n i y) := .hyp (Or.inl rfl)
  exact PacketByteInputFields.byte_at_field hZ w n l i y h0 h1 h2 h3 h4

theorem tokensByteGuardAllActualFieldValuesAreBytes_kernel_certificate {m} (w n l i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (tokensByteGuardAllActualFieldValuesAreBytesSentence w n l i y)) := TheoryTransport.sentence (source_tokensByteGuardAllActualFieldValuesAreBytes w n l i y)

theorem native_tokensByteGuardAllActualFieldValuesAreBytes {m} (w n l i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (tokensByteGuardAllActualFieldValuesAreBytesSentence w n l i y)) := ZFReplay.replay (tokensByteGuardAllActualFieldValuesAreBytes_kernel_certificate w n l i y)

def tokensByteEncodedInputAllActualFieldsBoundedSentence {m} (w n bytes C l : Fin m) : Source.Sentence := ((omega w).imp ((PacketTokensBytes.encoded w n bytes).imp ((SyntaxNumeralSyntax.numeral 256 C).imp ((StructuralListLengthSyntax.hasLength w bytes l).imp ((PacketByteInputSyntax.bounds w C bytes l)))))).close

theorem source_tokensByteEncodedInputAllActualFieldsBounded {m} (w n bytes C l : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (tokensByteEncodedInputAllActualFieldsBoundedSentence w n bytes C l) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralListLengthSyntax.hasLength w bytes l) (Context.add (SyntaxNumeralSyntax.numeral 256 C) (Context.add (PacketTokensBytes.encoded w n bytes) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (PacketTokensBytes.encoded w n bytes) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral 256 C) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (StructuralListLengthSyntax.hasLength w bytes l) := .hyp (Or.inl rfl)
  exact PacketTokensBytesByteConsequences.bounds_at_length hZ w n bytes C l h0 h1 h2 h3

theorem tokensByteEncodedInputAllActualFieldsBounded_kernel_certificate {m} (w n bytes C l : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (tokensByteEncodedInputAllActualFieldsBoundedSentence w n bytes C l)) := TheoryTransport.sentence (source_tokensByteEncodedInputAllActualFieldsBounded w n bytes C l)

theorem native_tokensByteEncodedInputAllActualFieldsBounded {m} (w n bytes C l : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (tokensByteEncodedInputAllActualFieldsBoundedSentence w n bytes C l)) := ZFReplay.replay (tokensByteEncodedInputAllActualFieldsBounded_kernel_certificate w n bytes C l)

def tokensByteEncodedInputEveryFieldValueIsByteSentence {m} (w n bytes l i y : Fin m) : Source.Sentence := ((omega w).imp ((PacketTokensBytes.encoded w n bytes).imp ((StructuralListLengthSyntax.hasLength w bytes l).imp ((Formula.mem i l).imp ((StructuralListFieldSyntax.field w bytes i y).imp ((PacketByteInputSyntax.byte y))))))).close

theorem source_tokensByteEncodedInputEveryFieldValueIsByte {m} (w n bytes l i y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (tokensByteEncodedInputEveryFieldValueIsByteSentence w n bytes l i y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralListFieldSyntax.field w bytes i y) (Context.add (Formula.mem i l) (Context.add (StructuralListLengthSyntax.hasLength w bytes l) (Context.add (PacketTokensBytes.encoded w n bytes) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (PacketTokensBytes.encoded w n bytes) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (StructuralListLengthSyntax.hasLength w bytes l) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (Formula.mem i l) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (StructuralListFieldSyntax.field w bytes i y) := .hyp (Or.inl rfl)
  exact PacketTokensBytesByteConsequences.byte_at_field hZ w n bytes l i y h0 h1 h2 h3 h4

theorem tokensByteEncodedInputEveryFieldValueIsByte_kernel_certificate {m} (w n bytes l i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (tokensByteEncodedInputEveryFieldValueIsByteSentence w n bytes l i y)) := TheoryTransport.sentence (source_tokensByteEncodedInputEveryFieldValueIsByte w n bytes l i y)

theorem native_tokensByteEncodedInputEveryFieldValueIsByte {m} (w n bytes l i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (tokensByteEncodedInputEveryFieldValueIsByteSentence w n bytes l i y)) := ZFReplay.replay (tokensByteEncodedInputEveryFieldValueIsByte_kernel_certificate w n bytes l i y)

def tokensByteEncodedInputAndAllInitializedReturnsSentence {m} (w n bytes : Fin m) : Source.Sentence := ((omega w).imp ((PacketTokensBytes.encoded w n bytes).imp (((PacketByteInputSyntax.byteList w bytes).conj (PacketReaderTokensRoundtrip.allReturns w n bytes))))).close

theorem source_tokensByteEncodedInputAndAllInitializedReturns {m} (w n bytes : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (tokensByteEncodedInputAndAllInitializedReturnsSentence w n bytes) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketTokensBytes.encoded w n bytes) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PacketTokensBytes.encoded w n bytes) := .hyp (Or.inl rfl)
  exact PacketTokensBytesByteConsequences.at_encoded hZ w n bytes h0 h1

theorem tokensByteEncodedInputAndAllInitializedReturns_kernel_certificate {m} (w n bytes : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (tokensByteEncodedInputAndAllInitializedReturnsSentence w n bytes)) := TheoryTransport.sentence (source_tokensByteEncodedInputAndAllInitializedReturns w n bytes)

theorem native_tokensByteEncodedInputAndAllInitializedReturns {m} (w n bytes : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (tokensByteEncodedInputAndAllInitializedReturnsSentence w n bytes)) := ZFReplay.replay (tokensByteEncodedInputAndAllInitializedReturns_kernel_certificate w n bytes)

def tokensByteUniqueActualBoundedInputAndAllInitializedReturnsSentence {m} (w n : Fin m) : Source.Sentence := ((omega w).imp ((StructuralListTraceSyntax.valid w n).imp ((PacketTokensBytesByteConsequences.boundedComplete w n)))).close

theorem source_tokensByteUniqueActualBoundedInputAndAllInitializedReturns {m} (w n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (tokensByteUniqueActualBoundedInputAndAllInitializedReturnsSentence w n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralListTraceSyntax.valid w n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (StructuralListTraceSyntax.valid w n) := .hyp (Or.inl rfl)
  exact PacketTokensBytesByteConsequences.exists_unique hZ w n h0 h1

theorem tokensByteUniqueActualBoundedInputAndAllInitializedReturns_kernel_certificate {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (tokensByteUniqueActualBoundedInputAndAllInitializedReturnsSentence w n)) := TheoryTransport.sentence (source_tokensByteUniqueActualBoundedInputAndAllInitializedReturns w n)

theorem native_tokensByteUniqueActualBoundedInputAndAllInitializedReturns {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (tokensByteUniqueActualBoundedInputAndAllInitializedReturnsSentence w n)) := ZFReplay.replay (tokensByteUniqueActualBoundedInputAndAllInitializedReturns_kernel_certificate w n)

def tokensByteContinuationDigitBoundSentence {m} (w B b d : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 128 B).imp ((PacketByteInputSyntax.byte b).imp ((Formula.mem d w).imp ((NaturalAdditionSyntax.sum w B d b).imp ((Formula.mem d B))))))).close

theorem source_tokensByteContinuationDigitBound {m} (w B b d : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (tokensByteContinuationDigitBoundSentence w B b d) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (NaturalAdditionSyntax.sum w B d b) (Context.add (Formula.mem d w) (Context.add (PacketByteInputSyntax.byte b) (Context.add (SyntaxNumeralSyntax.numeral 128 B) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 128 B) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (PacketByteInputSyntax.byte b) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (Formula.mem d w) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (NaturalAdditionSyntax.sum w B d b) := .hyp (Or.inl rfl)
  exact PacketReaderInverseArithmetic.continuation_digit_bound hZ w B b d h0 h1 h2 h3 h4

theorem tokensByteContinuationDigitBound_kernel_certificate {m} (w B b d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (tokensByteContinuationDigitBoundSentence w B b d)) := TheoryTransport.sentence (source_tokensByteContinuationDigitBound w B b d)

theorem native_tokensByteContinuationDigitBound {m} (w B b d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (tokensByteContinuationDigitBoundSentence w B b d)) := ZFReplay.replay (tokensByteContinuationDigitBound_kernel_certificate w B b d)

def tokensBytePositiveContinuationScaleGuardSentence {m} (w B z o s S : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 128 B).imp ((empty z).imp ((successor o z).imp ((Formula.mem s w).imp (((empty s).neg).imp ((NaturalMultiplicationSyntax.product w s B S).imp ((((empty S).neg).conj ((Formula.equal S o).neg)))))))))).close

theorem source_tokensBytePositiveContinuationScaleGuard {m} (w B z o s S : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (tokensBytePositiveContinuationScaleGuardSentence w B z o s S) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (NaturalMultiplicationSyntax.product w s B S) (Context.add ((empty s).neg) (Context.add (Formula.mem s w) (Context.add (successor o z) (Context.add (empty z) (Context.add (SyntaxNumeralSyntax.numeral 128 B) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))
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
  have h4 : Derives Δ (Formula.mem s w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h5 : Derives Δ ((empty s).neg) := .hyp (Or.inr (Or.inl rfl))
  have h6 : Derives Δ (NaturalMultiplicationSyntax.product w s B S) := .hyp (Or.inl rfl)
  exact PacketReaderInverseArithmetic.continuation_scale_growth hZ w B z o s S h0 h1 h2 h3 h4 h5 h6

theorem tokensBytePositiveContinuationScaleGuard_kernel_certificate {m} (w B z o s S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (tokensBytePositiveContinuationScaleGuardSentence w B z o s S)) := TheoryTransport.sentence (source_tokensBytePositiveContinuationScaleGuard w B z o s S)

theorem native_tokensBytePositiveContinuationScaleGuard {m} (w B z o s S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (tokensBytePositiveContinuationScaleGuardSentence w B z o s S)) := ZFReplay.replay (tokensBytePositiveContinuationScaleGuard_kernel_certificate w B z o s S)

end PPAC.Migration.Internal.ObjectPacketTokensByteInput
