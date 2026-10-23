import PPAC.Migration.Internal.TermQuotationLiftJoint

/-! 原coded binder与提升双表quotation的精确对应及实际联合纤维的原YesMetaZFC核证书。 -/
namespace PPAC.Migration.Internal.ObjectTermLiftQuotation
open Source SourceAlgebra SourceLogic OmegaSyntax

def readingsFromImagesSentence {m} {bound free : PureSyntaxQuotation.Ctx} (values : List (PureSyntaxQuotation.Tm bound free)) (w L : Fin m) : Source.Sentence := ((omega w).imp ((TermImageQuotationSyntax.images values w L).imp ((TermImageReadingSyntax.readings values w L)))).close

theorem source_readingsFromImages {m} {bound free : PureSyntaxQuotation.Ctx} (values : List (PureSyntaxQuotation.Tm bound free)) (w L : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (readingsFromImagesSentence values w L) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (TermImageQuotationSyntax.images values w L) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (TermImageQuotationSyntax.images values w L) := .hyp (Or.inl rfl)
  exact TermImageReading.from_images hZ values w L h0 h1

theorem readingsFromImages_kernel_certificate {m} {bound free : PureSyntaxQuotation.Ctx} (values : List (PureSyntaxQuotation.Tm bound free)) (w L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (readingsFromImagesSentence values w L)) := TheoryTransport.sentence (source_readingsFromImages values w L)

theorem native_readingsFromImages {m} {bound free : PureSyntaxQuotation.Ctx} (values : List (PureSyntaxQuotation.Tm bound free)) (w L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (readingsFromImagesSentence values w L)) := ZFReplay.replay (readingsFromImages_kernel_certificate values w L)

def readingsAtSentence {m} {bound free : PureSyntaxQuotation.Ctx} (values : List (PureSyntaxQuotation.Tm bound free)) (j : Fin values.length) (w L i q : Fin m) : Source.Sentence := ((TermImageReadingSyntax.readings values w L).imp ((SyntaxNumeralSyntax.numeral j.val i).imp (((StructuralListFieldSyntax.field w L i q).iff (PureQuotationSyntax.term (values.get j) w q))))).close

theorem source_readingsAt {m} {bound free : PureSyntaxQuotation.Ctx} (values : List (PureSyntaxQuotation.Tm bound free)) (j : Fin values.length) (w L i q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (readingsAtSentence values j w L i q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNumeralSyntax.numeral j.val i) (Context.add (TermImageReadingSyntax.readings values w L) (Source.SetLanguage.ZF.at m))
  have h0 : Derives Δ (TermImageReadingSyntax.readings values w L) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral j.val i) := .hyp (Or.inl rfl)
  exact TermImageReadingSyntax.at_index values w L j i q h0 h1

theorem readingsAt_kernel_certificate {m} {bound free : PureSyntaxQuotation.Ctx} (values : List (PureSyntaxQuotation.Tm bound free)) (j : Fin values.length) (w L i q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (readingsAtSentence values j w L i q)) := TheoryTransport.sentence (source_readingsAt values j w L i q)

theorem native_readingsAt {m} {bound free : PureSyntaxQuotation.Ctx} (values : List (PureSyntaxQuotation.Tm bound free)) (j : Fin values.length) (w L i q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (readingsAtSentence values j w L i q)) := ZFReplay.replay (readingsAt_kernel_certificate values j w L i q)

def agreeFromReadingsSentence {m} {bound free : PureSyntaxQuotation.Ctx} (values : List (PureSyntaxQuotation.Tm bound free)) (w a L V : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral values.length a).imp ((TermImageReadingSyntax.readings values w L).imp ((TermImageQuotationSyntax.images values w V).imp ((StructuralListCodeSyntax.agree w a L V)))))).close

theorem source_agreeFromReadings {m} {bound free : PureSyntaxQuotation.Ctx} (values : List (PureSyntaxQuotation.Tm bound free)) (w a L V : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (agreeFromReadingsSentence values w a L V) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (TermImageQuotationSyntax.images values w V) (Context.add (TermImageReadingSyntax.readings values w L) (Context.add (SyntaxNumeralSyntax.numeral values.length a) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral values.length a) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (TermImageReadingSyntax.readings values w L) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (TermImageQuotationSyntax.images values w V) := .hyp (Or.inl rfl)
  exact TermImageReading.agree_from_readings hZ values w a L V h0 h1 h2 h3

theorem agreeFromReadings_kernel_certificate {m} {bound free : PureSyntaxQuotation.Ctx} (values : List (PureSyntaxQuotation.Tm bound free)) (w a L V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (agreeFromReadingsSentence values w a L V)) := TheoryTransport.sentence (source_agreeFromReadings values w a L V)

theorem native_agreeFromReadings {m} {bound free : PureSyntaxQuotation.Ctx} (values : List (PureSyntaxQuotation.Tm bound free)) (w a L V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (agreeFromReadingsSentence values w a L V)) := ZFReplay.replay (agreeFromReadings_kernel_certificate values w a L V)

def imagesFromReadingsSentence {m} {bound free : PureSyntaxQuotation.Ctx} (values : List (PureSyntaxQuotation.Tm bound free)) (w a L : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral values.length a).imp ((StructuralListLengthSyntax.hasLength w L a).imp ((TermImageReadingSyntax.readings values w L).imp ((TermImageQuotationSyntax.images values w L)))))).close

theorem source_imagesFromReadings {m} {bound free : PureSyntaxQuotation.Ctx} (values : List (PureSyntaxQuotation.Tm bound free)) (w a L : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (imagesFromReadingsSentence values w a L) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (TermImageReadingSyntax.readings values w L) (Context.add (StructuralListLengthSyntax.hasLength w L a) (Context.add (SyntaxNumeralSyntax.numeral values.length a) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral values.length a) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (StructuralListLengthSyntax.hasLength w L a) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (TermImageReadingSyntax.readings values w L) := .hyp (Or.inl rfl)
  exact TermImageReading.images_of_readings hZ values w a L h0 h1 h2 h3

theorem imagesFromReadings_kernel_certificate {m} {bound free : PureSyntaxQuotation.Ctx} (values : List (PureSyntaxQuotation.Tm bound free)) (w a L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (imagesFromReadingsSentence values w a L)) := TheoryTransport.sentence (source_imagesFromReadings values w a L)

theorem native_imagesFromReadings {m} {bound free : PureSyntaxQuotation.Ctx} (values : List (PureSyntaxQuotation.Tm bound free)) (w a L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (imagesFromReadingsSentence values w a L)) := ZFReplay.replay (imagesFromReadings_kernel_certificate values w a L)

def zeroFieldSentence {m} (w R S a b c d A C K H U V z n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H).imp ((SyntaxFreeShiftSyntax.shiftMap w c C U).imp ((SyntaxIdentityMapSyntax.identityMap w d V).imp ((SyntaxMixedImageHead.head w C d z n).imp ((((Formula.mem z A).conj (StructuralListFieldSyntax.field w K z q)).iff (OriginalTreeQuotationSyntax.tree (.node 0 [YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.leaf 0]) w q)))))))).close

theorem source_zeroField {m} (w R S a b c d A C K H U V z n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (zeroFieldSentence w R S a b c d A C K H U V z n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMixedImageHead.head w C d z n) (Context.add (SyntaxIdentityMapSyntax.identityMap w d V) (Context.add (SyntaxFreeShiftSyntax.shiftMap w c C U) (Context.add (SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (SyntaxFreeShiftSyntax.shiftMap w c C U) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (SyntaxIdentityMapSyntax.identityMap w d V) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (SyntaxMixedImageHead.head w C d z n) := .hyp (Or.inl rfl)
  exact TermQuotationBinderFields.zero_iff hZ w R S a b c d A C K H U V z n q h0 h1 h2 h3 h4

theorem zeroField_kernel_certificate {m} (w R S a b c d A C K H U V z n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (zeroFieldSentence w R S a b c d A C K H U V z n q)) := TheoryTransport.sentence (source_zeroField w R S a b c d A C K H U V z n q)

theorem native_zeroField {m} (w R S a b c d A C K H U V z n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (zeroFieldSentence w R S a b c d A C K H U V z n q)) := ZFReplay.replay (zeroField_kernel_certificate w R S a b c d A C K H U V z n q)

def zeroAtNumeralSentence {m} (w R S a b c d A C K H U V z n i q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H).imp ((SyntaxFreeShiftSyntax.shiftMap w c C U).imp ((SyntaxIdentityMapSyntax.identityMap w d V).imp ((SyntaxMixedImageHead.head w C d z n).imp ((SyntaxNumeralSyntax.numeral 0 i).imp (((StructuralListFieldSyntax.field w K i q).iff (OriginalTreeQuotationSyntax.tree (.node 0 [YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.leaf 0]) w q))))))))).close

theorem source_zeroAtNumeral {m} (w R S a b c d A C K H U V z n i q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (zeroAtNumeralSentence w R S a b c d A C K H U V z n i q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNumeralSyntax.numeral 0 i) (Context.add (SyntaxMixedImageHead.head w C d z n) (Context.add (SyntaxIdentityMapSyntax.identityMap w d V) (Context.add (SyntaxFreeShiftSyntax.shiftMap w c C U) (Context.add (SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (SyntaxFreeShiftSyntax.shiftMap w c C U) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (SyntaxIdentityMapSyntax.identityMap w d V) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (SyntaxMixedImageHead.head w C d z n) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (SyntaxNumeralSyntax.numeral 0 i) := .hyp (Or.inl rfl)
  exact TermQuotationBinderValues.zero_at_numeral hZ w R S a b c d A C K H U V z n i q h0 h1 h2 h3 h4 h5

theorem zeroAtNumeral_kernel_certificate {m} (w R S a b c d A C K H U V z n i q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (zeroAtNumeralSentence w R S a b c d A C K H U V z n i q)) := TheoryTransport.sentence (source_zeroAtNumeral w R S a b c d A C K H U V z n i q)

theorem native_zeroAtNumeral {m} (w R S a b c d A C K H U V z n i q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (zeroAtNumeralSentence w R S a b c d A C K H U V z n i q)) := ZFReplay.replay (zeroAtNumeral_kernel_certificate w R S a b c d A C K H U V z n i q)

def boundAtCodeSentence {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (j : Fin bs.length) (w R S a b c d A C K H U V z n i v t q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral bs.length a).imp ((SyntaxNumeralSyntax.numeral bound.length c).imp ((SyntaxNumeralSyntax.numeral free.length d).imp ((TermQuotationEnvironmentSyntax.environment bs fs w a b c d R S).imp ((SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H).imp ((SyntaxFreeShiftSyntax.shiftMap w c C U).imp ((SyntaxIdentityMapSyntax.identityMap w d V).imp ((SyntaxMixedImageHead.head w C d z n).imp ((SyntaxNumeralSyntax.numeral j.val v).imp ((successor i v).imp ((PureQuotationSyntax.term (bs.get j) w t).imp ((((Formula.mem i A).conj (StructuralListFieldSyntax.field w K i q)).iff (PureQuotationSyntax.term ((bs.get j).weakenBound YesMetaZFC.SetTheory.SetSort.set) w q))))))))))))))).close

theorem source_boundAtCode {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (j : Fin bs.length) (w R S a b c d A C K H U V z n i v t q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (boundAtCodeSentence bs fs j w R S a b c d A C K H U V z n i v t q) := by
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
  apply Derives.impI
  let Δ : Context m := Context.add (PureQuotationSyntax.term (bs.get j) w t) (Context.add (successor i v) (Context.add (SyntaxNumeralSyntax.numeral j.val v) (Context.add (SyntaxMixedImageHead.head w C d z n) (Context.add (SyntaxIdentityMapSyntax.identityMap w d V) (Context.add (SyntaxFreeShiftSyntax.shiftMap w c C U) (Context.add (SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H) (Context.add (TermQuotationEnvironmentSyntax.environment bs fs w a b c d R S) (Context.add (SyntaxNumeralSyntax.numeral free.length d) (Context.add (SyntaxNumeralSyntax.numeral bound.length c) (Context.add (SyntaxNumeralSyntax.numeral bs.length a) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))))))))
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
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral bs.length a) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral bound.length c) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))
  have h3 : Derives Δ (SyntaxNumeralSyntax.numeral free.length d) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))
  have h4 : Derives Δ (TermQuotationEnvironmentSyntax.environment bs fs w a b c d R S) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  have h5 : Derives Δ (SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h6 : Derives Δ (SyntaxFreeShiftSyntax.shiftMap w c C U) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h7 : Derives Δ (SyntaxIdentityMapSyntax.identityMap w d V) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h8 : Derives Δ (SyntaxMixedImageHead.head w C d z n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h9 : Derives Δ (SyntaxNumeralSyntax.numeral j.val v) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h10 : Derives Δ (successor i v) := .hyp (Or.inr (Or.inl rfl))
  have h11 : Derives Δ (PureQuotationSyntax.term (bs.get j) w t) := .hyp (Or.inl rfl)
  exact TermQuotationBinderFields.bound_at_code hZ bs fs j w R S a b c d A C K H U V z n i v t q h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11

theorem boundAtCode_kernel_certificate {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (j : Fin bs.length) (w R S a b c d A C K H U V z n i v t q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (boundAtCodeSentence bs fs j w R S a b c d A C K H U V z n i v t q)) := TheoryTransport.sentence (source_boundAtCode bs fs j w R S a b c d A C K H U V z n i v t q)

theorem native_boundAtCode {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (j : Fin bs.length) (w R S a b c d A C K H U V z n i v t q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (boundAtCodeSentence bs fs j w R S a b c d A C K H U V z n i v t q)) := ZFReplay.replay (boundAtCode_kernel_certificate bs fs j w R S a b c d A C K H U V z n i v t q)

def boundValueSentence {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (j : Fin bs.length) (w R S a b c d A C K H U V z n i v q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral bs.length a).imp ((SyntaxNumeralSyntax.numeral bound.length c).imp ((SyntaxNumeralSyntax.numeral free.length d).imp ((TermQuotationEnvironmentSyntax.environment bs fs w a b c d R S).imp ((SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H).imp ((SyntaxFreeShiftSyntax.shiftMap w c C U).imp ((SyntaxIdentityMapSyntax.identityMap w d V).imp ((SyntaxMixedImageHead.head w C d z n).imp ((SyntaxNumeralSyntax.numeral j.val v).imp ((successor i v).imp ((((Formula.mem i A).conj (StructuralListFieldSyntax.field w K i q)).iff (PureQuotationSyntax.term ((bs.get j).weakenBound YesMetaZFC.SetTheory.SetSort.set) w q)))))))))))))).close

theorem source_boundValue {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (j : Fin bs.length) (w R S a b c d A C K H U V z n i v q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (boundValueSentence bs fs j w R S a b c d A C K H U V z n i v q) := by
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
  let Δ : Context m := Context.add (successor i v) (Context.add (SyntaxNumeralSyntax.numeral j.val v) (Context.add (SyntaxMixedImageHead.head w C d z n) (Context.add (SyntaxIdentityMapSyntax.identityMap w d V) (Context.add (SyntaxFreeShiftSyntax.shiftMap w c C U) (Context.add (SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H) (Context.add (TermQuotationEnvironmentSyntax.environment bs fs w a b c d R S) (Context.add (SyntaxNumeralSyntax.numeral free.length d) (Context.add (SyntaxNumeralSyntax.numeral bound.length c) (Context.add (SyntaxNumeralSyntax.numeral bs.length a) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))))))
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
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral bs.length a) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral bound.length c) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))
  have h3 : Derives Δ (SyntaxNumeralSyntax.numeral free.length d) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  have h4 : Derives Δ (TermQuotationEnvironmentSyntax.environment bs fs w a b c d R S) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h5 : Derives Δ (SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h6 : Derives Δ (SyntaxFreeShiftSyntax.shiftMap w c C U) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h7 : Derives Δ (SyntaxIdentityMapSyntax.identityMap w d V) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h8 : Derives Δ (SyntaxMixedImageHead.head w C d z n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h9 : Derives Δ (SyntaxNumeralSyntax.numeral j.val v) := .hyp (Or.inr (Or.inl rfl))
  have h10 : Derives Δ (successor i v) := .hyp (Or.inl rfl)
  exact TermQuotationBinderValues.bound_iff hZ bs fs j w R S a b c d A C K H U V z n i v q h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10

theorem boundValue_kernel_certificate {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (j : Fin bs.length) (w R S a b c d A C K H U V z n i v q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (boundValueSentence bs fs j w R S a b c d A C K H U V z n i v q)) := TheoryTransport.sentence (source_boundValue bs fs j w R S a b c d A C K H U V z n i v q)

theorem native_boundValue {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (j : Fin bs.length) (w R S a b c d A C K H U V z n i v q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (boundValueSentence bs fs j w R S a b c d A C K H U V z n i v q)) := ZFReplay.replay (boundValue_kernel_certificate bs fs j w R S a b c d A C K H U V z n i v q)

def boundAtNumeralSentence {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (j : Fin bs.length) (w R S a b c d A C K H U V z n i q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral bs.length a).imp ((SyntaxNumeralSyntax.numeral bound.length c).imp ((SyntaxNumeralSyntax.numeral free.length d).imp ((TermQuotationEnvironmentSyntax.environment bs fs w a b c d R S).imp ((SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H).imp ((SyntaxFreeShiftSyntax.shiftMap w c C U).imp ((SyntaxIdentityMapSyntax.identityMap w d V).imp ((SyntaxMixedImageHead.head w C d z n).imp ((SyntaxNumeralSyntax.numeral (j.val+1) i).imp ((((Formula.mem i A).conj (StructuralListFieldSyntax.field w K i q)).iff (PureQuotationSyntax.term ((bs.get j).weakenBound YesMetaZFC.SetTheory.SetSort.set) w q))))))))))))).close

theorem source_boundAtNumeral {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (j : Fin bs.length) (w R S a b c d A C K H U V z n i q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (boundAtNumeralSentence bs fs j w R S a b c d A C K H U V z n i q) := by
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
  let Δ : Context m := Context.add (SyntaxNumeralSyntax.numeral (j.val+1) i) (Context.add (SyntaxMixedImageHead.head w C d z n) (Context.add (SyntaxIdentityMapSyntax.identityMap w d V) (Context.add (SyntaxFreeShiftSyntax.shiftMap w c C U) (Context.add (SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H) (Context.add (TermQuotationEnvironmentSyntax.environment bs fs w a b c d R S) (Context.add (SyntaxNumeralSyntax.numeral free.length d) (Context.add (SyntaxNumeralSyntax.numeral bound.length c) (Context.add (SyntaxNumeralSyntax.numeral bs.length a) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))))))
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
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral bs.length a) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral bound.length c) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  have h3 : Derives Δ (SyntaxNumeralSyntax.numeral free.length d) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h4 : Derives Δ (TermQuotationEnvironmentSyntax.environment bs fs w a b c d R S) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h5 : Derives Δ (SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h6 : Derives Δ (SyntaxFreeShiftSyntax.shiftMap w c C U) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h7 : Derives Δ (SyntaxIdentityMapSyntax.identityMap w d V) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h8 : Derives Δ (SyntaxMixedImageHead.head w C d z n) := .hyp (Or.inr (Or.inl rfl))
  have h9 : Derives Δ (SyntaxNumeralSyntax.numeral (j.val+1) i) := .hyp (Or.inl rfl)
  exact TermQuotationBinderValues.bound_at_numeral hZ bs fs j w R S a b c d A C K H U V z n i q h0 h1 h2 h3 h4 h5 h6 h7 h8 h9

theorem boundAtNumeral_kernel_certificate {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (j : Fin bs.length) (w R S a b c d A C K H U V z n i q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (boundAtNumeralSentence bs fs j w R S a b c d A C K H U V z n i q)) := TheoryTransport.sentence (source_boundAtNumeral bs fs j w R S a b c d A C K H U V z n i q)

theorem native_boundAtNumeral {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (j : Fin bs.length) (w R S a b c d A C K H U V z n i q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (boundAtNumeralSentence bs fs j w R S a b c d A C K H U V z n i q)) := ZFReplay.replay (boundAtNumeral_kernel_certificate bs fs j w R S a b c d A C K H U V z n i q)

def boundReadingsSentence {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (w R S a b c d A C K H U V z n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral bs.length a).imp ((SyntaxNumeralSyntax.numeral bound.length c).imp ((SyntaxNumeralSyntax.numeral free.length d).imp ((TermQuotationEnvironmentSyntax.environment bs fs w a b c d R S).imp ((SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H).imp ((SyntaxFreeShiftSyntax.shiftMap w c C U).imp ((SyntaxIdentityMapSyntax.identityMap w d V).imp ((SyntaxMixedImageHead.head w C d z n).imp ((TermImageReadingSyntax.readings (TermQuotationLiftSyntax.newBound bs) w K))))))))))).close

theorem source_boundReadings {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (w R S a b c d A C K H U V z n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (boundReadingsSentence bs fs w R S a b c d A C K H U V z n) := by
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
  let Δ : Context m := Context.add (SyntaxMixedImageHead.head w C d z n) (Context.add (SyntaxIdentityMapSyntax.identityMap w d V) (Context.add (SyntaxFreeShiftSyntax.shiftMap w c C U) (Context.add (SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H) (Context.add (TermQuotationEnvironmentSyntax.environment bs fs w a b c d R S) (Context.add (SyntaxNumeralSyntax.numeral free.length d) (Context.add (SyntaxNumeralSyntax.numeral bound.length c) (Context.add (SyntaxNumeralSyntax.numeral bs.length a) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))))
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
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral bs.length a) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral bound.length c) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h3 : Derives Δ (SyntaxNumeralSyntax.numeral free.length d) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h4 : Derives Δ (TermQuotationEnvironmentSyntax.environment bs fs w a b c d R S) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h5 : Derives Δ (SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h6 : Derives Δ (SyntaxFreeShiftSyntax.shiftMap w c C U) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h7 : Derives Δ (SyntaxIdentityMapSyntax.identityMap w d V) := .hyp (Or.inr (Or.inl rfl))
  have h8 : Derives Δ (SyntaxMixedImageHead.head w C d z n) := .hyp (Or.inl rfl)
  exact TermQuotationLiftReading.bound_readings hZ bs fs w R S a b c d A C K H U V z n h0 h1 h2 h3 h4 h5 h6 h7 h8

theorem boundReadings_kernel_certificate {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (w R S a b c d A C K H U V z n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (boundReadingsSentence bs fs w R S a b c d A C K H U V z n)) := TheoryTransport.sentence (source_boundReadings bs fs w R S a b c d A C K H U V z n)

theorem native_boundReadings {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (w R S a b c d A C K H U V z n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (boundReadingsSentence bs fs w R S a b c d A C K H U V z n)) := ZFReplay.replay (boundReadings_kernel_certificate bs fs w R S a b c d A C K H U V z n)

def freeAtCodeSentence {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (j : Fin fs.length) (w R S a b c d A C K H U V z n v t q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral fs.length b).imp ((SyntaxNumeralSyntax.numeral bound.length c).imp ((SyntaxNumeralSyntax.numeral free.length d).imp ((TermQuotationEnvironmentSyntax.environment bs fs w a b c d R S).imp ((SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H).imp ((SyntaxFreeShiftSyntax.shiftMap w c C U).imp ((SyntaxIdentityMapSyntax.identityMap w d V).imp ((SyntaxMixedImageHead.head w C d z n).imp ((SyntaxNumeralSyntax.numeral j.val v).imp ((PureQuotationSyntax.term (fs.get j) w t).imp ((((Formula.mem v b).conj (StructuralListFieldSyntax.field w H v q)).iff (PureQuotationSyntax.term ((fs.get j).weakenBound YesMetaZFC.SetTheory.SetSort.set) w q)))))))))))))).close

theorem source_freeAtCode {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (j : Fin fs.length) (w R S a b c d A C K H U V z n v t q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (freeAtCodeSentence bs fs j w R S a b c d A C K H U V z n v t q) := by
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
  let Δ : Context m := Context.add (PureQuotationSyntax.term (fs.get j) w t) (Context.add (SyntaxNumeralSyntax.numeral j.val v) (Context.add (SyntaxMixedImageHead.head w C d z n) (Context.add (SyntaxIdentityMapSyntax.identityMap w d V) (Context.add (SyntaxFreeShiftSyntax.shiftMap w c C U) (Context.add (SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H) (Context.add (TermQuotationEnvironmentSyntax.environment bs fs w a b c d R S) (Context.add (SyntaxNumeralSyntax.numeral free.length d) (Context.add (SyntaxNumeralSyntax.numeral bound.length c) (Context.add (SyntaxNumeralSyntax.numeral fs.length b) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))))))
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
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral fs.length b) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral bound.length c) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))
  have h3 : Derives Δ (SyntaxNumeralSyntax.numeral free.length d) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  have h4 : Derives Δ (TermQuotationEnvironmentSyntax.environment bs fs w a b c d R S) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h5 : Derives Δ (SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h6 : Derives Δ (SyntaxFreeShiftSyntax.shiftMap w c C U) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h7 : Derives Δ (SyntaxIdentityMapSyntax.identityMap w d V) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h8 : Derives Δ (SyntaxMixedImageHead.head w C d z n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h9 : Derives Δ (SyntaxNumeralSyntax.numeral j.val v) := .hyp (Or.inr (Or.inl rfl))
  have h10 : Derives Δ (PureQuotationSyntax.term (fs.get j) w t) := .hyp (Or.inl rfl)
  exact TermQuotationBinderFields.free_at_code hZ bs fs j w R S a b c d A C K H U V z n v t q h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10

theorem freeAtCode_kernel_certificate {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (j : Fin fs.length) (w R S a b c d A C K H U V z n v t q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (freeAtCodeSentence bs fs j w R S a b c d A C K H U V z n v t q)) := TheoryTransport.sentence (source_freeAtCode bs fs j w R S a b c d A C K H U V z n v t q)

theorem native_freeAtCode {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (j : Fin fs.length) (w R S a b c d A C K H U V z n v t q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (freeAtCodeSentence bs fs j w R S a b c d A C K H U V z n v t q)) := ZFReplay.replay (freeAtCode_kernel_certificate bs fs j w R S a b c d A C K H U V z n v t q)

def freeValueSentence {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (j : Fin fs.length) (w R S a b c d A C K H U V z n v q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral fs.length b).imp ((SyntaxNumeralSyntax.numeral bound.length c).imp ((SyntaxNumeralSyntax.numeral free.length d).imp ((TermQuotationEnvironmentSyntax.environment bs fs w a b c d R S).imp ((SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H).imp ((SyntaxFreeShiftSyntax.shiftMap w c C U).imp ((SyntaxIdentityMapSyntax.identityMap w d V).imp ((SyntaxMixedImageHead.head w C d z n).imp ((SyntaxNumeralSyntax.numeral j.val v).imp ((((Formula.mem v b).conj (StructuralListFieldSyntax.field w H v q)).iff (PureQuotationSyntax.term ((fs.get j).weakenBound YesMetaZFC.SetTheory.SetSort.set) w q))))))))))))).close

theorem source_freeValue {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (j : Fin fs.length) (w R S a b c d A C K H U V z n v q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (freeValueSentence bs fs j w R S a b c d A C K H U V z n v q) := by
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
  let Δ : Context m := Context.add (SyntaxNumeralSyntax.numeral j.val v) (Context.add (SyntaxMixedImageHead.head w C d z n) (Context.add (SyntaxIdentityMapSyntax.identityMap w d V) (Context.add (SyntaxFreeShiftSyntax.shiftMap w c C U) (Context.add (SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H) (Context.add (TermQuotationEnvironmentSyntax.environment bs fs w a b c d R S) (Context.add (SyntaxNumeralSyntax.numeral free.length d) (Context.add (SyntaxNumeralSyntax.numeral bound.length c) (Context.add (SyntaxNumeralSyntax.numeral fs.length b) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))))))
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
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral fs.length b) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral bound.length c) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  have h3 : Derives Δ (SyntaxNumeralSyntax.numeral free.length d) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h4 : Derives Δ (TermQuotationEnvironmentSyntax.environment bs fs w a b c d R S) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h5 : Derives Δ (SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h6 : Derives Δ (SyntaxFreeShiftSyntax.shiftMap w c C U) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h7 : Derives Δ (SyntaxIdentityMapSyntax.identityMap w d V) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h8 : Derives Δ (SyntaxMixedImageHead.head w C d z n) := .hyp (Or.inr (Or.inl rfl))
  have h9 : Derives Δ (SyntaxNumeralSyntax.numeral j.val v) := .hyp (Or.inl rfl)
  exact TermQuotationBinderValues.free_iff hZ bs fs j w R S a b c d A C K H U V z n v q h0 h1 h2 h3 h4 h5 h6 h7 h8 h9

theorem freeValue_kernel_certificate {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (j : Fin fs.length) (w R S a b c d A C K H U V z n v q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (freeValueSentence bs fs j w R S a b c d A C K H U V z n v q)) := TheoryTransport.sentence (source_freeValue bs fs j w R S a b c d A C K H U V z n v q)

theorem native_freeValue {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (j : Fin fs.length) (w R S a b c d A C K H U V z n v q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (freeValueSentence bs fs j w R S a b c d A C K H U V z n v q)) := ZFReplay.replay (freeValue_kernel_certificate bs fs j w R S a b c d A C K H U V z n v q)

def freeReadingsSentence {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (w R S a b c d A C K H U V z n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral fs.length b).imp ((SyntaxNumeralSyntax.numeral bound.length c).imp ((SyntaxNumeralSyntax.numeral free.length d).imp ((TermQuotationEnvironmentSyntax.environment bs fs w a b c d R S).imp ((SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H).imp ((SyntaxFreeShiftSyntax.shiftMap w c C U).imp ((SyntaxIdentityMapSyntax.identityMap w d V).imp ((SyntaxMixedImageHead.head w C d z n).imp ((TermImageReadingSyntax.readings (TermQuotationLiftSyntax.shifted fs) w H))))))))))).close

theorem source_freeReadings {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (w R S a b c d A C K H U V z n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (freeReadingsSentence bs fs w R S a b c d A C K H U V z n) := by
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
  let Δ : Context m := Context.add (SyntaxMixedImageHead.head w C d z n) (Context.add (SyntaxIdentityMapSyntax.identityMap w d V) (Context.add (SyntaxFreeShiftSyntax.shiftMap w c C U) (Context.add (SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H) (Context.add (TermQuotationEnvironmentSyntax.environment bs fs w a b c d R S) (Context.add (SyntaxNumeralSyntax.numeral free.length d) (Context.add (SyntaxNumeralSyntax.numeral bound.length c) (Context.add (SyntaxNumeralSyntax.numeral fs.length b) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))))
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
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral fs.length b) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral bound.length c) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h3 : Derives Δ (SyntaxNumeralSyntax.numeral free.length d) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h4 : Derives Δ (TermQuotationEnvironmentSyntax.environment bs fs w a b c d R S) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h5 : Derives Δ (SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h6 : Derives Δ (SyntaxFreeShiftSyntax.shiftMap w c C U) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h7 : Derives Δ (SyntaxIdentityMapSyntax.identityMap w d V) := .hyp (Or.inr (Or.inl rfl))
  have h8 : Derives Δ (SyntaxMixedImageHead.head w C d z n) := .hyp (Or.inl rfl)
  exact TermQuotationLiftReading.free_readings hZ bs fs w R S a b c d A C K H U V z n h0 h1 h2 h3 h4 h5 h6 h7 h8

theorem freeReadings_kernel_certificate {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (w R S a b c d A C K H U V z n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (freeReadingsSentence bs fs w R S a b c d A C K H U V z n)) := TheoryTransport.sentence (source_freeReadings bs fs w R S a b c d A C K H U V z n)

theorem native_freeReadings {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (w R S a b c d A C K H U V z n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (freeReadingsSentence bs fs w R S a b c d A C K H U V z n)) := ZFReplay.replay (freeReadings_kernel_certificate bs fs w R S a b c d A C K H U V z n)

def environmentAtWitnessesSentence {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (w R S a b c d A C K H U V z n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral bs.length a).imp ((SyntaxNumeralSyntax.numeral fs.length b).imp ((SyntaxNumeralSyntax.numeral bound.length c).imp ((SyntaxNumeralSyntax.numeral free.length d).imp ((TermQuotationEnvironmentSyntax.environment bs fs w a b c d R S).imp ((SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H).imp ((SyntaxFreeShiftSyntax.shiftMap w c C U).imp ((SyntaxIdentityMapSyntax.identityMap w d V).imp ((SyntaxMixedImageHead.head w C d z n).imp ((TermQuotationEnvironmentSyntax.environment (TermQuotationLiftSyntax.newBound bs) (TermQuotationLiftSyntax.shifted fs) w A b C d K H)))))))))))).close

theorem source_environmentAtWitnesses {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (w R S a b c d A C K H U V z n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (environmentAtWitnessesSentence bs fs w R S a b c d A C K H U V z n) := by
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
  let Δ : Context m := Context.add (SyntaxMixedImageHead.head w C d z n) (Context.add (SyntaxIdentityMapSyntax.identityMap w d V) (Context.add (SyntaxFreeShiftSyntax.shiftMap w c C U) (Context.add (SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H) (Context.add (TermQuotationEnvironmentSyntax.environment bs fs w a b c d R S) (Context.add (SyntaxNumeralSyntax.numeral free.length d) (Context.add (SyntaxNumeralSyntax.numeral bound.length c) (Context.add (SyntaxNumeralSyntax.numeral fs.length b) (Context.add (SyntaxNumeralSyntax.numeral bs.length a) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))))))
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
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral bs.length a) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral fs.length b) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  have h3 : Derives Δ (SyntaxNumeralSyntax.numeral bound.length c) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h4 : Derives Δ (SyntaxNumeralSyntax.numeral free.length d) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h5 : Derives Δ (TermQuotationEnvironmentSyntax.environment bs fs w a b c d R S) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h6 : Derives Δ (SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h7 : Derives Δ (SyntaxFreeShiftSyntax.shiftMap w c C U) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h8 : Derives Δ (SyntaxIdentityMapSyntax.identityMap w d V) := .hyp (Or.inr (Or.inl rfl))
  have h9 : Derives Δ (SyntaxMixedImageHead.head w C d z n) := .hyp (Or.inl rfl)
  exact TermQuotationLiftEnvironment.at_witnesses hZ bs fs w R S a b c d A C K H U V z n h0 h1 h2 h3 h4 h5 h6 h7 h8 h9

theorem environmentAtWitnesses_kernel_certificate {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (w R S a b c d A C K H U V z n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (environmentAtWitnessesSentence bs fs w R S a b c d A C K H U V z n)) := TheoryTransport.sentence (source_environmentAtWitnesses bs fs w R S a b c d A C K H U V z n)

theorem native_environmentAtWitnesses {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (w R S a b c d A C K H U V z n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (environmentAtWitnessesSentence bs fs w R S a b c d A C K H U V z n)) := ZFReplay.replay (environmentAtWitnesses_kernel_certificate bs fs w R S a b c d A C K H U V z n)

def environmentAtMapsSentence {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (w R S a b c d A C K H U V : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral bs.length a).imp ((SyntaxNumeralSyntax.numeral fs.length b).imp ((SyntaxNumeralSyntax.numeral bound.length c).imp ((SyntaxNumeralSyntax.numeral free.length d).imp ((TermQuotationEnvironmentSyntax.environment bs fs w a b c d R S).imp ((SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H).imp ((SyntaxFreeShiftSyntax.shiftMap w c C U).imp ((SyntaxIdentityMapSyntax.identityMap w d V).imp ((TermQuotationEnvironmentSyntax.environment (TermQuotationLiftSyntax.newBound bs) (TermQuotationLiftSyntax.shifted fs) w A b C d K H))))))))))).close

theorem source_environmentAtMaps {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (w R S a b c d A C K H U V : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (environmentAtMapsSentence bs fs w R S a b c d A C K H U V) := by
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
  let Δ : Context m := Context.add (SyntaxIdentityMapSyntax.identityMap w d V) (Context.add (SyntaxFreeShiftSyntax.shiftMap w c C U) (Context.add (SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H) (Context.add (TermQuotationEnvironmentSyntax.environment bs fs w a b c d R S) (Context.add (SyntaxNumeralSyntax.numeral free.length d) (Context.add (SyntaxNumeralSyntax.numeral bound.length c) (Context.add (SyntaxNumeralSyntax.numeral fs.length b) (Context.add (SyntaxNumeralSyntax.numeral bs.length a) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))))
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
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral bs.length a) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral fs.length b) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h3 : Derives Δ (SyntaxNumeralSyntax.numeral bound.length c) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h4 : Derives Δ (SyntaxNumeralSyntax.numeral free.length d) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h5 : Derives Δ (TermQuotationEnvironmentSyntax.environment bs fs w a b c d R S) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h6 : Derives Δ (SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h7 : Derives Δ (SyntaxFreeShiftSyntax.shiftMap w c C U) := .hyp (Or.inr (Or.inl rfl))
  have h8 : Derives Δ (SyntaxIdentityMapSyntax.identityMap w d V) := .hyp (Or.inl rfl)
  exact TermQuotationLiftEnvironment.at_maps hZ bs fs w R S a b c d A C K H U V h0 h1 h2 h3 h4 h5 h6 h7 h8

theorem environmentAtMaps_kernel_certificate {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (w R S a b c d A C K H U V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (environmentAtMapsSentence bs fs w R S a b c d A C K H U V)) := TheoryTransport.sentence (source_environmentAtMaps bs fs w R S a b c d A C K H U V)

theorem native_environmentAtMaps {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (w R S a b c d A C K H U V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (environmentAtMapsSentence bs fs w R S a b c d A C K H U V)) := ZFReplay.replay (environmentAtMaps_kernel_certificate bs fs w R S a b c d A C K H U V)

def environmentAtLiftedSentence {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (w R S a b c d A C K H : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral bs.length a).imp ((SyntaxNumeralSyntax.numeral fs.length b).imp ((SyntaxNumeralSyntax.numeral bound.length c).imp ((SyntaxNumeralSyntax.numeral free.length d).imp ((TermQuotationEnvironmentSyntax.environment bs fs w a b c d R S).imp ((SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H).imp ((TermQuotationEnvironmentSyntax.environment (TermQuotationLiftSyntax.newBound bs) (TermQuotationLiftSyntax.shifted fs) w A b C d K H))))))))).close

theorem source_environmentAtLifted {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (w R S a b c d A C K H : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (environmentAtLiftedSentence bs fs w R S a b c d A C K H) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H) (Context.add (TermQuotationEnvironmentSyntax.environment bs fs w a b c d R S) (Context.add (SyntaxNumeralSyntax.numeral free.length d) (Context.add (SyntaxNumeralSyntax.numeral bound.length c) (Context.add (SyntaxNumeralSyntax.numeral fs.length b) (Context.add (SyntaxNumeralSyntax.numeral bs.length a) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))
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
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral bs.length a) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral fs.length b) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h3 : Derives Δ (SyntaxNumeralSyntax.numeral bound.length c) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : Derives Δ (SyntaxNumeralSyntax.numeral free.length d) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h5 : Derives Δ (TermQuotationEnvironmentSyntax.environment bs fs w a b c d R S) := .hyp (Or.inr (Or.inl rfl))
  have h6 : Derives Δ (SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H) := .hyp (Or.inl rfl)
  exact TermQuotationLiftEnvironment.at_lifted hZ bs fs w R S a b c d A C K H h0 h1 h2 h3 h4 h5 h6

theorem environmentAtLifted_kernel_certificate {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (w R S a b c d A C K H : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (environmentAtLiftedSentence bs fs w R S a b c d A C K H)) := TheoryTransport.sentence (source_environmentAtLifted bs fs w R S a b c d A C K H)

theorem native_environmentAtLifted {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (w R S a b c d A C K H : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (environmentAtLiftedSentence bs fs w R S a b c d A C K H)) := ZFReplay.replay (environmentAtLifted_kernel_certificate bs fs w R S a b c d A C K H)

def liftedFromEnvironmentSentence {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (w R S a b c d A C K H : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral bs.length a).imp ((SyntaxNumeralSyntax.numeral fs.length b).imp ((SyntaxNumeralSyntax.numeral bound.length c).imp ((SyntaxNumeralSyntax.numeral free.length d).imp ((TermQuotationEnvironmentSyntax.environment bs fs w a b c d R S).imp ((successor A a).imp ((successor C c).imp ((TermQuotationEnvironmentSyntax.environment (TermQuotationLiftSyntax.newBound bs) (TermQuotationLiftSyntax.shifted fs) w A b C d K H).imp ((SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H))))))))))).close

theorem source_liftedFromEnvironment {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (w R S a b c d A C K H : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (liftedFromEnvironmentSentence bs fs w R S a b c d A C K H) := by
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
  let Δ : Context m := Context.add (TermQuotationEnvironmentSyntax.environment (TermQuotationLiftSyntax.newBound bs) (TermQuotationLiftSyntax.shifted fs) w A b C d K H) (Context.add (successor C c) (Context.add (successor A a) (Context.add (TermQuotationEnvironmentSyntax.environment bs fs w a b c d R S) (Context.add (SyntaxNumeralSyntax.numeral free.length d) (Context.add (SyntaxNumeralSyntax.numeral bound.length c) (Context.add (SyntaxNumeralSyntax.numeral fs.length b) (Context.add (SyntaxNumeralSyntax.numeral bs.length a) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))))
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
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral bs.length a) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral fs.length b) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h3 : Derives Δ (SyntaxNumeralSyntax.numeral bound.length c) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h4 : Derives Δ (SyntaxNumeralSyntax.numeral free.length d) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h5 : Derives Δ (TermQuotationEnvironmentSyntax.environment bs fs w a b c d R S) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h6 : Derives Δ (successor A a) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h7 : Derives Δ (successor C c) := .hyp (Or.inr (Or.inl rfl))
  have h8 : Derives Δ (TermQuotationEnvironmentSyntax.environment (TermQuotationLiftSyntax.newBound bs) (TermQuotationLiftSyntax.shifted fs) w A b C d K H) := .hyp (Or.inl rfl)
  exact TermQuotationLiftCorrespondence.of_environment hZ bs fs w R S a b c d A C K H h0 h1 h2 h3 h4 h5 h6 h7 h8

theorem liftedFromEnvironment_kernel_certificate {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (w R S a b c d A C K H : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (liftedFromEnvironmentSentence bs fs w R S a b c d A C K H)) := TheoryTransport.sentence (source_liftedFromEnvironment bs fs w R S a b c d A C K H)

theorem native_liftedFromEnvironment {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (w R S a b c d A C K H : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (liftedFromEnvironmentSentence bs fs w R S a b c d A C K H)) := ZFReplay.replay (liftedFromEnvironment_kernel_certificate bs fs w R S a b c d A C K H)

def liftedIffEnvironmentSentence {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (w R S a b c d A C K H : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral bs.length a).imp ((SyntaxNumeralSyntax.numeral fs.length b).imp ((SyntaxNumeralSyntax.numeral bound.length c).imp ((SyntaxNumeralSyntax.numeral free.length d).imp ((TermQuotationEnvironmentSyntax.environment bs fs w a b c d R S).imp ((successor A a).imp ((successor C c).imp (((SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H).iff (TermQuotationEnvironmentSyntax.environment (TermQuotationLiftSyntax.newBound bs) (TermQuotationLiftSyntax.shifted fs) w A b C d K H))))))))))).close

theorem source_liftedIffEnvironment {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (w R S a b c d A C K H : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (liftedIffEnvironmentSentence bs fs w R S a b c d A C K H) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor C c) (Context.add (successor A a) (Context.add (TermQuotationEnvironmentSyntax.environment bs fs w a b c d R S) (Context.add (SyntaxNumeralSyntax.numeral free.length d) (Context.add (SyntaxNumeralSyntax.numeral bound.length c) (Context.add (SyntaxNumeralSyntax.numeral fs.length b) (Context.add (SyntaxNumeralSyntax.numeral bs.length a) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral bs.length a) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral fs.length b) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h3 : Derives Δ (SyntaxNumeralSyntax.numeral bound.length c) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h4 : Derives Δ (SyntaxNumeralSyntax.numeral free.length d) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h5 : Derives Δ (TermQuotationEnvironmentSyntax.environment bs fs w a b c d R S) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h6 : Derives Δ (successor A a) := .hyp (Or.inr (Or.inl rfl))
  have h7 : Derives Δ (successor C c) := .hyp (Or.inl rfl)
  exact TermQuotationLiftCorrespondence.lifted_iff_environment hZ bs fs w R S a b c d A C K H h0 h1 h2 h3 h4 h5 h6 h7

theorem liftedIffEnvironment_kernel_certificate {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (w R S a b c d A C K H : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (liftedIffEnvironmentSentence bs fs w R S a b c d A C K H)) := TheoryTransport.sentence (source_liftedIffEnvironment bs fs w R S a b c d A C K H)

theorem native_liftedIffEnvironment {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (w R S a b c d A C K H : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (liftedIffEnvironmentSentence bs fs w R S a b c d A C K H)) := ZFReplay.replay (liftedIffEnvironment_kernel_certificate bs fs w R S a b c d A C K H)

def environmentFiberSentence {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (w a b c d A C : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral bs.length a).imp ((SyntaxNumeralSyntax.numeral fs.length b).imp ((SyntaxNumeralSyntax.numeral bound.length c).imp ((SyntaxNumeralSyntax.numeral free.length d).imp ((successor A a).imp ((successor C c).imp ((TermQuotationEnvironmentSyntax.fiber (TermQuotationLiftSyntax.newBound bs) (TermQuotationLiftSyntax.shifted fs) w A b C d))))))))).close

theorem source_environmentFiber {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (w a b c d A C : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (environmentFiberSentence bs fs w a b c d A C) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor C c) (Context.add (successor A a) (Context.add (SyntaxNumeralSyntax.numeral free.length d) (Context.add (SyntaxNumeralSyntax.numeral bound.length c) (Context.add (SyntaxNumeralSyntax.numeral fs.length b) (Context.add (SyntaxNumeralSyntax.numeral bs.length a) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))
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
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral bs.length a) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral fs.length b) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h3 : Derives Δ (SyntaxNumeralSyntax.numeral bound.length c) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : Derives Δ (SyntaxNumeralSyntax.numeral free.length d) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h5 : Derives Δ (successor A a) := .hyp (Or.inr (Or.inl rfl))
  have h6 : Derives Δ (successor C c) := .hyp (Or.inl rfl)
  exact TermQuotationLiftCorrespondence.actual_environment_fiber hZ bs fs w a b c d A C h0 h1 h2 h3 h4 h5 h6

theorem environmentFiber_kernel_certificate {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (w a b c d A C : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (environmentFiberSentence bs fs w a b c d A C)) := TheoryTransport.sentence (source_environmentFiber bs fs w a b c d A C)

theorem native_environmentFiber {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (w a b c d A C : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (environmentFiberSentence bs fs w a b c d A C)) := ZFReplay.replay (environmentFiber_kernel_certificate bs fs w a b c d A C)

def jointFiberSentence {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (w R S a b c d A C : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral bs.length a).imp ((SyntaxNumeralSyntax.numeral fs.length b).imp ((SyntaxNumeralSyntax.numeral bound.length c).imp ((SyntaxNumeralSyntax.numeral free.length d).imp ((TermQuotationEnvironmentSyntax.environment bs fs w a b c d R S).imp ((successor A a).imp ((successor C c).imp ((TermQuotationLiftJointSyntax.fiber bs fs w R S a b c d A C)))))))))).close

theorem source_jointFiber {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (w R S a b c d A C : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (jointFiberSentence bs fs w R S a b c d A C) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor C c) (Context.add (successor A a) (Context.add (TermQuotationEnvironmentSyntax.environment bs fs w a b c d R S) (Context.add (SyntaxNumeralSyntax.numeral free.length d) (Context.add (SyntaxNumeralSyntax.numeral bound.length c) (Context.add (SyntaxNumeralSyntax.numeral fs.length b) (Context.add (SyntaxNumeralSyntax.numeral bs.length a) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral bs.length a) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral fs.length b) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h3 : Derives Δ (SyntaxNumeralSyntax.numeral bound.length c) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h4 : Derives Δ (SyntaxNumeralSyntax.numeral free.length d) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h5 : Derives Δ (TermQuotationEnvironmentSyntax.environment bs fs w a b c d R S) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h6 : Derives Δ (successor A a) := .hyp (Or.inr (Or.inl rfl))
  have h7 : Derives Δ (successor C c) := .hyp (Or.inl rfl)
  exact TermQuotationLiftJoint.actual_fiber hZ bs fs w R S a b c d A C h0 h1 h2 h3 h4 h5 h6 h7

theorem jointFiber_kernel_certificate {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (w R S a b c d A C : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (jointFiberSentence bs fs w R S a b c d A C)) := TheoryTransport.sentence (source_jointFiber bs fs w R S a b c d A C)

theorem native_jointFiber {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (w R S a b c d A C : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (jointFiberSentence bs fs w R S a b c d A C)) := ZFReplay.replay (jointFiber_kernel_certificate bs fs w R S a b c d A C)

end PPAC.Migration.Internal.ObjectTermLiftQuotation
