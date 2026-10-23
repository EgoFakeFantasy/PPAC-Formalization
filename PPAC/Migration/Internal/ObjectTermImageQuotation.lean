import PPAC.Migration.Internal.TermQuotationShift

/-! 项像quotation实际环境、混合项替换和绑定变量提升的精确数值对应的原YesMetaZFC核证书。 -/
namespace PPAC.Migration.Internal.ObjectTermImageQuotation
open Source SourceAlgebra SourceLogic OmegaSyntax

def quotationAtValueSentence {m} (input : YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree) (w n q : Fin m) : Source.Sentence := ((omega w).imp ((OriginalTreeQuotationSyntax.tree input w n).imp (((OriginalTreeQuotationSyntax.tree input w q).iff (.equal q n))))).close

theorem source_quotationAtValue {m} (input : YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree) (w n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (quotationAtValueSentence input w n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (OriginalTreeQuotationSyntax.tree input w n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (OriginalTreeQuotationSyntax.tree input w n) := .hyp (Or.inl rfl)
  exact OriginalQuotationValue.at_value hZ input w n q h0 h1

theorem quotationAtValue_kernel_certificate {m} (input : YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree) (w n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (quotationAtValueSentence input w n q)) := TheoryTransport.sentence (source_quotationAtValue input w n q)

theorem native_quotationAtValue {m} (input : YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree) (w n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (quotationAtValueSentence input w n q)) := ZFReplay.replay (quotationAtValue_kernel_certificate input w n q)

def forestReadSentence {m} (children : List (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree)) (j : Fin children.length) (w n i q : Fin m) : Source.Sentence := ((omega w).imp ((OriginalTreeQuotationSyntax.forest children w n).imp ((SyntaxNumeralSyntax.numeral j.val i).imp (((StructuralListFieldSyntax.field w n i q).iff (OriginalTreeQuotationSyntax.tree (children.get j) w q)))))).close

theorem source_forestRead {m} (children : List (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree)) (j : Fin children.length) (w n i q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (forestReadSentence children j w n i q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNumeralSyntax.numeral j.val i) (Context.add (OriginalTreeQuotationSyntax.forest children w n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (OriginalTreeQuotationSyntax.forest children w n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral j.val i) := .hyp (Or.inl rfl)
  exact OriginalQuotationForestRead.field_at hZ children w n j i q h0 h1 h2

theorem forestRead_kernel_certificate {m} (children : List (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree)) (j : Fin children.length) (w n i q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (forestReadSentence children j w n i q)) := TheoryTransport.sentence (source_forestRead children j w n i q)

theorem native_forestRead {m} (children : List (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree)) (j : Fin children.length) (w n i q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (forestReadSentence children j w n i q)) := ZFReplay.replay (forestRead_kernel_certificate children j w n i q)

def forestLengthSentence {m} (children : List (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree)) (w n l : Fin m) : Source.Sentence := ((omega w).imp ((OriginalTreeQuotationSyntax.forest children w n).imp ((SyntaxNumeralSyntax.numeral children.length l).imp ((StructuralListLengthSyntax.hasLength w n l))))).close

theorem source_forestLength {m} (children : List (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree)) (w n l : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (forestLengthSentence children w n l) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNumeralSyntax.numeral children.length l) (Context.add (OriginalTreeQuotationSyntax.forest children w n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (OriginalTreeQuotationSyntax.forest children w n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral children.length l) := .hyp (Or.inl rfl)
  exact OriginalQuotationForestLength.at_numeral hZ children w n l h0 h1 h2

theorem forestLength_kernel_certificate {m} (children : List (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree)) (w n l : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (forestLengthSentence children w n l)) := TheoryTransport.sentence (source_forestLength children w n l)

theorem native_forestLength {m} (children : List (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree)) (w n l : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (forestLengthSentence children w n l)) := ZFReplay.replay (forestLength_kernel_certificate children w n l)

def imageFieldSentence {m} {bound free : PureSyntaxQuotation.Ctx} (values : List (PureSyntaxQuotation.Tm bound free)) (j : Fin values.length) (w L i q : Fin m) : Source.Sentence := ((omega w).imp ((TermImageQuotationSyntax.images values w L).imp ((SyntaxNumeralSyntax.numeral j.val i).imp (((StructuralListFieldSyntax.field w L i q).iff (PureQuotationSyntax.term (values.get j) w q)))))).close

theorem source_imageField {m} {bound free : PureSyntaxQuotation.Ctx} (values : List (PureSyntaxQuotation.Tm bound free)) (j : Fin values.length) (w L i q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (imageFieldSentence values j w L i q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNumeralSyntax.numeral j.val i) (Context.add (TermImageQuotationSyntax.images values w L) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (TermImageQuotationSyntax.images values w L) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral j.val i) := .hyp (Or.inl rfl)
  exact TermImageQuotationFields.field_at hZ values w L j i q h0 h1 h2

theorem imageField_kernel_certificate {m} {bound free : PureSyntaxQuotation.Ctx} (values : List (PureSyntaxQuotation.Tm bound free)) (j : Fin values.length) (w L i q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (imageFieldSentence values j w L i q)) := TheoryTransport.sentence (source_imageField values j w L i q)

theorem native_imageField {m} {bound free : PureSyntaxQuotation.Ctx} (values : List (PureSyntaxQuotation.Tm bound free)) (j : Fin values.length) (w L i q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (imageFieldSentence values j w L i q)) := ZFReplay.replay (imageField_kernel_certificate values j w L i q)

def imageLengthSentence {m} {bound free : PureSyntaxQuotation.Ctx} (values : List (PureSyntaxQuotation.Tm bound free)) (w L a : Fin m) : Source.Sentence := ((omega w).imp ((TermImageQuotationSyntax.images values w L).imp ((SyntaxNumeralSyntax.numeral values.length a).imp ((StructuralListLengthSyntax.hasLength w L a))))).close

theorem source_imageLength {m} {bound free : PureSyntaxQuotation.Ctx} (values : List (PureSyntaxQuotation.Tm bound free)) (w L a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (imageLengthSentence values w L a) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNumeralSyntax.numeral values.length a) (Context.add (TermImageQuotationSyntax.images values w L) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (TermImageQuotationSyntax.images values w L) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral values.length a) := .hyp (Or.inl rfl)
  exact TermImageQuotationFields.length_at hZ values w L a h0 h1 h2

theorem imageLength_kernel_certificate {m} {bound free : PureSyntaxQuotation.Ctx} (values : List (PureSyntaxQuotation.Tm bound free)) (w L a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (imageLengthSentence values w L a)) := TheoryTransport.sentence (source_imageLength values w L a)

theorem native_imageLength {m} {bound free : PureSyntaxQuotation.Ctx} (values : List (PureSyntaxQuotation.Tm bound free)) (w L a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (imageLengthSentence values w L a)) := ZFReplay.replay (imageLength_kernel_certificate values w L a)

def imageRangeSentence {m} {bound free : PureSyntaxQuotation.Ctx} (values : List (PureSyntaxQuotation.Tm bound free)) (w L : Fin m) : Source.Sentence := ((omega w).imp ((TermImageQuotationSyntax.images values w L).imp ((.mem L w)))).close

theorem source_imageRange {m} {bound free : PureSyntaxQuotation.Ctx} (values : List (PureSyntaxQuotation.Tm bound free)) (w L : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (imageRangeSentence values w L) := by
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
  exact TermImageQuotationFields.range hZ values w L h0 h1

theorem imageRange_kernel_certificate {m} {bound free : PureSyntaxQuotation.Ctx} (values : List (PureSyntaxQuotation.Tm bound free)) (w L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (imageRangeSentence values w L)) := TheoryTransport.sentence (source_imageRange values w L)

theorem native_imageRange {m} {bound free : PureSyntaxQuotation.Ctx} (values : List (PureSyntaxQuotation.Tm bound free)) (w L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (imageRangeSentence values w L)) := ZFReplay.replay (imageRange_kernel_certificate values w L)

def imageUniqueSentence {m} {bound free : PureSyntaxQuotation.Ctx} (values : List (PureSyntaxQuotation.Tm bound free)) (w L K : Fin m) : Source.Sentence := ((omega w).imp ((TermImageQuotationSyntax.images values w L).imp ((TermImageQuotationSyntax.images values w K).imp ((.equal L K))))).close

theorem source_imageUnique {m} {bound free : PureSyntaxQuotation.Ctx} (values : List (PureSyntaxQuotation.Tm bound free)) (w L K : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (imageUniqueSentence values w L K) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (TermImageQuotationSyntax.images values w K) (Context.add (TermImageQuotationSyntax.images values w L) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (TermImageQuotationSyntax.images values w L) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (TermImageQuotationSyntax.images values w K) := .hyp (Or.inl rfl)
  exact TermImageQuotationFields.unique hZ values w L K h0 h1 h2

theorem imageUnique_kernel_certificate {m} {bound free : PureSyntaxQuotation.Ctx} (values : List (PureSyntaxQuotation.Tm bound free)) (w L K : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (imageUniqueSentence values w L K)) := TheoryTransport.sentence (source_imageUnique values w L K)

theorem native_imageUnique {m} {bound free : PureSyntaxQuotation.Ctx} (values : List (PureSyntaxQuotation.Tm bound free)) (w L K : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (imageUniqueSentence values w L K)) := ZFReplay.replay (imageUnique_kernel_certificate values w L K)

def imageExistsSentence {m} {bound free : PureSyntaxQuotation.Ctx} (values : List (PureSyntaxQuotation.Tm bound free)) (w : Fin m) : Source.Sentence := ((omega w).imp ((TermImageQuotationSyntax.existsImages values w))).close

theorem source_imageExists {m} {bound free : PureSyntaxQuotation.Ctx} (values : List (PureSyntaxQuotation.Tm bound free)) (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (imageExistsSentence values w) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact TermImageQuotationFields.exists_images hZ values w h0

theorem imageExists_kernel_certificate {m} {bound free : PureSyntaxQuotation.Ctx} (values : List (PureSyntaxQuotation.Tm bound free)) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (imageExistsSentence values w)) := TheoryTransport.sentence (source_imageExists values w)

theorem native_imageExists {m} {bound free : PureSyntaxQuotation.Ctx} (values : List (PureSyntaxQuotation.Tm bound free)) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (imageExistsSentence values w)) := ZFReplay.replay (imageExists_kernel_certificate values w)

def imageTypedFieldsSentence {m} {bound free : PureSyntaxQuotation.Ctx} (values : List (PureSyntaxQuotation.Tm bound free)) (w a c d L : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral values.length a).imp ((SyntaxNumeralSyntax.numeral bound.length c).imp ((SyntaxNumeralSyntax.numeral free.length d).imp ((TermImageQuotationSyntax.images values w L).imp ((SyntaxMixedImageCodeSyntax.typedFields w a c d L))))))).close

theorem source_imageTypedFields {m} {bound free : PureSyntaxQuotation.Ctx} (values : List (PureSyntaxQuotation.Tm bound free)) (w a c d L : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (imageTypedFieldsSentence values w a c d L) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (TermImageQuotationSyntax.images values w L) (Context.add (SyntaxNumeralSyntax.numeral free.length d) (Context.add (SyntaxNumeralSyntax.numeral bound.length c) (Context.add (SyntaxNumeralSyntax.numeral values.length a) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral values.length a) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral bound.length c) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (SyntaxNumeralSyntax.numeral free.length d) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (TermImageQuotationSyntax.images values w L) := .hyp (Or.inl rfl)
  exact TermImageQuotationTyping.typed_fields hZ values w a c d L h0 h1 h2 h3 h4

theorem imageTypedFields_kernel_certificate {m} {bound free : PureSyntaxQuotation.Ctx} (values : List (PureSyntaxQuotation.Tm bound free)) (w a c d L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (imageTypedFieldsSentence values w a c d L)) := TheoryTransport.sentence (source_imageTypedFields values w a c d L)

theorem native_imageTypedFields {m} {bound free : PureSyntaxQuotation.Ctx} (values : List (PureSyntaxQuotation.Tm bound free)) (w a c d L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (imageTypedFieldsSentence values w a c d L)) := ZFReplay.replay (imageTypedFields_kernel_certificate values w a c d L)

def imageTermListSentence {m} {bound free : PureSyntaxQuotation.Ctx} (values : List (PureSyntaxQuotation.Tm bound free)) (w a c d L : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral values.length a).imp ((SyntaxNumeralSyntax.numeral bound.length c).imp ((SyntaxNumeralSyntax.numeral free.length d).imp ((TermImageQuotationSyntax.images values w L).imp ((SyntaxMixedImageCodeSyntax.termList w a c d L))))))).close

theorem source_imageTermList {m} {bound free : PureSyntaxQuotation.Ctx} (values : List (PureSyntaxQuotation.Tm bound free)) (w a c d L : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (imageTermListSentence values w a c d L) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (TermImageQuotationSyntax.images values w L) (Context.add (SyntaxNumeralSyntax.numeral free.length d) (Context.add (SyntaxNumeralSyntax.numeral bound.length c) (Context.add (SyntaxNumeralSyntax.numeral values.length a) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral values.length a) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral bound.length c) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (SyntaxNumeralSyntax.numeral free.length d) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (TermImageQuotationSyntax.images values w L) := .hyp (Or.inl rfl)
  exact TermImageQuotationTyping.term_list hZ values w a c d L h0 h1 h2 h3 h4

theorem imageTermList_kernel_certificate {m} {bound free : PureSyntaxQuotation.Ctx} (values : List (PureSyntaxQuotation.Tm bound free)) (w a c d L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (imageTermListSentence values w a c d L)) := TheoryTransport.sentence (source_imageTermList values w a c d L)

theorem native_imageTermList {m} {bound free : PureSyntaxQuotation.Ctx} (values : List (PureSyntaxQuotation.Tm bound free)) (w a c d L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (imageTermListSentence values w a c d L)) := ZFReplay.replay (imageTermList_kernel_certificate values w a c d L)

def environmentExistsSentence {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (w a b c d : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral bs.length a).imp ((SyntaxNumeralSyntax.numeral fs.length b).imp ((SyntaxNumeralSyntax.numeral bound.length c).imp ((SyntaxNumeralSyntax.numeral free.length d).imp ((TermQuotationEnvironmentSyntax.existsEnvironment bs fs w a b c d))))))).close

theorem source_environmentExists {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (w a b c d : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (environmentExistsSentence bs fs w a b c d) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNumeralSyntax.numeral free.length d) (Context.add (SyntaxNumeralSyntax.numeral bound.length c) (Context.add (SyntaxNumeralSyntax.numeral fs.length b) (Context.add (SyntaxNumeralSyntax.numeral bs.length a) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral bs.length a) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral fs.length b) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (SyntaxNumeralSyntax.numeral bound.length c) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (SyntaxNumeralSyntax.numeral free.length d) := .hyp (Or.inl rfl)
  exact TermQuotationEnvironment.exists_environment hZ bs fs w a b c d h0 h1 h2 h3 h4

theorem environmentExists_kernel_certificate {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (w a b c d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (environmentExistsSentence bs fs w a b c d)) := TheoryTransport.sentence (source_environmentExists bs fs w a b c d)

theorem native_environmentExists {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (w a b c d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (environmentExistsSentence bs fs w a b c d)) := ZFReplay.replay (environmentExists_kernel_certificate bs fs w a b c d)

def environmentFiberSentence {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (w a b c d : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral bs.length a).imp ((SyntaxNumeralSyntax.numeral fs.length b).imp ((SyntaxNumeralSyntax.numeral bound.length c).imp ((SyntaxNumeralSyntax.numeral free.length d).imp ((TermQuotationEnvironmentSyntax.fiber bs fs w a b c d))))))).close

theorem source_environmentFiber {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (w a b c d : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (environmentFiberSentence bs fs w a b c d) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNumeralSyntax.numeral free.length d) (Context.add (SyntaxNumeralSyntax.numeral bound.length c) (Context.add (SyntaxNumeralSyntax.numeral fs.length b) (Context.add (SyntaxNumeralSyntax.numeral bs.length a) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral bs.length a) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral fs.length b) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (SyntaxNumeralSyntax.numeral bound.length c) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (SyntaxNumeralSyntax.numeral free.length d) := .hyp (Or.inl rfl)
  exact TermQuotationEnvironment.actual_fiber hZ bs fs w a b c d h0 h1 h2 h3 h4

theorem environmentFiber_kernel_certificate {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (w a b c d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (environmentFiberSentence bs fs w a b c d)) := TheoryTransport.sentence (source_environmentFiber bs fs w a b c d)

theorem native_environmentFiber {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (w a b c d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (environmentFiberSentence bs fs w a b c d)) := ZFReplay.replay (environmentFiber_kernel_certificate bs fs w a b c d)

def environmentUniqueSentence {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (w a b c d R S U V : Fin m) : Source.Sentence := ((omega w).imp ((TermQuotationEnvironmentSyntax.environment bs fs w a b c d R S).imp ((TermQuotationEnvironmentSyntax.environment bs fs w a b c d U V).imp (((Formula.equal R U).conj (.equal S V)))))).close

theorem source_environmentUnique {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (w a b c d R S U V : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (environmentUniqueSentence bs fs w a b c d R S U V) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (TermQuotationEnvironmentSyntax.environment bs fs w a b c d U V) (Context.add (TermQuotationEnvironmentSyntax.environment bs fs w a b c d R S) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (TermQuotationEnvironmentSyntax.environment bs fs w a b c d R S) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (TermQuotationEnvironmentSyntax.environment bs fs w a b c d U V) := .hyp (Or.inl rfl)
  exact TermQuotationEnvironment.unique hZ bs fs w a b c d R S U V h0 h1 h2

theorem environmentUnique_kernel_certificate {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (w a b c d R S U V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (environmentUniqueSentence bs fs w a b c d R S U V)) := TheoryTransport.sentence (source_environmentUnique bs fs w a b c d R S U V)

theorem native_environmentUnique {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (w a b c d R S U V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (environmentUniqueSentence bs fs w a b c d R S U V)) := ZFReplay.replay (environmentUnique_kernel_certificate bs fs w a b c d R S U V)

def environmentUniqueOutputSentence {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (w a b c d R S : Fin m) : Source.Sentence := ((omega w).imp ((TermQuotationEnvironmentSyntax.environment bs fs w a b c d R S).imp ((TermQuotationEnvironmentSyntax.uniqueEnvironment bs fs w a b c d R S)))).close

theorem source_environmentUniqueOutput {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (w a b c d R S : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (environmentUniqueOutputSentence bs fs w a b c d R S) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (TermQuotationEnvironmentSyntax.environment bs fs w a b c d R S) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (TermQuotationEnvironmentSyntax.environment bs fs w a b c d R S) := .hyp (Or.inl rfl)
  exact TermQuotationEnvironment.unique_output hZ bs fs w a b c d R S h0 h1

theorem environmentUniqueOutput_kernel_certificate {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (w a b c d R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (environmentUniqueOutputSentence bs fs w a b c d R S)) := TheoryTransport.sentence (source_environmentUniqueOutput bs fs w a b c d R S)

theorem native_environmentUniqueOutput {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (w a b c d R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (environmentUniqueOutputSentence bs fs w a b c d R S)) := ZFReplay.replay (environmentUniqueOutput_kernel_certificate bs fs w a b c d R S)

def mixedAtIndexSentence {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (isBound : Bool) (j : Fin (TermQuotationSubstitution.selected isBound bs fs).length) (w a b c d R S n i q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral bs.length a).imp ((SyntaxNumeralSyntax.numeral fs.length b).imp ((TermQuotationEnvironmentSyntax.environment bs fs w a b c d R S).imp ((SyntaxNumeralSyntax.numeral j.val i).imp ((OriginalTreeQuotationSyntax.tree (.node (SyntaxVariableSyntax.tag isBound) [YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.leaf j.val]) w n).imp (((SyntaxCodedMixedTermSyntax.substituted w R S a b c d n q).iff (PureQuotationSyntax.term ((TermQuotationSubstitution.selected isBound bs fs).get j) w q))))))))).close

theorem source_mixedAtIndex {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (isBound : Bool) (j : Fin (TermQuotationSubstitution.selected isBound bs fs).length) (w a b c d R S n i q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (mixedAtIndexSentence bs fs isBound j w a b c d R S n i q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (OriginalTreeQuotationSyntax.tree (.node (SyntaxVariableSyntax.tag isBound) [YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.leaf j.val]) w n) (Context.add (SyntaxNumeralSyntax.numeral j.val i) (Context.add (TermQuotationEnvironmentSyntax.environment bs fs w a b c d R S) (Context.add (SyntaxNumeralSyntax.numeral fs.length b) (Context.add (SyntaxNumeralSyntax.numeral bs.length a) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral bs.length a) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral fs.length b) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (TermQuotationEnvironmentSyntax.environment bs fs w a b c d R S) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (SyntaxNumeralSyntax.numeral j.val i) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (OriginalTreeQuotationSyntax.tree (.node (SyntaxVariableSyntax.tag isBound) [YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.leaf j.val]) w n) := .hyp (Or.inl rfl)
  exact TermQuotationSubstitution.at_index hZ isBound bs fs j w a b c d R S n i q h0 h1 h2 h3 h4 h5

theorem mixedAtIndex_kernel_certificate {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (isBound : Bool) (j : Fin (TermQuotationSubstitution.selected isBound bs fs).length) (w a b c d R S n i q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (mixedAtIndexSentence bs fs isBound j w a b c d R S n i q)) := TheoryTransport.sentence (source_mixedAtIndex bs fs isBound j w a b c d R S n i q)

theorem native_mixedAtIndex {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (isBound : Bool) (j : Fin (TermQuotationSubstitution.selected isBound bs fs).length) (w a b c d R S n i q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (mixedAtIndexSentence bs fs isBound j w a b c d R S n i q)) := ZFReplay.replay (mixedAtIndex_kernel_certificate bs fs isBound j w a b c d R S n i q)

def mixedTermSentence {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (isBound : Bool) (j : Fin (TermQuotationSubstitution.selected isBound bs fs).length) (w a b c d R S n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral bs.length a).imp ((SyntaxNumeralSyntax.numeral fs.length b).imp ((TermQuotationEnvironmentSyntax.environment bs fs w a b c d R S).imp ((OriginalTreeQuotationSyntax.tree (.node (SyntaxVariableSyntax.tag isBound) [YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.leaf j.val]) w n).imp (((SyntaxCodedMixedTermSyntax.substituted w R S a b c d n q).iff (PureQuotationSyntax.term ((TermQuotationSubstitution.selected isBound bs fs).get j) w q)))))))).close

theorem source_mixedTerm {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (isBound : Bool) (j : Fin (TermQuotationSubstitution.selected isBound bs fs).length) (w a b c d R S n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (mixedTermSentence bs fs isBound j w a b c d R S n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (OriginalTreeQuotationSyntax.tree (.node (SyntaxVariableSyntax.tag isBound) [YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.leaf j.val]) w n) (Context.add (TermQuotationEnvironmentSyntax.environment bs fs w a b c d R S) (Context.add (SyntaxNumeralSyntax.numeral fs.length b) (Context.add (SyntaxNumeralSyntax.numeral bs.length a) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral bs.length a) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral fs.length b) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (TermQuotationEnvironmentSyntax.environment bs fs w a b c d R S) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (OriginalTreeQuotationSyntax.tree (.node (SyntaxVariableSyntax.tag isBound) [YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.leaf j.val]) w n) := .hyp (Or.inl rfl)
  exact TermQuotationSubstitution.term_iff hZ isBound bs fs j w a b c d R S n q h0 h1 h2 h3 h4

theorem mixedTerm_kernel_certificate {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (isBound : Bool) (j : Fin (TermQuotationSubstitution.selected isBound bs fs).length) (w a b c d R S n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (mixedTermSentence bs fs isBound j w a b c d R S n q)) := TheoryTransport.sentence (source_mixedTerm bs fs isBound j w a b c d R S n q)

theorem native_mixedTerm {m} {bound free : PureSyntaxQuotation.Ctx} (bs fs : List (PureSyntaxQuotation.Tm bound free)) (isBound : Bool) (j : Fin (TermQuotationSubstitution.selected isBound bs fs).length) (w a b c d R S n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (mixedTermSentence bs fs isBound j w a b c d R S n q)) := ZFReplay.replay (mixedTerm_kernel_certificate bs fs isBound j w a b c d R S n q)

def shiftAtIndexSentence {m} (isBound : Bool) (k bLen fLen : Nat) (_hlt : k < (if isBound then bLen else fLen)) (w U V c d C n q i : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral bLen c).imp ((SyntaxNumeralSyntax.numeral fLen d).imp ((SyntaxFreeShiftSyntax.shiftMap w c C U).imp ((SyntaxIdentityMapSyntax.identityMap w d V).imp ((SyntaxNumeralSyntax.numeral k i).imp ((OriginalTreeQuotationSyntax.tree (.node (SyntaxVariableSyntax.tag isBound) [YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.leaf k]) w n).imp (((SyntaxRenameTermSyntax.renamed w U V c d C d n q).iff (OriginalTreeQuotationSyntax.tree (.node (SyntaxVariableSyntax.tag isBound) [YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.leaf (TermQuotationShiftFields.shiftIndex isBound k)]) w q)))))))))).close

theorem source_shiftAtIndex {m} (isBound : Bool) (k bLen fLen : Nat) (_hlt : k < (if isBound then bLen else fLen)) (w U V c d C n q i : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (shiftAtIndexSentence isBound k bLen fLen _hlt w U V c d C n q i) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (OriginalTreeQuotationSyntax.tree (.node (SyntaxVariableSyntax.tag isBound) [YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.leaf k]) w n) (Context.add (SyntaxNumeralSyntax.numeral k i) (Context.add (SyntaxIdentityMapSyntax.identityMap w d V) (Context.add (SyntaxFreeShiftSyntax.shiftMap w c C U) (Context.add (SyntaxNumeralSyntax.numeral fLen d) (Context.add (SyntaxNumeralSyntax.numeral bLen c) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))
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
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral bLen c) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral fLen d) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h3 : Derives Δ (SyntaxFreeShiftSyntax.shiftMap w c C U) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : Derives Δ (SyntaxIdentityMapSyntax.identityMap w d V) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h5 : Derives Δ (SyntaxNumeralSyntax.numeral k i) := .hyp (Or.inr (Or.inl rfl))
  have h6 : Derives Δ (OriginalTreeQuotationSyntax.tree (.node (SyntaxVariableSyntax.tag isBound) [YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.leaf k]) w n) := .hyp (Or.inl rfl)
  exact TermQuotationShift.at_index_iff hZ isBound k bLen fLen _hlt w U V c d C n q i h0 h1 h2 h3 h4 h5 h6

theorem shiftAtIndex_kernel_certificate {m} (isBound : Bool) (k bLen fLen : Nat) (_hlt : k < (if isBound then bLen else fLen)) (w U V c d C n q i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (shiftAtIndexSentence isBound k bLen fLen _hlt w U V c d C n q i)) := TheoryTransport.sentence (source_shiftAtIndex isBound k bLen fLen _hlt w U V c d C n q i)

theorem native_shiftAtIndex {m} (isBound : Bool) (k bLen fLen : Nat) (_hlt : k < (if isBound then bLen else fLen)) (w U V c d C n q i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (shiftAtIndexSentence isBound k bLen fLen _hlt w U V c d C n q i)) := ZFReplay.replay (shiftAtIndex_kernel_certificate isBound k bLen fLen _hlt w U V c d C n q i)

def shiftVariableSentence {m} (isBound : Bool) (k bLen fLen : Nat) (_hlt : k < (if isBound then bLen else fLen)) (w U V c d C n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral bLen c).imp ((SyntaxNumeralSyntax.numeral fLen d).imp ((SyntaxFreeShiftSyntax.shiftMap w c C U).imp ((SyntaxIdentityMapSyntax.identityMap w d V).imp ((OriginalTreeQuotationSyntax.tree (.node (SyntaxVariableSyntax.tag isBound) [YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.leaf k]) w n).imp (((SyntaxRenameTermSyntax.renamed w U V c d C d n q).iff (OriginalTreeQuotationSyntax.tree (.node (SyntaxVariableSyntax.tag isBound) [YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.leaf (TermQuotationShiftFields.shiftIndex isBound k)]) w q))))))))).close

theorem source_shiftVariable {m} (isBound : Bool) (k bLen fLen : Nat) (_hlt : k < (if isBound then bLen else fLen)) (w U V c d C n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (shiftVariableSentence isBound k bLen fLen _hlt w U V c d C n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (OriginalTreeQuotationSyntax.tree (.node (SyntaxVariableSyntax.tag isBound) [YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.leaf k]) w n) (Context.add (SyntaxIdentityMapSyntax.identityMap w d V) (Context.add (SyntaxFreeShiftSyntax.shiftMap w c C U) (Context.add (SyntaxNumeralSyntax.numeral fLen d) (Context.add (SyntaxNumeralSyntax.numeral bLen c) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral bLen c) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral fLen d) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (SyntaxFreeShiftSyntax.shiftMap w c C U) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (SyntaxIdentityMapSyntax.identityMap w d V) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (OriginalTreeQuotationSyntax.tree (.node (SyntaxVariableSyntax.tag isBound) [YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.leaf k]) w n) := .hyp (Or.inl rfl)
  exact TermQuotationShift.variable_iff hZ isBound k bLen fLen _hlt w U V c d C n q h0 h1 h2 h3 h4 h5

theorem shiftVariable_kernel_certificate {m} (isBound : Bool) (k bLen fLen : Nat) (_hlt : k < (if isBound then bLen else fLen)) (w U V c d C n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (shiftVariableSentence isBound k bLen fLen _hlt w U V c d C n q)) := TheoryTransport.sentence (source_shiftVariable isBound k bLen fLen _hlt w U V c d C n q)

theorem native_shiftVariable {m} (isBound : Bool) (k bLen fLen : Nat) (_hlt : k < (if isBound then bLen else fLen)) (w U V c d C n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (shiftVariableSentence isBound k bLen fLen _hlt w U V c d C n q)) := ZFReplay.replay (shiftVariable_kernel_certificate isBound k bLen fLen _hlt w U V c d C n q)

def shiftTermSentence {m} {bound free : PureSyntaxQuotation.Ctx} {sort : YesMetaZFC.SetTheory.SetSort} (input : PureSyntaxQuotation.Tm bound free sort) (w U V c d C n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral bound.length c).imp ((SyntaxNumeralSyntax.numeral free.length d).imp ((SyntaxFreeShiftSyntax.shiftMap w c C U).imp ((SyntaxIdentityMapSyntax.identityMap w d V).imp ((PureQuotationSyntax.term input w n).imp (((SyntaxRenameTermSyntax.renamed w U V c d C d n q).iff (PureQuotationSyntax.term (input.weakenBound YesMetaZFC.SetTheory.SetSort.set) w q))))))))).close

theorem source_shiftTerm {m} {bound free : PureSyntaxQuotation.Ctx} {sort : YesMetaZFC.SetTheory.SetSort} (input : PureSyntaxQuotation.Tm bound free sort) (w U V c d C n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (shiftTermSentence input w U V c d C n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PureQuotationSyntax.term input w n) (Context.add (SyntaxIdentityMapSyntax.identityMap w d V) (Context.add (SyntaxFreeShiftSyntax.shiftMap w c C U) (Context.add (SyntaxNumeralSyntax.numeral free.length d) (Context.add (SyntaxNumeralSyntax.numeral bound.length c) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral bound.length c) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral free.length d) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (SyntaxFreeShiftSyntax.shiftMap w c C U) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (SyntaxIdentityMapSyntax.identityMap w d V) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (PureQuotationSyntax.term input w n) := .hyp (Or.inl rfl)
  exact TermQuotationShift.term_iff hZ input w U V c d C n q h0 h1 h2 h3 h4 h5

theorem shiftTerm_kernel_certificate {m} {bound free : PureSyntaxQuotation.Ctx} {sort : YesMetaZFC.SetTheory.SetSort} (input : PureSyntaxQuotation.Tm bound free sort) (w U V c d C n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (shiftTermSentence input w U V c d C n q)) := TheoryTransport.sentence (source_shiftTerm input w U V c d C n q)

theorem native_shiftTerm {m} {bound free : PureSyntaxQuotation.Ctx} {sort : YesMetaZFC.SetTheory.SetSort} (input : PureSyntaxQuotation.Tm bound free sort) (w U V c d C n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (shiftTermSentence input w U V c d C n q)) := ZFReplay.replay (shiftTerm_kernel_certificate input w U V c d C n q)

end PPAC.Migration.Internal.ObjectTermImageQuotation
