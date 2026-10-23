import PPAC.Migration.Internal.SyntaxCodedMixedBinderFields

/-! 原数值混合环境、混合项替换与binder提升的原YesMetaZFC核证书。 -/
namespace PPAC.Migration.Internal.ObjectMixedEnvironment
open Source SourceAlgebra SourceLogic OmegaSyntax

def listTypeSentence {m} (w f a c d L : Fin m) : Source.Sentence := ((SyntaxMixedImageCodeSyntax.encoded w f a c d L).imp ((SyntaxMixedImageCodeSyntax.termList w a c d L))).close

theorem source_listType {m} (w f a c d L : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (listTypeSentence w f a c d L) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMixedImageCodeSyntax.encoded w f a c d L) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (SyntaxMixedImageCodeSyntax.encoded w f a c d L) := .hyp (Or.inl rfl)
  exact SyntaxMixedImageCodeFields.term_list w f a c d L h0

theorem listType_kernel_certificate {m} (w f a c d L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (listTypeSentence w f a c d L)) := TheoryTransport.sentence (source_listType w f a c d L)

theorem native_listType {m} (w f a c d L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (listTypeSentence w f a c d L)) := ZFReplay.replay (listType_kernel_certificate w f a c d L)

def fromFieldsSentence {m} (w f a c d L : Fin m) : Source.Sentence := ((SyntaxMixedImageCodeSyntax.termList w a c d L).imp ((StructuralListFieldGraphSyntax.fields w L a f).imp ((SyntaxMixedImageCodeSyntax.encoded w f a c d L)))).close

theorem source_fromFields {m} (w f a c d L : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (fromFieldsSentence w f a c d L) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralListFieldGraphSyntax.fields w L a f) (Context.add (SyntaxMixedImageCodeSyntax.termList w a c d L) (Source.SetLanguage.ZF.at m))
  have h0 : Derives Δ (SyntaxMixedImageCodeSyntax.termList w a c d L) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (StructuralListFieldGraphSyntax.fields w L a f) := .hyp (Or.inl rfl)
  exact SyntaxMixedImageCodeFields.from_fields w f a c d L h0 h1

theorem fromFields_kernel_certificate {m} (w f a c d L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (fromFieldsSentence w f a c d L)) := TheoryTransport.sentence (source_fromFields w f a c d L)

theorem native_fromFields {m} (w f a c d L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (fromFieldsSentence w f a c d L)) := ZFReplay.replay (fromFields_kernel_certificate w f a c d L)

def fieldTypeSentence {m} (w a c d L i q : Fin m) : Source.Sentence := ((SyntaxMixedImageCodeSyntax.termList w a c d L).imp ((Formula.mem i a).imp ((StructuralListFieldSyntax.field w L i q).imp ((SyntaxTermSyntax.term w c d q))))).close

theorem source_fieldType {m} (w a c d L i q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (fieldTypeSentence w a c d L i q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralListFieldSyntax.field w L i q) (Context.add (Formula.mem i a) (Context.add (SyntaxMixedImageCodeSyntax.termList w a c d L) (Source.SetLanguage.ZF.at m)))
  have h0 : Derives Δ (SyntaxMixedImageCodeSyntax.termList w a c d L) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (Formula.mem i a) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (StructuralListFieldSyntax.field w L i q) := .hyp (Or.inl rfl)
  exact SyntaxMixedImageCodeFields.field_type w a c d L i q h0 h1 h2

theorem fieldType_kernel_certificate {m} (w a c d L i q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (fieldTypeSentence w a c d L i q)) := TheoryTransport.sentence (source_fieldType w a c d L i q)

theorem native_fieldType {m} (w a c d L i q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (fieldTypeSentence w a c d L i q)) := ZFReplay.replay (fieldType_kernel_certificate w a c d L i q)

def imageEdgesSentence {m} (w f a c d L i q : Fin m) : Source.Sentence := ((SyntaxMixedImageCodeSyntax.encoded w f a c d L).imp (((GraphSyntax.edge f i q).iff ((Formula.mem i a).conj (StructuralListFieldSyntax.field w L i q))))).close

theorem source_imageEdges {m} (w f a c d L i q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (imageEdgesSentence w f a c d L i q) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMixedImageCodeSyntax.encoded w f a c d L) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (SyntaxMixedImageCodeSyntax.encoded w f a c d L) := .hyp (Or.inl rfl)
  exact SyntaxMixedImageCodeFields.edges w f a c d L i q h0

theorem imageEdges_kernel_certificate {m} (w f a c d L i q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (imageEdgesSentence w f a c d L i q)) := TheoryTransport.sentence (source_imageEdges w f a c d L i q)

theorem native_imageEdges {m} (w f a c d L i q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (imageEdgesSentence w f a c d L i q)) := ZFReplay.replay (imageEdges_kernel_certificate w f a c d L i q)

def codeExistsSentence {m} (w f a c d : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxTermImageSyntax.imageMap w f a c d).imp ((SyntaxMixedImageCodeSyntax.existsCode w f a c d)))).close

theorem source_codeExists {m} (w f a c d : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (codeExistsSentence w f a c d) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTermImageSyntax.imageMap w f a c d) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxTermImageSyntax.imageMap w f a c d) := .hyp (Or.inl rfl)
  exact SyntaxMixedImageCodeExistence.exists_code hZ w f a c d h0 h1

theorem codeExists_kernel_certificate {m} (w f a c d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (codeExistsSentence w f a c d)) := TheoryTransport.sentence (source_codeExists w f a c d)

theorem native_codeExists {m} (w f a c d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (codeExistsSentence w f a c d)) := ZFReplay.replay (codeExists_kernel_certificate w f a c d)

def graphExistsSentence {m} (w a c d L : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMixedImageCodeSyntax.termList w a c d L).imp ((SyntaxMixedImageCodeSyntax.existsGraph w a c d L)))).close

theorem source_graphExists {m} (w a c d L : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (graphExistsSentence w a c d L) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMixedImageCodeSyntax.termList w a c d L) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxMixedImageCodeSyntax.termList w a c d L) := .hyp (Or.inl rfl)
  exact SyntaxMixedImageCodeExistence.exists_graph hZ w a c d L h0 h1

theorem graphExists_kernel_certificate {m} (w a c d L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (graphExistsSentence w a c d L)) := TheoryTransport.sentence (source_graphExists w a c d L)

theorem native_graphExists {m} (w a c d L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (graphExistsSentence w a c d L)) := ZFReplay.replay (graphExists_kernel_certificate w a c d L)

def codeInputIffSentence {m} (w f a c d : Fin m) : Source.Sentence := ((omega w).imp (((SyntaxMixedImageCodeSyntax.existsCode w f a c d).iff (SyntaxTermImageSyntax.imageMap w f a c d)))).close

theorem source_codeInputIff {m} (w f a c d : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (codeInputIffSentence w f a c d) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact SyntaxMixedImageCodeExistence.code_iff_input hZ w f a c d h0

theorem codeInputIff_kernel_certificate {m} (w f a c d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (codeInputIffSentence w f a c d)) := TheoryTransport.sentence (source_codeInputIff w f a c d)

theorem native_codeInputIff {m} (w f a c d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (codeInputIffSentence w f a c d)) := ZFReplay.replay (codeInputIff_kernel_certificate w f a c d)

def graphInputIffSentence {m} (w a c d L : Fin m) : Source.Sentence := ((omega w).imp (((SyntaxMixedImageCodeSyntax.existsGraph w a c d L).iff (SyntaxMixedImageCodeSyntax.termList w a c d L)))).close

theorem source_graphInputIff {m} (w a c d L : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (graphInputIffSentence w a c d L) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact SyntaxMixedImageCodeExistence.graph_iff_input hZ w a c d L h0

theorem graphInputIff_kernel_certificate {m} (w a c d L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (graphInputIffSentence w a c d L)) := TheoryTransport.sentence (source_graphInputIff w a c d L)

theorem native_graphInputIff {m} (w a c d L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (graphInputIffSentence w a c d L)) := ZFReplay.replay (graphInputIff_kernel_certificate w a c d L)

def codeUniqueSentence {m} (w f a c d L M : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMixedImageCodeSyntax.encoded w f a c d L).imp ((SyntaxMixedImageCodeSyntax.encoded w f a c d M).imp ((Formula.equal L M))))).close

theorem source_codeUnique {m} (w f a c d L M : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (codeUniqueSentence w f a c d L M) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMixedImageCodeSyntax.encoded w f a c d M) (Context.add (SyntaxMixedImageCodeSyntax.encoded w f a c d L) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxMixedImageCodeSyntax.encoded w f a c d L) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxMixedImageCodeSyntax.encoded w f a c d M) := .hyp (Or.inl rfl)
  exact SyntaxMixedImageCodeUnique.unique_code hZ w f a c d L M h0 h1 h2

theorem codeUnique_kernel_certificate {m} (w f a c d L M : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (codeUniqueSentence w f a c d L M)) := TheoryTransport.sentence (source_codeUnique w f a c d L M)

theorem native_codeUnique {m} (w f a c d L M : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (codeUniqueSentence w f a c d L M)) := ZFReplay.replay (codeUnique_kernel_certificate w f a c d L M)

def graphUniqueSentence {m} (w f g a c d L : Fin m) : Source.Sentence := ((SyntaxMixedImageCodeSyntax.encoded w f a c d L).imp ((SyntaxMixedImageCodeSyntax.encoded w g a c d L).imp ((Formula.equal f g)))).close

theorem source_graphUnique {m} (w f g a c d L : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (graphUniqueSentence w f g a c d L) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMixedImageCodeSyntax.encoded w g a c d L) (Context.add (SyntaxMixedImageCodeSyntax.encoded w f a c d L) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (SyntaxMixedImageCodeSyntax.encoded w f a c d L) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxMixedImageCodeSyntax.encoded w g a c d L) := .hyp (Or.inl rfl)
  exact SyntaxMixedImageCodeUnique.unique_graph hZ w f g a c d L h0 h1

theorem graphUnique_kernel_certificate {m} (w f g a c d L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (graphUniqueSentence w f g a c d L)) := TheoryTransport.sentence (source_graphUnique w f g a c d L)

theorem native_graphUnique {m} (w f g a c d L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (graphUniqueSentence w f g a c d L)) := ZFReplay.replay (graphUnique_kernel_certificate w f g a c d L)

def atEncodingSentence {m} (w f a c d L : Fin m) : Source.Sentence := ((StructuralListEncodeSyntax.encoding w f a L).imp (((SyntaxMixedImageCodeSyntax.encoded w f a c d L).iff (SyntaxMixedImageCodeSyntax.termList w a c d L)))).close

theorem source_atEncoding {m} (w f a c d L : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (atEncodingSentence w f a c d L) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralListEncodeSyntax.encoding w f a L) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (StructuralListEncodeSyntax.encoding w f a L) := .hyp (Or.inl rfl)
  exact SyntaxMixedImageCodeUnique.encoded_iff_input w f a c d L h0

theorem atEncoding_kernel_certificate {m} (w f a c d L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (atEncodingSentence w f a c d L)) := TheoryTransport.sentence (source_atEncoding w f a c d L)

theorem native_atEncoding {m} (w f a c d L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (atEncodingSentence w f a c d L)) := ZFReplay.replay (atEncoding_kernel_certificate w f a c d L)

def codeFiberSentence {m} (w f a c d : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxTermImageSyntax.imageMap w f a c d).imp ((SyntaxMixedImageCodeSyntax.codeFiber w f a c d)))).close

theorem source_codeFiber {m} (w f a c d : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (codeFiberSentence w f a c d) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTermImageSyntax.imageMap w f a c d) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxTermImageSyntax.imageMap w f a c d) := .hyp (Or.inl rfl)
  exact SyntaxMixedImageCodeFiber.code_fiber hZ w f a c d h0 h1

theorem codeFiber_kernel_certificate {m} (w f a c d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (codeFiberSentence w f a c d)) := TheoryTransport.sentence (source_codeFiber w f a c d)

theorem native_codeFiber {m} (w f a c d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (codeFiberSentence w f a c d)) := ZFReplay.replay (codeFiber_kernel_certificate w f a c d)

def codeFiberIffSentence {m} (w f a c d : Fin m) : Source.Sentence := ((omega w).imp (((SyntaxMixedImageCodeSyntax.codeFiber w f a c d).iff (SyntaxTermImageSyntax.imageMap w f a c d)))).close

theorem source_codeFiberIff {m} (w f a c d : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (codeFiberIffSentence w f a c d) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact SyntaxMixedImageCodeFiber.code_fiber_iff_input hZ w f a c d h0

theorem codeFiberIff_kernel_certificate {m} (w f a c d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (codeFiberIffSentence w f a c d)) := TheoryTransport.sentence (source_codeFiberIff w f a c d)

theorem native_codeFiberIff {m} (w f a c d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (codeFiberIffSentence w f a c d)) := ZFReplay.replay (codeFiberIff_kernel_certificate w f a c d)

def graphFiberSentence {m} (w a c d L : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMixedImageCodeSyntax.termList w a c d L).imp ((SyntaxMixedImageCodeSyntax.graphFiber w a c d L)))).close

theorem source_graphFiber {m} (w a c d L : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (graphFiberSentence w a c d L) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMixedImageCodeSyntax.termList w a c d L) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxMixedImageCodeSyntax.termList w a c d L) := .hyp (Or.inl rfl)
  exact SyntaxMixedImageCodeFiber.graph_fiber hZ w a c d L h0 h1

theorem graphFiber_kernel_certificate {m} (w a c d L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (graphFiberSentence w a c d L)) := TheoryTransport.sentence (source_graphFiber w a c d L)

theorem native_graphFiber {m} (w a c d L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (graphFiberSentence w a c d L)) := ZFReplay.replay (graphFiber_kernel_certificate w a c d L)

def graphFiberIffSentence {m} (w a c d L : Fin m) : Source.Sentence := ((omega w).imp (((SyntaxMixedImageCodeSyntax.graphFiber w a c d L).iff (SyntaxMixedImageCodeSyntax.termList w a c d L)))).close

theorem source_graphFiberIff {m} (w a c d L : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (graphFiberIffSentence w a c d L) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact SyntaxMixedImageCodeFiber.graph_fiber_iff_input hZ w a c d L h0

theorem graphFiberIff_kernel_certificate {m} (w a c d L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (graphFiberIffSentence w a c d L)) := TheoryTransport.sentence (source_graphFiberIff w a c d L)

theorem native_graphFiberIff {m} (w a c d L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (graphFiberIffSentence w a c d L)) := ZFReplay.replay (graphFiberIff_kernel_certificate w a c d L)

def pairCodesSentence {m} (w r s a b c d : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxTermImageSyntax.maps w r s a b c d).imp ((SyntaxMixedImageCodePairs.existsCodes w r s a b c d)))).close

theorem source_pairCodes {m} (w r s a b c d : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (pairCodesSentence w r s a b c d) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTermImageSyntax.maps w r s a b c d) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxTermImageSyntax.maps w r s a b c d) := .hyp (Or.inl rfl)
  exact SyntaxMixedImageCodePairs.exists_codes hZ w r s a b c d h0 h1

theorem pairCodes_kernel_certificate {m} (w r s a b c d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (pairCodesSentence w r s a b c d)) := TheoryTransport.sentence (source_pairCodes w r s a b c d)

theorem native_pairCodes {m} (w r s a b c d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (pairCodesSentence w r s a b c d)) := ZFReplay.replay (pairCodes_kernel_certificate w r s a b c d)

def pairGraphsSentence {m} (w a b c d R S : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMixedImageCodeSyntax.termLists w a b c d R S).imp ((SyntaxMixedImageCodePairs.existsGraphs w a b c d R S)))).close

theorem source_pairGraphs {m} (w a b c d R S : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (pairGraphsSentence w a b c d R S) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMixedImageCodeSyntax.termLists w a b c d R S) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxMixedImageCodeSyntax.termLists w a b c d R S) := .hyp (Or.inl rfl)
  exact SyntaxMixedImageCodePairs.exists_graphs hZ w a b c d R S h0 h1

theorem pairGraphs_kernel_certificate {m} (w a b c d R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (pairGraphsSentence w a b c d R S)) := TheoryTransport.sentence (source_pairGraphs w a b c d R S)

theorem native_pairGraphs {m} (w a b c d R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (pairGraphsSentence w a b c d R S)) := ZFReplay.replay (pairGraphs_kernel_certificate w a b c d R S)

def pairGraphUniqueSentence {m} (w r s a b c d R S u v : Fin m) : Source.Sentence := ((SyntaxMixedImageCodeSyntax.encodings w r s a b c d R S).imp ((SyntaxMixedImageCodeSyntax.encodings w u v a b c d R S).imp (((Formula.equal r u).conj (Formula.equal s v))))).close

theorem source_pairGraphUnique {m} (w r s a b c d R S u v : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (pairGraphUniqueSentence w r s a b c d R S u v) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMixedImageCodeSyntax.encodings w u v a b c d R S) (Context.add (SyntaxMixedImageCodeSyntax.encodings w r s a b c d R S) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (SyntaxMixedImageCodeSyntax.encodings w r s a b c d R S) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxMixedImageCodeSyntax.encodings w u v a b c d R S) := .hyp (Or.inl rfl)
  exact SyntaxMixedImageCodePairs.graphs_unique hZ w r s a b c d R S u v h0 h1

theorem pairGraphUnique_kernel_certificate {m} (w r s a b c d R S u v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (pairGraphUniqueSentence w r s a b c d R S u v)) := TheoryTransport.sentence (source_pairGraphUnique w r s a b c d R S u v)

theorem native_pairGraphUnique {m} (w r s a b c d R S u v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (pairGraphUniqueSentence w r s a b c d R S u v)) := ZFReplay.replay (pairGraphUnique_kernel_certificate w r s a b c d R S u v)

def pairCodeUniqueSentence {m} (w r s a b c d R S U V : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMixedImageCodeSyntax.encodings w r s a b c d R S).imp ((SyntaxMixedImageCodeSyntax.encodings w r s a b c d U V).imp (((Formula.equal R U).conj (Formula.equal S V)))))).close

theorem source_pairCodeUnique {m} (w r s a b c d R S U V : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (pairCodeUniqueSentence w r s a b c d R S U V) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMixedImageCodeSyntax.encodings w r s a b c d U V) (Context.add (SyntaxMixedImageCodeSyntax.encodings w r s a b c d R S) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxMixedImageCodeSyntax.encodings w r s a b c d R S) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxMixedImageCodeSyntax.encodings w r s a b c d U V) := .hyp (Or.inl rfl)
  exact SyntaxMixedImageCodePairs.codes_unique hZ w r s a b c d R S U V h0 h1 h2

theorem pairCodeUnique_kernel_certificate {m} (w r s a b c d R S U V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (pairCodeUniqueSentence w r s a b c d R S U V)) := TheoryTransport.sentence (source_pairCodeUnique w r s a b c d R S U V)

theorem native_pairCodeUnique {m} (w r s a b c d R S U V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (pairCodeUniqueSentence w r s a b c d R S U V)) := ZFReplay.replay (pairCodeUnique_kernel_certificate w r s a b c d R S U V)

def termInputSentence {m} (w R S a b c d n q : Fin m) : Source.Sentence := ((SyntaxCodedMixedTermSyntax.substituted w R S a b c d n q).imp ((SyntaxCodedMixedTermSyntax.input w R S a b c d n))).close

theorem source_termInput {m} (w R S a b c d n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (termInputSentence w R S a b c d n q) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxCodedMixedTermSyntax.substituted w R S a b c d n q) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (SyntaxCodedMixedTermSyntax.substituted w R S a b c d n q) := .hyp (Or.inl rfl)
  exact SyntaxCodedMixedTermTyping.input_of_substituted w R S a b c d n q h0

theorem termInput_kernel_certificate {m} (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (termInputSentence w R S a b c d n q)) := TheoryTransport.sentence (source_termInput w R S a b c d n q)

theorem native_termInput {m} (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (termInputSentence w R S a b c d n q)) := ZFReplay.replay (termInput_kernel_certificate w R S a b c d n q)

def termSourceSentence {m} (w R S a b c d n q : Fin m) : Source.Sentence := ((SyntaxCodedMixedTermSyntax.substituted w R S a b c d n q).imp ((SyntaxTermSyntax.term w a b n))).close

theorem source_termSource {m} (w R S a b c d n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (termSourceSentence w R S a b c d n q) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxCodedMixedTermSyntax.substituted w R S a b c d n q) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (SyntaxCodedMixedTermSyntax.substituted w R S a b c d n q) := .hyp (Or.inl rfl)
  exact SyntaxCodedMixedTermTyping.source_type w R S a b c d n q h0

theorem termSource_kernel_certificate {m} (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (termSourceSentence w R S a b c d n q)) := TheoryTransport.sentence (source_termSource w R S a b c d n q)

theorem native_termSource {m} (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (termSourceSentence w R S a b c d n q)) := ZFReplay.replay (termSource_kernel_certificate w R S a b c d n q)

def termTargetSentence {m} (w R S a b c d n q : Fin m) : Source.Sentence := ((SyntaxCodedMixedTermSyntax.substituted w R S a b c d n q).imp ((SyntaxTermSyntax.term w c d q))).close

theorem source_termTarget {m} (w R S a b c d n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (termTargetSentence w R S a b c d n q) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxCodedMixedTermSyntax.substituted w R S a b c d n q) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (SyntaxCodedMixedTermSyntax.substituted w R S a b c d n q) := .hyp (Or.inl rfl)
  exact SyntaxCodedMixedTermTyping.target_type w R S a b c d n q h0

theorem termTarget_kernel_certificate {m} (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (termTargetSentence w R S a b c d n q)) := TheoryTransport.sentence (source_termTarget w R S a b c d n q)

theorem native_termTarget {m} (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (termTargetSentence w R S a b c d n q)) := ZFReplay.replay (termTarget_kernel_certificate w R S a b c d n q)

def termNaturalSentence {m} (w R S a b c d n q : Fin m) : Source.Sentence := ((SyntaxCodedMixedTermSyntax.substituted w R S a b c d n q).imp ((Formula.mem q w))).close

theorem source_termNatural {m} (w R S a b c d n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (termNaturalSentence w R S a b c d n q) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxCodedMixedTermSyntax.substituted w R S a b c d n q) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (SyntaxCodedMixedTermSyntax.substituted w R S a b c d n q) := .hyp (Or.inl rfl)
  exact SyntaxCodedMixedTermTyping.output_natural w R S a b c d n q h0

theorem termNatural_kernel_certificate {m} (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (termNaturalSentence w R S a b c d n q)) := TheoryTransport.sentence (source_termNatural w R S a b c d n q)

theorem native_termNatural {m} (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (termNaturalSentence w R S a b c d n q)) := ZFReplay.replay (termNatural_kernel_certificate w R S a b c d n q)

def termExistsSentence {m} (w R S a b c d n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxCodedMixedTermSyntax.input w R S a b c d n).imp ((SyntaxCodedMixedTermSyntax.existsOutput w R S a b c d n)))).close

theorem source_termExists {m} (w R S a b c d n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (termExistsSentence w R S a b c d n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxCodedMixedTermSyntax.input w R S a b c d n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxCodedMixedTermSyntax.input w R S a b c d n) := .hyp (Or.inl rfl)
  exact SyntaxCodedMixedTermExistence.exists_output hZ w R S a b c d n h0 h1

theorem termExists_kernel_certificate {m} (w R S a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (termExistsSentence w R S a b c d n)) := TheoryTransport.sentence (source_termExists w R S a b c d n)

theorem native_termExists {m} (w R S a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (termExistsSentence w R S a b c d n)) := ZFReplay.replay (termExists_kernel_certificate w R S a b c d n)

def termAtGraphsSentence {m} (w R S a b c d n q r s : Fin m) : Source.Sentence := ((SyntaxMixedImageCodeSyntax.encodings w r s a b c d R S).imp (((SyntaxCodedMixedTermSyntax.substituted w R S a b c d n q).iff (SyntaxMixedTermSyntax.substituted w r s a b c d n q)))).close

theorem source_termAtGraphs {m} (w R S a b c d n q r s : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (termAtGraphsSentence w R S a b c d n q r s) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMixedImageCodeSyntax.encodings w r s a b c d R S) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (SyntaxMixedImageCodeSyntax.encodings w r s a b c d R S) := .hyp (Or.inl rfl)
  exact SyntaxCodedMixedTermGraphs.at_graphs_iff hZ w R S a b c d n q r s h0

theorem termAtGraphs_kernel_certificate {m} (w R S a b c d n q r s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (termAtGraphsSentence w R S a b c d n q r s)) := TheoryTransport.sentence (source_termAtGraphs w R S a b c d n q r s)

theorem native_termAtGraphs {m} (w R S a b c d n q r s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (termAtGraphsSentence w R S a b c d n q r s)) := ZFReplay.replay (termAtGraphs_kernel_certificate w R S a b c d n q r s)

def termUniqueSentence {m} (w R S a b c d n q v : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxCodedMixedTermSyntax.substituted w R S a b c d n q).imp ((SyntaxCodedMixedTermSyntax.substituted w R S a b c d n v).imp ((Formula.equal q v))))).close

theorem source_termUnique {m} (w R S a b c d n q v : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (termUniqueSentence w R S a b c d n q v) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxCodedMixedTermSyntax.substituted w R S a b c d n v) (Context.add (SyntaxCodedMixedTermSyntax.substituted w R S a b c d n q) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxCodedMixedTermSyntax.substituted w R S a b c d n q) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxCodedMixedTermSyntax.substituted w R S a b c d n v) := .hyp (Or.inl rfl)
  exact SyntaxCodedMixedTermUnique.unique hZ w R S a b c d n q v h0 h1 h2

theorem termUnique_kernel_certificate {m} (w R S a b c d n q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (termUniqueSentence w R S a b c d n q v)) := TheoryTransport.sentence (source_termUnique w R S a b c d n q v)

theorem native_termUnique {m} (w R S a b c d n q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (termUniqueSentence w R S a b c d n q v)) := ZFReplay.replay (termUnique_kernel_certificate w R S a b c d n q v)

def termUniqueOutputSentence {m} (w R S a b c d n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxCodedMixedTermSyntax.substituted w R S a b c d n q).imp ((SyntaxCodedMixedTermSyntax.uniqueOutput w R S a b c d n q)))).close

theorem source_termUniqueOutput {m} (w R S a b c d n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (termUniqueOutputSentence w R S a b c d n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxCodedMixedTermSyntax.substituted w R S a b c d n q) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxCodedMixedTermSyntax.substituted w R S a b c d n q) := .hyp (Or.inl rfl)
  exact SyntaxCodedMixedTermUnique.unique_output hZ w R S a b c d n q h0 h1

theorem termUniqueOutput_kernel_certificate {m} (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (termUniqueOutputSentence w R S a b c d n q)) := TheoryTransport.sentence (source_termUniqueOutput w R S a b c d n q)

theorem native_termUniqueOutput {m} (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (termUniqueOutputSentence w R S a b c d n q)) := ZFReplay.replay (termUniqueOutput_kernel_certificate w R S a b c d n q)

def termFiberSentence {m} (w R S a b c d n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxCodedMixedTermSyntax.input w R S a b c d n).imp ((SyntaxCodedMixedTermSyntax.fiber w R S a b c d n)))).close

theorem source_termFiber {m} (w R S a b c d n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (termFiberSentence w R S a b c d n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxCodedMixedTermSyntax.input w R S a b c d n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxCodedMixedTermSyntax.input w R S a b c d n) := .hyp (Or.inl rfl)
  exact SyntaxCodedMixedTermFiber.actual_fiber hZ w R S a b c d n h0 h1

theorem termFiber_kernel_certificate {m} (w R S a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (termFiberSentence w R S a b c d n)) := TheoryTransport.sentence (source_termFiber w R S a b c d n)

theorem native_termFiber {m} (w R S a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (termFiberSentence w R S a b c d n)) := ZFReplay.replay (termFiber_kernel_certificate w R S a b c d n)

def termExistsIffSentence {m} (w R S a b c d n : Fin m) : Source.Sentence := ((omega w).imp (((SyntaxCodedMixedTermSyntax.existsOutput w R S a b c d n).iff (SyntaxCodedMixedTermSyntax.input w R S a b c d n)))).close

theorem source_termExistsIff {m} (w R S a b c d n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (termExistsIffSentence w R S a b c d n) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact SyntaxCodedMixedTermFiber.exists_iff_input hZ w R S a b c d n h0

theorem termExistsIff_kernel_certificate {m} (w R S a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (termExistsIffSentence w R S a b c d n)) := TheoryTransport.sentence (source_termExistsIff w R S a b c d n)

theorem native_termExistsIff {m} (w R S a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (termExistsIffSentence w R S a b c d n)) := ZFReplay.replay (termExistsIff_kernel_certificate w R S a b c d n)

def termFiberIffSentence {m} (w R S a b c d n : Fin m) : Source.Sentence := ((omega w).imp (((SyntaxCodedMixedTermSyntax.fiber w R S a b c d n).iff (SyntaxCodedMixedTermSyntax.input w R S a b c d n)))).close

theorem source_termFiberIff {m} (w R S a b c d n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (termFiberIffSentence w R S a b c d n) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact SyntaxCodedMixedTermFiber.fiber_iff_input hZ w R S a b c d n h0

theorem termFiberIff_kernel_certificate {m} (w R S a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (termFiberIffSentence w R S a b c d n)) := TheoryTransport.sentence (source_termFiberIff w R S a b c d n)

theorem native_termFiberIff {m} (w R S a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (termFiberIffSentence w R S a b c d n)) := ZFReplay.replay (termFiberIff_kernel_certificate w R S a b c d n)

def termFieldSentence {m} (bound : Bool) (w R S a b c d n q i : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMixedImageCodeSyntax.termLists w a b c d R S).imp ((SyntaxVariableSyntax.code bound w i n).imp (((SyntaxCodedMixedTermSyntax.substituted w R S a b c d n q).iff ((Formula.mem i (SyntaxTermSyntax.limit bound a b)).conj (StructuralListFieldSyntax.field w (SyntaxIndexMapSyntax.selectMap bound R S) i q))))))).close

theorem source_termField {m} (bound : Bool) (w R S a b c d n q i : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (termFieldSentence bound w R S a b c d n q i) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxVariableSyntax.code bound w i n) (Context.add (SyntaxMixedImageCodeSyntax.termLists w a b c d R S) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxMixedImageCodeSyntax.termLists w a b c d R S) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxVariableSyntax.code bound w i n) := .hyp (Or.inl rfl)
  exact SyntaxCodedMixedTermFields.at_field hZ bound w R S a b c d n q i h0 h1 h2

theorem termField_kernel_certificate {m} (bound : Bool) (w R S a b c d n q i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (termFieldSentence bound w R S a b c d n q i)) := TheoryTransport.sentence (source_termField bound w R S a b c d n q i)

theorem native_termField {m} (bound : Bool) (w R S a b c d n q i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (termFieldSentence bound w R S a b c d n q i)) := ZFReplay.replay (termField_kernel_certificate bound w R S a b c d n q i)

def binderExistsSentence {m} (w R S a b c d A C : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxCodedMixedBinderSyntax.input w R S a b c d A C).imp ((SyntaxCodedMixedBinderSyntax.existsPair w R S a b c d A C)))).close

theorem source_binderExists {m} (w R S a b c d A C : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binderExistsSentence w R S a b c d A C) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxCodedMixedBinderSyntax.input w R S a b c d A C) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxCodedMixedBinderSyntax.input w R S a b c d A C) := .hyp (Or.inl rfl)
  exact SyntaxCodedMixedBinderExistence.exists_pair hZ w R S a b c d A C h0 h1

theorem binderExists_kernel_certificate {m} (w R S a b c d A C : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binderExistsSentence w R S a b c d A C)) := TheoryTransport.sentence (source_binderExists w R S a b c d A C)

theorem native_binderExists {m} (w R S a b c d A C : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binderExistsSentence w R S a b c d A C)) := ZFReplay.replay (binderExists_kernel_certificate w R S a b c d A C)

def binderUniqueSentence {m} (w R S a b c d A C K H U V : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H).imp ((SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C U V).imp (((Formula.equal K U).conj (Formula.equal H V)))))).close

theorem source_binderUnique {m} (w R S a b c d A C K H U V : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binderUniqueSentence w R S a b c d A C K H U V) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C U V) (Context.add (SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C U V) := .hyp (Or.inl rfl)
  exact SyntaxCodedMixedBinderUnique.unique_pair hZ w R S a b c d A C K H U V h0 h1 h2

theorem binderUnique_kernel_certificate {m} (w R S a b c d A C K H U V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binderUniqueSentence w R S a b c d A C K H U V)) := TheoryTransport.sentence (source_binderUnique w R S a b c d A C K H U V)

theorem native_binderUnique {m} (w R S a b c d A C K H U V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binderUniqueSentence w R S a b c d A C K H U V)) := ZFReplay.replay (binderUnique_kernel_certificate w R S a b c d A C K H U V)

def binderAtGraphsSentence {m} (w R S a b c d A C K H r s k h : Fin m) : Source.Sentence := ((SyntaxMixedImageCodeSyntax.encodings w r s a b c d R S).imp ((SyntaxMixedImageCodeSyntax.encodings w k h A b C d K H).imp (((SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H).iff (SyntaxMixedImageBinderSyntax.lifted w r s a b c d A C k h))))).close

theorem source_binderAtGraphs {m} (w R S a b c d A C K H r s k h : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binderAtGraphsSentence w R S a b c d A C K H r s k h) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMixedImageCodeSyntax.encodings w k h A b C d K H) (Context.add (SyntaxMixedImageCodeSyntax.encodings w r s a b c d R S) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (SyntaxMixedImageCodeSyntax.encodings w r s a b c d R S) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxMixedImageCodeSyntax.encodings w k h A b C d K H) := .hyp (Or.inl rfl)
  exact SyntaxCodedMixedBinderGraphs.at_graphs_iff hZ w R S a b c d A C K H r s k h h0 h1

theorem binderAtGraphs_kernel_certificate {m} (w R S a b c d A C K H r s k h : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binderAtGraphsSentence w R S a b c d A C K H r s k h)) := TheoryTransport.sentence (source_binderAtGraphs w R S a b c d A C K H r s k h)

theorem native_binderAtGraphs {m} (w R S a b c d A C K H r s k h : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binderAtGraphsSentence w R S a b c d A C K H r s k h)) := ZFReplay.replay (binderAtGraphs_kernel_certificate w R S a b c d A C K H r s k h)

def binderInputListsSentence {m} (w R S a b c d A C K H : Fin m) : Source.Sentence := ((SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H).imp ((SyntaxMixedImageCodeSyntax.termLists w a b c d R S))).close

theorem source_binderInputLists {m} (w R S a b c d A C K H : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binderInputListsSentence w R S a b c d A C K H) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H) := .hyp (Or.inl rfl)
  exact SyntaxCodedMixedBinderTyping.input_lists w R S a b c d A C K H h0

theorem binderInputLists_kernel_certificate {m} (w R S a b c d A C K H : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binderInputListsSentence w R S a b c d A C K H)) := TheoryTransport.sentence (source_binderInputLists w R S a b c d A C K H)

theorem native_binderInputLists {m} (w R S a b c d A C K H : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binderInputListsSentence w R S a b c d A C K H)) := ZFReplay.replay (binderInputLists_kernel_certificate w R S a b c d A C K H)

def binderOutputListsSentence {m} (w R S a b c d A C K H : Fin m) : Source.Sentence := ((SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H).imp ((SyntaxMixedImageCodeSyntax.termLists w A b C d K H))).close

theorem source_binderOutputLists {m} (w R S a b c d A C K H : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binderOutputListsSentence w R S a b c d A C K H) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H) := .hyp (Or.inl rfl)
  exact SyntaxCodedMixedBinderTyping.output_lists w R S a b c d A C K H h0

theorem binderOutputLists_kernel_certificate {m} (w R S a b c d A C K H : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binderOutputListsSentence w R S a b c d A C K H)) := TheoryTransport.sentence (source_binderOutputLists w R S a b c d A C K H)

theorem native_binderOutputLists {m} (w R S a b c d A C K H : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binderOutputListsSentence w R S a b c d A C K H)) := ZFReplay.replay (binderOutputLists_kernel_certificate w R S a b c d A C K H)

def binderInputSentence {m} (w R S a b c d A C K H : Fin m) : Source.Sentence := ((SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H).imp ((SyntaxCodedMixedBinderSyntax.input w R S a b c d A C))).close

theorem source_binderInput {m} (w R S a b c d A C K H : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binderInputSentence w R S a b c d A C K H) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H) := .hyp (Or.inl rfl)
  exact SyntaxCodedMixedBinderTyping.input_of_lifted w R S a b c d A C K H h0

theorem binderInput_kernel_certificate {m} (w R S a b c d A C K H : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binderInputSentence w R S a b c d A C K H)) := TheoryTransport.sentence (source_binderInput w R S a b c d A C K H)

theorem native_binderInput {m} (w R S a b c d A C K H : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binderInputSentence w R S a b c d A C K H)) := ZFReplay.replay (binderInput_kernel_certificate w R S a b c d A C K H)

def binderNaturalSentence {m} (w R S a b c d A C K H : Fin m) : Source.Sentence := ((SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H).imp (((Formula.mem K w).conj (Formula.mem H w)))).close

theorem source_binderNatural {m} (w R S a b c d A C K H : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binderNaturalSentence w R S a b c d A C K H) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H) := .hyp (Or.inl rfl)
  exact SyntaxCodedMixedBinderTyping.output_natural w R S a b c d A C K H h0

theorem binderNatural_kernel_certificate {m} (w R S a b c d A C K H : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binderNaturalSentence w R S a b c d A C K H)) := TheoryTransport.sentence (source_binderNatural w R S a b c d A C K H)

theorem native_binderNatural {m} (w R S a b c d A C K H : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binderNaturalSentence w R S a b c d A C K H)) := ZFReplay.replay (binderNatural_kernel_certificate w R S a b c d A C K H)

def binderUniqueOutputSentence {m} (w R S a b c d A C K H : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H).imp ((SyntaxCodedMixedBinderFiber.uniquePair w R S a b c d A C K H)))).close

theorem source_binderUniqueOutput {m} (w R S a b c d A C K H : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binderUniqueOutputSentence w R S a b c d A C K H) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H) := .hyp (Or.inl rfl)
  exact SyntaxCodedMixedBinderFiber.unique_pair hZ w R S a b c d A C K H h0 h1

theorem binderUniqueOutput_kernel_certificate {m} (w R S a b c d A C K H : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binderUniqueOutputSentence w R S a b c d A C K H)) := TheoryTransport.sentence (source_binderUniqueOutput w R S a b c d A C K H)

theorem native_binderUniqueOutput {m} (w R S a b c d A C K H : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binderUniqueOutputSentence w R S a b c d A C K H)) := ZFReplay.replay (binderUniqueOutput_kernel_certificate w R S a b c d A C K H)

def binderFiberSentence {m} (w R S a b c d A C : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxCodedMixedBinderSyntax.input w R S a b c d A C).imp ((SyntaxCodedMixedBinderFiber.fiber w R S a b c d A C)))).close

theorem source_binderFiber {m} (w R S a b c d A C : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binderFiberSentence w R S a b c d A C) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxCodedMixedBinderSyntax.input w R S a b c d A C) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxCodedMixedBinderSyntax.input w R S a b c d A C) := .hyp (Or.inl rfl)
  exact SyntaxCodedMixedBinderFiber.actual_fiber hZ w R S a b c d A C h0 h1

theorem binderFiber_kernel_certificate {m} (w R S a b c d A C : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binderFiberSentence w R S a b c d A C)) := TheoryTransport.sentence (source_binderFiber w R S a b c d A C)

theorem native_binderFiber {m} (w R S a b c d A C : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binderFiberSentence w R S a b c d A C)) := ZFReplay.replay (binderFiber_kernel_certificate w R S a b c d A C)

def binderExistsIffSentence {m} (w R S a b c d A C : Fin m) : Source.Sentence := ((omega w).imp (((SyntaxCodedMixedBinderSyntax.existsPair w R S a b c d A C).iff (SyntaxCodedMixedBinderSyntax.input w R S a b c d A C)))).close

theorem source_binderExistsIff {m} (w R S a b c d A C : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binderExistsIffSentence w R S a b c d A C) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact SyntaxCodedMixedBinderFiber.exists_iff_input hZ w R S a b c d A C h0

theorem binderExistsIff_kernel_certificate {m} (w R S a b c d A C : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binderExistsIffSentence w R S a b c d A C)) := TheoryTransport.sentence (source_binderExistsIff w R S a b c d A C)

theorem native_binderExistsIff {m} (w R S a b c d A C : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binderExistsIffSentence w R S a b c d A C)) := ZFReplay.replay (binderExistsIff_kernel_certificate w R S a b c d A C)

def binderFiberIffSentence {m} (w R S a b c d A C : Fin m) : Source.Sentence := ((omega w).imp (((SyntaxCodedMixedBinderFiber.fiber w R S a b c d A C).iff (SyntaxCodedMixedBinderSyntax.input w R S a b c d A C)))).close

theorem source_binderFiberIff {m} (w R S a b c d A C : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binderFiberIffSentence w R S a b c d A C) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact SyntaxCodedMixedBinderFiber.fiber_iff_input hZ w R S a b c d A C h0

theorem binderFiberIff_kernel_certificate {m} (w R S a b c d A C : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binderFiberIffSentence w R S a b c d A C)) := TheoryTransport.sentence (source_binderFiberIff w R S a b c d A C)

theorem native_binderFiberIff {m} (w R S a b c d A C : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binderFiberIffSentence w R S a b c d A C)) := ZFReplay.replay (binderFiberIff_kernel_certificate w R S a b c d A C)

def binderZeroSentence {m} (w R S a b c d A C K H U V z n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H).imp ((SyntaxFreeShiftSyntax.shiftMap w c C U).imp ((SyntaxIdentityMapSyntax.identityMap w d V).imp ((SyntaxMixedImageHead.head w C d z n).imp ((((Formula.mem z A).conj (StructuralListFieldSyntax.field w K z q)).iff (Formula.equal q n)))))))).close

theorem source_binderZero {m} (w R S a b c d A C K H U V z n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binderZeroSentence w R S a b c d A C K H U V z n q) := by
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
  exact SyntaxCodedMixedBinderFields.zero_iff hZ w R S a b c d A C K H U V z n q h0 h1 h2 h3 h4

theorem binderZero_kernel_certificate {m} (w R S a b c d A C K H U V z n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binderZeroSentence w R S a b c d A C K H U V z n q)) := TheoryTransport.sentence (source_binderZero w R S a b c d A C K H U V z n q)

theorem native_binderZero {m} (w R S a b c d A C K H U V z n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binderZeroSentence w R S a b c d A C K H U V z n q)) := ZFReplay.replay (binderZero_kernel_certificate w R S a b c d A C K H U V z n q)

def binderBoundSentence {m} (w R S a b c d A C K H U V z n i j t q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H).imp ((SyntaxFreeShiftSyntax.shiftMap w c C U).imp ((SyntaxIdentityMapSyntax.identityMap w d V).imp ((SyntaxMixedImageHead.head w C d z n).imp ((Formula.mem j a).imp ((successor i j).imp ((StructuralListFieldSyntax.field w R j t).imp ((((Formula.mem i A).conj (StructuralListFieldSyntax.field w K i q)).iff (SyntaxRenameTermSyntax.renamed w U V c d C d t q))))))))))).close

theorem source_binderBound {m} (w R S a b c d A C K H U V z n i j t q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binderBoundSentence w R S a b c d A C K H U V z n i j t q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralListFieldSyntax.field w R j t) (Context.add (successor i j) (Context.add (Formula.mem j a) (Context.add (SyntaxMixedImageHead.head w C d z n) (Context.add (SyntaxIdentityMapSyntax.identityMap w d V) (Context.add (SyntaxFreeShiftSyntax.shiftMap w c C U) (Context.add (SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))))
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
  have h1 : Derives Δ (SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h2 : Derives Δ (SyntaxFreeShiftSyntax.shiftMap w c C U) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h3 : Derives Δ (SyntaxIdentityMapSyntax.identityMap w d V) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h4 : Derives Δ (SyntaxMixedImageHead.head w C d z n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h5 : Derives Δ (Formula.mem j a) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h6 : Derives Δ (successor i j) := .hyp (Or.inr (Or.inl rfl))
  have h7 : Derives Δ (StructuralListFieldSyntax.field w R j t) := .hyp (Or.inl rfl)
  exact SyntaxCodedMixedBinderFields.bound_iff hZ w R S a b c d A C K H U V z n i j t q h0 h1 h2 h3 h4 h5 h6 h7

theorem binderBound_kernel_certificate {m} (w R S a b c d A C K H U V z n i j t q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binderBoundSentence w R S a b c d A C K H U V z n i j t q)) := TheoryTransport.sentence (source_binderBound w R S a b c d A C K H U V z n i j t q)

theorem native_binderBound {m} (w R S a b c d A C K H U V z n i j t q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binderBoundSentence w R S a b c d A C K H U V z n i j t q)) := ZFReplay.replay (binderBound_kernel_certificate w R S a b c d A C K H U V z n i j t q)

def binderFreeSentence {m} (w R S a b c d A C K H U V z n j t q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H).imp ((SyntaxFreeShiftSyntax.shiftMap w c C U).imp ((SyntaxIdentityMapSyntax.identityMap w d V).imp ((SyntaxMixedImageHead.head w C d z n).imp ((Formula.mem j b).imp ((StructuralListFieldSyntax.field w S j t).imp ((((Formula.mem j b).conj (StructuralListFieldSyntax.field w H j q)).iff (SyntaxRenameTermSyntax.renamed w U V c d C d t q)))))))))).close

theorem source_binderFree {m} (w R S a b c d A C K H U V z n j t q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binderFreeSentence w R S a b c d A C K H U V z n j t q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralListFieldSyntax.field w S j t) (Context.add (Formula.mem j b) (Context.add (SyntaxMixedImageHead.head w C d z n) (Context.add (SyntaxIdentityMapSyntax.identityMap w d V) (Context.add (SyntaxFreeShiftSyntax.shiftMap w c C U) (Context.add (SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))
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
  have h1 : Derives Δ (SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h2 : Derives Δ (SyntaxFreeShiftSyntax.shiftMap w c C U) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h3 : Derives Δ (SyntaxIdentityMapSyntax.identityMap w d V) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : Derives Δ (SyntaxMixedImageHead.head w C d z n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h5 : Derives Δ (Formula.mem j b) := .hyp (Or.inr (Or.inl rfl))
  have h6 : Derives Δ (StructuralListFieldSyntax.field w S j t) := .hyp (Or.inl rfl)
  exact SyntaxCodedMixedBinderFields.free_iff hZ w R S a b c d A C K H U V z n j t q h0 h1 h2 h3 h4 h5 h6

theorem binderFree_kernel_certificate {m} (w R S a b c d A C K H U V z n j t q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binderFreeSentence w R S a b c d A C K H U V z n j t q)) := TheoryTransport.sentence (source_binderFree w R S a b c d A C K H U V z n j t q)

theorem native_binderFree {m} (w R S a b c d A C K H U V z n j t q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binderFreeSentence w R S a b c d A C K H U V z n j t q)) := ZFReplay.replay (binderFree_kernel_certificate w R S a b c d A C K H U V z n j t q)

end PPAC.Migration.Internal.ObjectMixedEnvironment
