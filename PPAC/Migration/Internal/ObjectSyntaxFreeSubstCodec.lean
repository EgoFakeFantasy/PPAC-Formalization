import PPAC.Migration.Internal.SyntaxFreeSubstFields

/-! 全内部原替换项列表与实际索引码的双向唯一转换及原核证书。 -/
namespace PPAC.Migration.Internal.ObjectSyntaxFreeSubstCodec
open Source SourceAlgebra SourceLogic OmegaSyntax

def openTermSentence {m} (w z c t : Fin m) : Source.Sentence := ((omega w).imp ((empty z).imp ((Formula.mem c w).imp (((SyntaxTermSyntax.term w z c t).iff (SyntaxTermSyntax.branch false w c t)))))).close

theorem source_openTerm {m} (w z c t : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (openTermSentence w z c t) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem c w) (Context.add (empty z) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (empty z) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (Formula.mem c w) := .hyp (Or.inl rfl)
  exact SyntaxOpenTerm.at_zero_iff hZ w z c t h0 h1 h2

theorem openTerm_kernel_certificate {m} (w z c t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (openTermSentence w z c t)) := TheoryTransport.sentence (source_openTerm w z c t)

theorem native_openTerm {m} (w z c t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (openTermSentence w z c t)) := ZFReplay.replay (openTerm_kernel_certificate w z c t)

def decodedTargetSentence {m} (w f a c i j : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxFreeSubstSyntax.termGraph w f a c).imp ((SyntaxFreeSubstSyntax.decodedValue w f i j).imp ((Formula.mem j c))))).close

theorem source_decodedTarget {m} (w f a c i j : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (decodedTargetSentence w f a c i j) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxFreeSubstSyntax.decodedValue w f i j) (Context.add (SyntaxFreeSubstSyntax.termGraph w f a c) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxFreeSubstSyntax.termGraph w f a c) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxFreeSubstSyntax.decodedValue w f i j) := .hyp (Or.inl rfl)
  exact SyntaxFreeSubstPoint.decoded_target hZ w f a c i j h0 h1 h2

theorem decodedTarget_kernel_certificate {m} (w f a c i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (decodedTargetSentence w f a c i j)) := TheoryTransport.sentence (source_decodedTarget w f a c i j)

theorem native_decodedTarget {m} (w f a c i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (decodedTargetSentence w f a c i j)) := ZFReplay.replay (decodedTarget_kernel_certificate w f a c i j)

def encodedNaturalSentence {m} (w r i t : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxFreeSubstSyntax.encodedValue w r i t).imp ((Formula.mem t w)))).close

theorem source_encodedNatural {m} (w r i t : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (encodedNaturalSentence w r i t) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxFreeSubstSyntax.encodedValue w r i t) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxFreeSubstSyntax.encodedValue w r i t) := .hyp (Or.inl rfl)
  exact SyntaxFreeSubstPoint.encoded_natural hZ w r i t h0 h1

theorem encodedNatural_kernel_certificate {m} (w r i t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (encodedNaturalSentence w r i t)) := TheoryTransport.sentence (source_encodedNatural w r i t)

theorem native_encodedNatural {m} (w r i t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (encodedNaturalSentence w r i t)) := ZFReplay.replay (encodedNatural_kernel_certificate w r i t)

def encodedFreeSentence {m} (w r a c i t : Fin m) : Source.Sentence := ((SyntaxIndexMapSyntax.indexMap w r a c).imp ((SyntaxFreeSubstSyntax.encodedValue w r i t).imp ((SyntaxTermSyntax.branch false w c t)))).close

theorem source_encodedFree {m} (w r a c i t : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (encodedFreeSentence w r a c i t) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxFreeSubstSyntax.encodedValue w r i t) (Context.add (SyntaxIndexMapSyntax.indexMap w r a c) (Source.SetLanguage.ZF.at m))
  have h0 : Derives Δ (SyntaxIndexMapSyntax.indexMap w r a c) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxFreeSubstSyntax.encodedValue w r i t) := .hyp (Or.inl rfl)
  exact SyntaxFreeSubstPoint.encoded_free w r a c i t h0 h1

theorem encodedFree_kernel_certificate {m} (w r a c i t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (encodedFreeSentence w r a c i t)) := TheoryTransport.sentence (source_encodedFree w r a c i t)

theorem native_encodedFree {m} (w r a c i t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (encodedFreeSentence w r a c i t)) := ZFReplay.replay (encodedFree_kernel_certificate w r a c i t)

def decodedUniqueSentence {m} (w f a i j k : Fin m) : Source.Sentence := ((omega w).imp ((GraphSyntax.functionOn f a).imp ((SyntaxFreeSubstSyntax.decodedValue w f i j).imp ((SyntaxFreeSubstSyntax.decodedValue w f i k).imp ((Formula.equal j k)))))).close

theorem source_decodedUnique {m} (w f a i j k : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (decodedUniqueSentence w f a i j k) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxFreeSubstSyntax.decodedValue w f i k) (Context.add (SyntaxFreeSubstSyntax.decodedValue w f i j) (Context.add (GraphSyntax.functionOn f a) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (GraphSyntax.functionOn f a) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxFreeSubstSyntax.decodedValue w f i j) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxFreeSubstSyntax.decodedValue w f i k) := .hyp (Or.inl rfl)
  exact SyntaxFreeSubstPoint.decoded_unique hZ w f a i j k h0 h1 h2 h3

theorem decodedUnique_kernel_certificate {m} (w f a i j k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (decodedUniqueSentence w f a i j k)) := TheoryTransport.sentence (source_decodedUnique w f a i j k)

theorem native_decodedUnique {m} (w f a i j k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (decodedUniqueSentence w f a i j k)) := ZFReplay.replay (decodedUnique_kernel_certificate w f a i j k)

def encodedUniqueSentence {m} (w f a i j k : Fin m) : Source.Sentence := ((omega w).imp ((GraphSyntax.functionOn f a).imp ((SyntaxFreeSubstSyntax.encodedValue w f i j).imp ((SyntaxFreeSubstSyntax.encodedValue w f i k).imp ((Formula.equal j k)))))).close

theorem source_encodedUnique {m} (w f a i j k : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (encodedUniqueSentence w f a i j k) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxFreeSubstSyntax.encodedValue w f i k) (Context.add (SyntaxFreeSubstSyntax.encodedValue w f i j) (Context.add (GraphSyntax.functionOn f a) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (GraphSyntax.functionOn f a) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxFreeSubstSyntax.encodedValue w f i j) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxFreeSubstSyntax.encodedValue w f i k) := .hyp (Or.inl rfl)
  exact SyntaxFreeSubstPoint.encoded_unique hZ w f a i j k h0 h1 h2 h3

theorem encodedUnique_kernel_certificate {m} (w f a i j k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (encodedUniqueSentence w f a i j k)) := TheoryTransport.sentence (source_encodedUnique w f a i j k)

theorem native_encodedUnique {m} (w f a i j k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (encodedUniqueSentence w f a i j k)) := ZFReplay.replay (encodedUnique_kernel_certificate w f a i j k)

def decodedIndexSentence {m} (w f a c r : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxFreeSubstSyntax.termGraph w f a c).imp ((SyntaxFreeSubstSyntax.decodedGraph w f a r).imp ((SyntaxIndexMapSyntax.indexMap w r a c))))).close

theorem source_decodedIndex {m} (w f a c r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (decodedIndexSentence w f a c r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxFreeSubstSyntax.decodedGraph w f a r) (Context.add (SyntaxFreeSubstSyntax.termGraph w f a c) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxFreeSubstSyntax.termGraph w f a c) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxFreeSubstSyntax.decodedGraph w f a r) := .hyp (Or.inl rfl)
  exact SyntaxFreeSubstGraph.decoded_index hZ w f a c r h0 h1 h2

theorem decodedIndex_kernel_certificate {m} (w f a c r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (decodedIndexSentence w f a c r)) := TheoryTransport.sentence (source_decodedIndex w f a c r)

theorem native_decodedIndex {m} (w f a c r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (decodedIndexSentence w f a c r)) := ZFReplay.replay (decodedIndex_kernel_certificate w f a c r)

def encodedTermsSentence {m} (w r a c f : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxIndexMapSyntax.indexMap w r a c).imp ((SyntaxFreeSubstSyntax.encodedGraph w r a f).imp ((SyntaxFreeSubstSyntax.termGraph w f a c))))).close

theorem source_encodedTerms {m} (w r a c f : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (encodedTermsSentence w r a c f) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxFreeSubstSyntax.encodedGraph w r a f) (Context.add (SyntaxIndexMapSyntax.indexMap w r a c) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxIndexMapSyntax.indexMap w r a c) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxFreeSubstSyntax.encodedGraph w r a f) := .hyp (Or.inl rfl)
  exact SyntaxFreeSubstGraph.encoded_terms hZ w r a c f h0 h1 h2

theorem encodedTerms_kernel_certificate {m} (w r a c f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (encodedTermsSentence w r a c f)) := TheoryTransport.sentence (source_encodedTerms w r a c f)

theorem native_encodedTerms {m} (w r a c f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (encodedTermsSentence w r a c f)) := ZFReplay.replay (encodedTerms_kernel_certificate w r a c f)

def decodeExistsSentence {m} (w f a c : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxFreeSubstSyntax.termGraph w f a c).imp ((Formula.ex (SyntaxFreeSubstSyntax.conversion w.castSucc f.castSucc a.castSucc c.castSucc (Fin.last m)))))).close

theorem source_decodeExists {m} (w f a c : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (decodeExistsSentence w f a c) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxFreeSubstSyntax.termGraph w f a c) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxFreeSubstSyntax.termGraph w f a c) := .hyp (Or.inl rfl)
  exact SyntaxFreeSubstGraph.decode_exists hZ w f a c h0 h1

theorem decodeExists_kernel_certificate {m} (w f a c : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (decodeExistsSentence w f a c)) := TheoryTransport.sentence (source_decodeExists w f a c)

theorem native_decodeExists {m} (w f a c : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (decodeExistsSentence w f a c)) := ZFReplay.replay (decodeExists_kernel_certificate w f a c)

def encodeExistsSentence {m} (w r a c : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxIndexMapSyntax.indexMap w r a c).imp ((Formula.ex ((SyntaxFreeSubstSyntax.encodedGraph w.castSucc r.castSucc a.castSucc (Fin.last m)).conj (SyntaxFreeSubstSyntax.termGraph w.castSucc (Fin.last m) a.castSucc c.castSucc)))))).close

theorem source_encodeExists {m} (w r a c : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (encodeExistsSentence w r a c) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxIndexMapSyntax.indexMap w r a c) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxIndexMapSyntax.indexMap w r a c) := .hyp (Or.inl rfl)
  exact SyntaxFreeSubstGraph.encode_exists hZ w r a c h0 h1

theorem encodeExists_kernel_certificate {m} (w r a c : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (encodeExistsSentence w r a c)) := TheoryTransport.sentence (source_encodeExists w r a c)

theorem native_encodeExists {m} (w r a c : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (encodeExistsSentence w r a c)) := ZFReplay.replay (encodeExists_kernel_certificate w r a c)

def decodeGraphUniqueSentence {m} (w f a r s : Fin m) : Source.Sentence := ((SyntaxFreeSubstSyntax.decodedGraph w f a r).imp ((SyntaxFreeSubstSyntax.decodedGraph w f a s).imp ((Formula.equal r s)))).close

theorem source_decodeGraphUnique {m} (w f a r s : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (decodeGraphUniqueSentence w f a r s) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxFreeSubstSyntax.decodedGraph w f a s) (Context.add (SyntaxFreeSubstSyntax.decodedGraph w f a r) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (SyntaxFreeSubstSyntax.decodedGraph w f a r) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxFreeSubstSyntax.decodedGraph w f a s) := .hyp (Or.inl rfl)
  exact SyntaxFreeSubstGraph.decode_unique hZ w f a r s h0 h1

theorem decodeGraphUnique_kernel_certificate {m} (w f a r s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (decodeGraphUniqueSentence w f a r s)) := TheoryTransport.sentence (source_decodeGraphUnique w f a r s)

theorem native_decodeGraphUnique {m} (w f a r s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (decodeGraphUniqueSentence w f a r s)) := ZFReplay.replay (decodeGraphUnique_kernel_certificate w f a r s)

def encodeGraphUniqueSentence {m} (w r a f g : Fin m) : Source.Sentence := ((SyntaxFreeSubstSyntax.encodedGraph w r a f).imp ((SyntaxFreeSubstSyntax.encodedGraph w r a g).imp ((Formula.equal f g)))).close

theorem source_encodeGraphUnique {m} (w r a f g : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (encodeGraphUniqueSentence w r a f g) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxFreeSubstSyntax.encodedGraph w r a g) (Context.add (SyntaxFreeSubstSyntax.encodedGraph w r a f) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (SyntaxFreeSubstSyntax.encodedGraph w r a f) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxFreeSubstSyntax.encodedGraph w r a g) := .hyp (Or.inl rfl)
  exact SyntaxFreeSubstGraph.encode_unique hZ w r a f g h0 h1

theorem encodeGraphUnique_kernel_certificate {m} (w r a f g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (encodeGraphUniqueSentence w r a f g)) := TheoryTransport.sentence (source_encodeGraphUnique w r a f g)

theorem native_encodeGraphUnique {m} (w r a f g : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (encodeGraphUniqueSentence w r a f g)) := ZFReplay.replay (encodeGraphUnique_kernel_certificate w r a f g)

def encodedAtCodeSentence {m} (w r a c f i j t : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxIndexMapSyntax.indexMap w r a c).imp ((SyntaxFreeSubstSyntax.encodedGraph w r a f).imp ((SyntaxVariableSyntax.code false w j t).imp (((GraphSyntax.edge f i t).iff (GraphSyntax.edge r i j))))))).close

theorem source_encodedAtCode {m} (w r a c f i j t : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (encodedAtCodeSentence w r a c f i j t) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxVariableSyntax.code false w j t) (Context.add (SyntaxFreeSubstSyntax.encodedGraph w r a f) (Context.add (SyntaxIndexMapSyntax.indexMap w r a c) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxIndexMapSyntax.indexMap w r a c) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxFreeSubstSyntax.encodedGraph w r a f) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxVariableSyntax.code false w j t) := .hyp (Or.inl rfl)
  exact SyntaxFreeSubstBridge.encoded_at_code hZ w r a c f i j t h0 h1 h2 h3

theorem encodedAtCode_kernel_certificate {m} (w r a c f i j t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (encodedAtCodeSentence w r a c f i j t)) := TheoryTransport.sentence (source_encodedAtCode w r a c f i j t)

theorem native_encodedAtCode {m} (w r a c f i j t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (encodedAtCodeSentence w r a c f i j t)) := ZFReplay.replay (encodedAtCode_kernel_certificate w r a c f i j t)

def decodedAtCodeSentence {m} (w f a c r i j t : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxFreeSubstSyntax.termGraph w f a c).imp ((SyntaxFreeSubstSyntax.decodedGraph w f a r).imp ((SyntaxVariableSyntax.code false w j t).imp (((GraphSyntax.edge f i t).iff (GraphSyntax.edge r i j))))))).close

theorem source_decodedAtCode {m} (w f a c r i j t : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (decodedAtCodeSentence w f a c r i j t) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxVariableSyntax.code false w j t) (Context.add (SyntaxFreeSubstSyntax.decodedGraph w f a r) (Context.add (SyntaxFreeSubstSyntax.termGraph w f a c) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxFreeSubstSyntax.termGraph w f a c) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxFreeSubstSyntax.decodedGraph w f a r) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxVariableSyntax.code false w j t) := .hyp (Or.inl rfl)
  exact SyntaxFreeSubstBridge.decoded_at_code hZ w f a c r i j t h0 h1 h2 h3

theorem decodedAtCode_kernel_certificate {m} (w f a c r i j t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (decodedAtCodeSentence w f a c r i j t)) := TheoryTransport.sentence (source_decodedAtCode w f a c r i j t)

theorem native_decodedAtCode {m} (w f a c r i j t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (decodedAtCodeSentence w f a c r i j t)) := ZFReplay.replay (decodedAtCode_kernel_certificate w f a c r i j t)

def encodedToDecodedSentence {m} (w r a c f : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxIndexMapSyntax.indexMap w r a c).imp ((SyntaxFreeSubstSyntax.encodedGraph w r a f).imp ((SyntaxFreeSubstSyntax.decodedGraph w f a r))))).close

theorem source_encodedToDecoded {m} (w r a c f : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (encodedToDecodedSentence w r a c f) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxFreeSubstSyntax.encodedGraph w r a f) (Context.add (SyntaxIndexMapSyntax.indexMap w r a c) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxIndexMapSyntax.indexMap w r a c) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxFreeSubstSyntax.encodedGraph w r a f) := .hyp (Or.inl rfl)
  exact SyntaxFreeSubstRoundTrip.encoded_implies_decoded hZ w r a c f h0 h1 h2

theorem encodedToDecoded_kernel_certificate {m} (w r a c f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (encodedToDecodedSentence w r a c f)) := TheoryTransport.sentence (source_encodedToDecoded w r a c f)

theorem native_encodedToDecoded {m} (w r a c f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (encodedToDecodedSentence w r a c f)) := ZFReplay.replay (encodedToDecoded_kernel_certificate w r a c f)

def decodedToEncodedSentence {m} (w r a c f : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxFreeSubstSyntax.termGraph w f a c).imp ((SyntaxFreeSubstSyntax.decodedGraph w f a r).imp ((SyntaxFreeSubstSyntax.encodedGraph w r a f))))).close

theorem source_decodedToEncoded {m} (w r a c f : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (decodedToEncodedSentence w r a c f) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxFreeSubstSyntax.decodedGraph w f a r) (Context.add (SyntaxFreeSubstSyntax.termGraph w f a c) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxFreeSubstSyntax.termGraph w f a c) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxFreeSubstSyntax.decodedGraph w f a r) := .hyp (Or.inl rfl)
  exact SyntaxFreeSubstRoundTrip.decoded_implies_encoded hZ w r a c f h0 h1 h2

theorem decodedToEncoded_kernel_certificate {m} (w r a c f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (decodedToEncodedSentence w r a c f)) := TheoryTransport.sentence (source_decodedToEncoded w r a c f)

theorem native_decodedToEncoded {m} (w r a c f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (decodedToEncodedSentence w r a c f)) := ZFReplay.replay (decodedToEncoded_kernel_certificate w r a c f)

def indicesUniqueSentence {m} (w f a c r s : Fin m) : Source.Sentence := ((SyntaxFreeSubstSyntax.conversion w f a c r).imp ((SyntaxFreeSubstSyntax.conversion w f a c s).imp ((Formula.equal r s)))).close

theorem source_indicesUnique {m} (w f a c r s : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (indicesUniqueSentence w f a c r s) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxFreeSubstSyntax.conversion w f a c s) (Context.add (SyntaxFreeSubstSyntax.conversion w f a c r) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (SyntaxFreeSubstSyntax.conversion w f a c r) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxFreeSubstSyntax.conversion w f a c s) := .hyp (Or.inl rfl)
  exact SyntaxFreeSubstCode.indices_unique hZ w f a c r s h0 h1

theorem indicesUnique_kernel_certificate {m} (w f a c r s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (indicesUniqueSentence w f a c r s)) := TheoryTransport.sentence (source_indicesUnique w f a c r s)

theorem native_indicesUnique {m} (w f a c r s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (indicesUniqueSentence w f a c r s)) := ZFReplay.replay (indicesUnique_kernel_certificate w f a c r s)

def termsUniqueSentence {m} (w f g a c r : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxFreeSubstSyntax.conversion w f a c r).imp ((SyntaxFreeSubstSyntax.conversion w g a c r).imp ((Formula.equal f g))))).close

theorem source_termsUnique {m} (w f g a c r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (termsUniqueSentence w f g a c r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxFreeSubstSyntax.conversion w g a c r) (Context.add (SyntaxFreeSubstSyntax.conversion w f a c r) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxFreeSubstSyntax.conversion w f a c r) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxFreeSubstSyntax.conversion w g a c r) := .hyp (Or.inl rfl)
  exact SyntaxFreeSubstCode.terms_unique hZ w f g a c r h0 h1 h2

theorem termsUnique_kernel_certificate {m} (w f g a c r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (termsUniqueSentence w f g a c r)) := TheoryTransport.sentence (source_termsUnique w f g a c r)

theorem native_termsUnique {m} (w f g a c r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (termsUniqueSentence w f g a c r)) := ZFReplay.replay (termsUnique_kernel_certificate w f g a c r)

def listProjectionSentence {m} (w a c L S : Fin m) : Source.Sentence := ((SyntaxFreeSubstSyntax.codeConversion w a c L S).imp ((SyntaxFreeSubstSyntax.termList w a c L))).close

theorem source_listProjection {m} (w a c L S : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (listProjectionSentence w a c L S) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxFreeSubstSyntax.codeConversion w a c L S) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (SyntaxFreeSubstSyntax.codeConversion w a c L S) := .hyp (Or.inl rfl)
  exact SyntaxFreeSubstCode.list_of_conversion w a c L S h0

theorem listProjection_kernel_certificate {m} (w a c L S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (listProjectionSentence w a c L S)) := TheoryTransport.sentence (source_listProjection w a c L S)

theorem native_listProjection {m} (w a c L S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (listProjectionSentence w a c L S)) := ZFReplay.replay (listProjection_kernel_certificate w a c L S)

def mapProjectionSentence {m} (w a c L S : Fin m) : Source.Sentence := ((SyntaxFreeSubstSyntax.codeConversion w a c L S).imp ((SyntaxMapCodeSyntax.mapCode w a c S))).close

theorem source_mapProjection {m} (w a c L S : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (mapProjectionSentence w a c L S) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxFreeSubstSyntax.codeConversion w a c L S) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (SyntaxFreeSubstSyntax.codeConversion w a c L S) := .hyp (Or.inl rfl)
  exact SyntaxFreeSubstCode.map_of_conversion w a c L S h0

theorem mapProjection_kernel_certificate {m} (w a c L S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (mapProjectionSentence w a c L S)) := TheoryTransport.sentence (source_mapProjection w a c L S)

theorem native_mapProjection {m} (w a c L S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (mapProjectionSentence w a c L S)) := ZFReplay.replay (mapProjection_kernel_certificate w a c L S)

def fromListSentence {m} (w a c L : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxFreeSubstSyntax.termList w a c L).imp ((SyntaxFreeSubstFiber.mapExists w a c L)))).close

theorem source_fromList {m} (w a c L : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (fromListSentence w a c L) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxFreeSubstSyntax.termList w a c L) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxFreeSubstSyntax.termList w a c L) := .hyp (Or.inl rfl)
  exact SyntaxFreeSubstCode.from_list hZ w a c L h0 h1

theorem fromList_kernel_certificate {m} (w a c L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (fromListSentence w a c L)) := TheoryTransport.sentence (source_fromList w a c L)

theorem native_fromList {m} (w a c L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (fromListSentence w a c L)) := ZFReplay.replay (fromList_kernel_certificate w a c L)

def fromMapSentence {m} (w a c S : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMapCodeSyntax.mapCode w a c S).imp ((SyntaxFreeSubstFiber.listExists w a c S)))).close

theorem source_fromMap {m} (w a c S : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (fromMapSentence w a c S) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMapCodeSyntax.mapCode w a c S) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxMapCodeSyntax.mapCode w a c S) := .hyp (Or.inl rfl)
  exact SyntaxFreeSubstCode.from_map hZ w a c S h0 h1

theorem fromMap_kernel_certificate {m} (w a c S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (fromMapSentence w a c S)) := TheoryTransport.sentence (source_fromMap w a c S)

theorem native_fromMap {m} (w a c S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (fromMapSentence w a c S)) := ZFReplay.replay (fromMap_kernel_certificate w a c S)

def mapUniqueSentence {m} (w a c L S T : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxFreeSubstSyntax.codeConversion w a c L S).imp ((SyntaxFreeSubstSyntax.codeConversion w a c L T).imp ((Formula.equal S T))))).close

theorem source_mapUnique {m} (w a c L S T : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (mapUniqueSentence w a c L S T) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxFreeSubstSyntax.codeConversion w a c L T) (Context.add (SyntaxFreeSubstSyntax.codeConversion w a c L S) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxFreeSubstSyntax.codeConversion w a c L S) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxFreeSubstSyntax.codeConversion w a c L T) := .hyp (Or.inl rfl)
  exact SyntaxFreeSubstCodeUnique.map_unique hZ w a c L S T h0 h1 h2

theorem mapUnique_kernel_certificate {m} (w a c L S T : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (mapUniqueSentence w a c L S T)) := TheoryTransport.sentence (source_mapUnique w a c L S T)

theorem native_mapUnique {m} (w a c L S T : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (mapUniqueSentence w a c L S T)) := ZFReplay.replay (mapUnique_kernel_certificate w a c L S T)

def listUniqueSentence {m} (w a c L M S : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxFreeSubstSyntax.codeConversion w a c L S).imp ((SyntaxFreeSubstSyntax.codeConversion w a c M S).imp ((Formula.equal L M))))).close

theorem source_listUnique {m} (w a c L M S : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (listUniqueSentence w a c L M S) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxFreeSubstSyntax.codeConversion w a c M S) (Context.add (SyntaxFreeSubstSyntax.codeConversion w a c L S) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxFreeSubstSyntax.codeConversion w a c L S) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxFreeSubstSyntax.codeConversion w a c M S) := .hyp (Or.inl rfl)
  exact SyntaxFreeSubstCodeUnique.list_unique hZ w a c L M S h0 h1 h2

theorem listUnique_kernel_certificate {m} (w a c L M S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (listUniqueSentence w a c L M S)) := TheoryTransport.sentence (source_listUnique w a c L M S)

theorem native_listUnique {m} (w a c L M S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (listUniqueSentence w a c L M S)) := ZFReplay.replay (listUnique_kernel_certificate w a c L M S)

def mapFiberSentence {m} (w a c L : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxFreeSubstSyntax.termList w a c L).imp ((SyntaxFreeSubstFiber.mapFiber w a c L)))).close

theorem source_mapFiber {m} (w a c L : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (mapFiberSentence w a c L) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxFreeSubstSyntax.termList w a c L) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxFreeSubstSyntax.termList w a c L) := .hyp (Or.inl rfl)
  exact SyntaxFreeSubstFiber.map_actual_fiber hZ w a c L h0 h1

theorem mapFiber_kernel_certificate {m} (w a c L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (mapFiberSentence w a c L)) := TheoryTransport.sentence (source_mapFiber w a c L)

theorem native_mapFiber {m} (w a c L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (mapFiberSentence w a c L)) := ZFReplay.replay (mapFiber_kernel_certificate w a c L)

def mapExistsIffSentence {m} (w a c L : Fin m) : Source.Sentence := ((omega w).imp (((SyntaxFreeSubstFiber.mapExists w a c L).iff (SyntaxFreeSubstSyntax.termList w a c L)))).close

theorem source_mapExistsIff {m} (w a c L : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (mapExistsIffSentence w a c L) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact SyntaxFreeSubstFiber.map_exists_iff hZ w a c L h0

theorem mapExistsIff_kernel_certificate {m} (w a c L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (mapExistsIffSentence w a c L)) := TheoryTransport.sentence (source_mapExistsIff w a c L)

theorem native_mapExistsIff {m} (w a c L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (mapExistsIffSentence w a c L)) := ZFReplay.replay (mapExistsIff_kernel_certificate w a c L)

def mapFiberIffSentence {m} (w a c L : Fin m) : Source.Sentence := ((omega w).imp (((SyntaxFreeSubstFiber.mapFiber w a c L).iff (SyntaxFreeSubstSyntax.termList w a c L)))).close

theorem source_mapFiberIff {m} (w a c L : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (mapFiberIffSentence w a c L) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact SyntaxFreeSubstFiber.map_fiber_iff hZ w a c L h0

theorem mapFiberIff_kernel_certificate {m} (w a c L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (mapFiberIffSentence w a c L)) := TheoryTransport.sentence (source_mapFiberIff w a c L)

theorem native_mapFiberIff {m} (w a c L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (mapFiberIffSentence w a c L)) := ZFReplay.replay (mapFiberIff_kernel_certificate w a c L)

def listFiberSentence {m} (w a c S : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMapCodeSyntax.mapCode w a c S).imp ((SyntaxFreeSubstFiber.listFiber w a c S)))).close

theorem source_listFiber {m} (w a c S : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (listFiberSentence w a c S) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMapCodeSyntax.mapCode w a c S) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxMapCodeSyntax.mapCode w a c S) := .hyp (Or.inl rfl)
  exact SyntaxFreeSubstFiber.list_actual_fiber hZ w a c S h0 h1

theorem listFiber_kernel_certificate {m} (w a c S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (listFiberSentence w a c S)) := TheoryTransport.sentence (source_listFiber w a c S)

theorem native_listFiber {m} (w a c S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (listFiberSentence w a c S)) := ZFReplay.replay (listFiber_kernel_certificate w a c S)

def listExistsIffSentence {m} (w a c S : Fin m) : Source.Sentence := ((omega w).imp (((SyntaxFreeSubstFiber.listExists w a c S).iff (SyntaxMapCodeSyntax.mapCode w a c S)))).close

theorem source_listExistsIff {m} (w a c S : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (listExistsIffSentence w a c S) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact SyntaxFreeSubstFiber.list_exists_iff hZ w a c S h0

theorem listExistsIff_kernel_certificate {m} (w a c S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (listExistsIffSentence w a c S)) := TheoryTransport.sentence (source_listExistsIff w a c S)

theorem native_listExistsIff {m} (w a c S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (listExistsIffSentence w a c S)) := ZFReplay.replay (listExistsIff_kernel_certificate w a c S)

def listFiberIffSentence {m} (w a c S : Fin m) : Source.Sentence := ((omega w).imp (((SyntaxFreeSubstFiber.listFiber w a c S).iff (SyntaxMapCodeSyntax.mapCode w a c S)))).close

theorem source_listFiberIff {m} (w a c S : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (listFiberIffSentence w a c S) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact SyntaxFreeSubstFiber.list_fiber_iff hZ w a c S h0

theorem listFiberIff_kernel_certificate {m} (w a c S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (listFiberIffSentence w a c S)) := TheoryTransport.sentence (source_listFiberIff w a c S)

theorem native_listFiberIff {m} (w a c S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (listFiberIffSentence w a c S)) := ZFReplay.replay (listFiberIff_kernel_certificate w a c S)

def atGraphSentence {m} (w a c L S r : Fin m) : Source.Sentence := ((SyntaxFreeSubstSyntax.codeConversion w a c L S).imp ((SyntaxMapCodeSyntax.encoded w r a c S).imp ((Formula.ex ((StructuralListEncodeSyntax.encoding w.castSucc (Fin.last m) a.castSucc L.castSucc).conj (SyntaxFreeSubstSyntax.conversion w.castSucc (Fin.last m) a.castSucc c.castSucc r.castSucc)))))).close

theorem source_atGraph {m} (w a c L S r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (atGraphSentence w a c L S r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMapCodeSyntax.encoded w r a c S) (Context.add (SyntaxFreeSubstSyntax.codeConversion w a c L S) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (SyntaxFreeSubstSyntax.codeConversion w a c L S) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxMapCodeSyntax.encoded w r a c S) := .hyp (Or.inl rfl)
  exact SyntaxFreeSubstFields.at_graph hZ w a c L S r h0 h1

theorem atGraph_kernel_certificate {m} (w a c L S r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (atGraphSentence w a c L S r)) := TheoryTransport.sentence (source_atGraph w a c L S r)

theorem native_atGraph {m} (w a c L S r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (atGraphSentence w a c L S r)) := ZFReplay.replay (atGraph_kernel_certificate w a c L S r)

def fieldAtCodeSentence {m} (w a c L S r i j t : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxFreeSubstSyntax.codeConversion w a c L S).imp ((SyntaxMapCodeSyntax.encoded w r a c S).imp ((SyntaxVariableSyntax.code false w j t).imp (((GraphSyntax.edge r i j).iff ((Formula.mem i a).conj (StructuralListFieldSyntax.field w L i t)))))))).close

theorem source_fieldAtCode {m} (w a c L S r i j t : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (fieldAtCodeSentence w a c L S r i j t) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxVariableSyntax.code false w j t) (Context.add (SyntaxMapCodeSyntax.encoded w r a c S) (Context.add (SyntaxFreeSubstSyntax.codeConversion w a c L S) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxFreeSubstSyntax.codeConversion w a c L S) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxMapCodeSyntax.encoded w r a c S) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxVariableSyntax.code false w j t) := .hyp (Or.inl rfl)
  exact SyntaxFreeSubstFields.field_at_code hZ w a c L S r i j t h0 h1 h2 h3

theorem fieldAtCode_kernel_certificate {m} (w a c L S r i j t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (fieldAtCodeSentence w a c L S r i j t)) := TheoryTransport.sentence (source_fieldAtCode w a c L S r i j t)

theorem native_fieldAtCode {m} (w a c L S r i j t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (fieldAtCodeSentence w a c L S r i j t)) := ZFReplay.replay (fieldAtCode_kernel_certificate w a c L S r i j t)

def fieldIsFreeSentence {m} (w a c L i t : Fin m) : Source.Sentence := ((SyntaxFreeSubstSyntax.termList w a c L).imp ((Formula.mem i a).imp ((StructuralListFieldSyntax.field w L i t).imp ((SyntaxTermSyntax.branch false w c t))))).close

theorem source_fieldIsFree {m} (w a c L i t : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (fieldIsFreeSentence w a c L i t) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralListFieldSyntax.field w L i t) (Context.add (Formula.mem i a) (Context.add (SyntaxFreeSubstSyntax.termList w a c L) (Source.SetLanguage.ZF.at m)))
  have h0 : Derives Δ (SyntaxFreeSubstSyntax.termList w a c L) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (Formula.mem i a) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (StructuralListFieldSyntax.field w L i t) := .hyp (Or.inl rfl)
  exact SyntaxFreeSubstFields.field_is_free w a c L i t h0 h1 h2

theorem fieldIsFree_kernel_certificate {m} (w a c L i t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (fieldIsFreeSentence w a c L i t)) := TheoryTransport.sentence (source_fieldIsFree w a c L i t)

theorem native_fieldIsFree {m} (w a c L i t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (fieldIsFreeSentence w a c L i t)) := ZFReplay.replay (fieldIsFree_kernel_certificate w a c L i t)

end PPAC.Migration.Internal.ObjectSyntaxFreeSubstCodec
