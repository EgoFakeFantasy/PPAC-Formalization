import PPAC.Migration.Internal.SyntaxTermImageBoundShift

/-! 混合项替换、实际项像表逐值变换及原YesMetaZFC核证书。 -/
namespace PPAC.Migration.Internal.ObjectMixedTerm
open Source SourceAlgebra SourceLogic OmegaSyntax

def inputSentence {m} (w r s a b c d n q : Fin m) : Source.Sentence := ((SyntaxMixedTermSyntax.substituted w r s a b c d n q).imp ((SyntaxMixedTermSyntax.input w r s a b c d n))).close

theorem source_input {m} (w r s a b c d n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (inputSentence w r s a b c d n q) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMixedTermSyntax.substituted w r s a b c d n q) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (SyntaxMixedTermSyntax.substituted w r s a b c d n q) := .hyp (Or.inl rfl)
  exact SyntaxMixedTermTyping.input_of_substituted w r s a b c d n q h0

theorem input_kernel_certificate {m} (w r s a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (inputSentence w r s a b c d n q)) := TheoryTransport.sentence (source_input w r s a b c d n q)

theorem native_input {m} (w r s a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (inputSentence w r s a b c d n q)) := ZFReplay.replay (input_kernel_certificate w r s a b c d n q)

def sourceTypeSentence {m} (w r s a b c d n q : Fin m) : Source.Sentence := ((SyntaxMixedTermSyntax.substituted w r s a b c d n q).imp ((SyntaxTermSyntax.term w a b n))).close

theorem source_sourceType {m} (w r s a b c d n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (sourceTypeSentence w r s a b c d n q) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMixedTermSyntax.substituted w r s a b c d n q) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (SyntaxMixedTermSyntax.substituted w r s a b c d n q) := .hyp (Or.inl rfl)
  exact SyntaxMixedTermTyping.source_type w r s a b c d n q h0

theorem sourceType_kernel_certificate {m} (w r s a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (sourceTypeSentence w r s a b c d n q)) := TheoryTransport.sentence (source_sourceType w r s a b c d n q)

theorem native_sourceType {m} (w r s a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (sourceTypeSentence w r s a b c d n q)) := ZFReplay.replay (sourceType_kernel_certificate w r s a b c d n q)

def targetTypeSentence {m} (w r s a b c d n q : Fin m) : Source.Sentence := ((SyntaxMixedTermSyntax.substituted w r s a b c d n q).imp ((SyntaxTermSyntax.term w c d q))).close

theorem source_targetType {m} (w r s a b c d n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (targetTypeSentence w r s a b c d n q) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMixedTermSyntax.substituted w r s a b c d n q) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (SyntaxMixedTermSyntax.substituted w r s a b c d n q) := .hyp (Or.inl rfl)
  exact SyntaxMixedTermTyping.target_type w r s a b c d n q h0

theorem targetType_kernel_certificate {m} (w r s a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (targetTypeSentence w r s a b c d n q)) := TheoryTransport.sentence (source_targetType w r s a b c d n q)

theorem native_targetType {m} (w r s a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (targetTypeSentence w r s a b c d n q)) := ZFReplay.replay (targetType_kernel_certificate w r s a b c d n q)

def outputNaturalSentence {m} (w r s a b c d n q : Fin m) : Source.Sentence := ((SyntaxMixedTermSyntax.substituted w r s a b c d n q).imp ((Formula.mem q w))).close

theorem source_outputNatural {m} (w r s a b c d n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (outputNaturalSentence w r s a b c d n q) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMixedTermSyntax.substituted w r s a b c d n q) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (SyntaxMixedTermSyntax.substituted w r s a b c d n q) := .hyp (Or.inl rfl)
  exact SyntaxMixedTermTyping.output_natural w r s a b c d n q h0

theorem outputNatural_kernel_certificate {m} (w r s a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (outputNaturalSentence w r s a b c d n q)) := TheoryTransport.sentence (source_outputNatural w r s a b c d n q)

theorem native_outputNatural {m} (w r s a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (outputNaturalSentence w r s a b c d n q)) := ZFReplay.replay (outputNatural_kernel_certificate w r s a b c d n q)

def existsOutputSentence {m} (w r s a b c d n : Fin m) : Source.Sentence := ((SyntaxMixedTermSyntax.input w r s a b c d n).imp ((SyntaxMixedTermSyntax.existsOutput w r s a b c d n))).close

theorem source_existsOutput {m} (w r s a b c d n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (existsOutputSentence w r s a b c d n) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMixedTermSyntax.input w r s a b c d n) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (SyntaxMixedTermSyntax.input w r s a b c d n) := .hyp (Or.inl rfl)
  exact SyntaxMixedTermExistence.exists_output w r s a b c d n h0

theorem existsOutput_kernel_certificate {m} (w r s a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (existsOutputSentence w r s a b c d n)) := TheoryTransport.sentence (source_existsOutput w r s a b c d n)

theorem native_existsOutput {m} (w r s a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (existsOutputSentence w r s a b c d n)) := ZFReplay.replay (existsOutput_kernel_certificate w r s a b c d n)

def outputUniqueSentence {m} (w r s a b c d n q v : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMixedTermSyntax.substituted w r s a b c d n q).imp ((SyntaxMixedTermSyntax.substituted w r s a b c d n v).imp ((Formula.equal q v))))).close

theorem source_outputUnique {m} (w r s a b c d n q v : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (outputUniqueSentence w r s a b c d n q v) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMixedTermSyntax.substituted w r s a b c d n v) (Context.add (SyntaxMixedTermSyntax.substituted w r s a b c d n q) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxMixedTermSyntax.substituted w r s a b c d n q) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxMixedTermSyntax.substituted w r s a b c d n v) := .hyp (Or.inl rfl)
  exact SyntaxMixedTermUnique.unique hZ w r s a b c d n q v h0 h1 h2

theorem outputUnique_kernel_certificate {m} (w r s a b c d n q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (outputUniqueSentence w r s a b c d n q v)) := TheoryTransport.sentence (source_outputUnique w r s a b c d n q v)

theorem native_outputUnique {m} (w r s a b c d n q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (outputUniqueSentence w r s a b c d n q v)) := ZFReplay.replay (outputUnique_kernel_certificate w r s a b c d n q v)

def uniqueOutputSentence {m} (w r s a b c d n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMixedTermSyntax.substituted w r s a b c d n q).imp ((SyntaxMixedTermSyntax.uniqueOutput w r s a b c d n q)))).close

theorem source_uniqueOutput {m} (w r s a b c d n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (uniqueOutputSentence w r s a b c d n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMixedTermSyntax.substituted w r s a b c d n q) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxMixedTermSyntax.substituted w r s a b c d n q) := .hyp (Or.inl rfl)
  exact SyntaxMixedTermUnique.unique_output hZ w r s a b c d n q h0 h1

theorem uniqueOutput_kernel_certificate {m} (w r s a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (uniqueOutputSentence w r s a b c d n q)) := TheoryTransport.sentence (source_uniqueOutput w r s a b c d n q)

theorem native_uniqueOutput {m} (w r s a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (uniqueOutputSentence w r s a b c d n q)) := ZFReplay.replay (uniqueOutput_kernel_certificate w r s a b c d n q)

def actualFiberSentence {m} (w r s a b c d n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMixedTermSyntax.input w r s a b c d n).imp ((SyntaxMixedTermSyntax.fiber w r s a b c d n)))).close

theorem source_actualFiber {m} (w r s a b c d n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (actualFiberSentence w r s a b c d n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMixedTermSyntax.input w r s a b c d n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxMixedTermSyntax.input w r s a b c d n) := .hyp (Or.inl rfl)
  exact SyntaxMixedTermUnique.actual_fiber hZ w r s a b c d n h0 h1

theorem actualFiber_kernel_certificate {m} (w r s a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (actualFiberSentence w r s a b c d n)) := TheoryTransport.sentence (source_actualFiber w r s a b c d n)

theorem native_actualFiber {m} (w r s a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (actualFiberSentence w r s a b c d n)) := ZFReplay.replay (actualFiber_kernel_certificate w r s a b c d n)

def existsInputIffSentence {m} (w r s a b c d n : Fin m) : Source.Sentence := (((SyntaxMixedTermSyntax.existsOutput w r s a b c d n).iff (SyntaxMixedTermSyntax.input w r s a b c d n))).close

theorem source_existsInputIff {m} (w r s a b c d n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (existsInputIffSentence w r s a b c d n) := by
  apply close_derives
  let Δ : Context m := Source.SetLanguage.ZF.at m
  exact SyntaxMixedTermUnique.exists_iff_input w r s a b c d n

theorem existsInputIff_kernel_certificate {m} (w r s a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (existsInputIffSentence w r s a b c d n)) := TheoryTransport.sentence (source_existsInputIff w r s a b c d n)

theorem native_existsInputIff {m} (w r s a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (existsInputIffSentence w r s a b c d n)) := ZFReplay.replay (existsInputIff_kernel_certificate w r s a b c d n)

def fiberInputIffSentence {m} (w r s a b c d n : Fin m) : Source.Sentence := ((omega w).imp (((SyntaxMixedTermSyntax.fiber w r s a b c d n).iff (SyntaxMixedTermSyntax.input w r s a b c d n)))).close

theorem source_fiberInputIff {m} (w r s a b c d n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (fiberInputIffSentence w r s a b c d n) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact SyntaxMixedTermUnique.fiber_iff_input hZ w r s a b c d n h0

theorem fiberInputIff_kernel_certificate {m} (w r s a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (fiberInputIffSentence w r s a b c d n)) := TheoryTransport.sentence (source_fiberInputIff w r s a b c d n)

theorem native_fiberInputIff {m} (w r s a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (fiberInputIffSentence w r s a b c d n)) := ZFReplay.replay (fiberInputIff_kernel_certificate w r s a b c d n)

def atCodeSentence {m} (bound : Bool) (w r s a b c d n q i : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxTermImageSyntax.maps w r s a b c d).imp ((SyntaxVariableSyntax.code bound w i n).imp (((SyntaxMixedTermSyntax.substituted w r s a b c d n q).iff ((Formula.mem i (SyntaxTermSyntax.limit bound a b)).conj (GraphSyntax.edge (SyntaxIndexMapSyntax.selectMap bound r s) i q))))))).close

theorem source_atCode {m} (bound : Bool) (w r s a b c d n q i : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (atCodeSentence bound w r s a b c d n q i) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxVariableSyntax.code bound w i n) (Context.add (SyntaxTermImageSyntax.maps w r s a b c d) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxTermImageSyntax.maps w r s a b c d) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxVariableSyntax.code bound w i n) := .hyp (Or.inl rfl)
  exact SyntaxMixedTermKnown.at_code hZ bound w r s a b c d n q i h0 h1 h2

theorem atCode_kernel_certificate {m} (bound : Bool) (w r s a b c d n q i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (atCodeSentence bound w r s a b c d n q i)) := TheoryTransport.sentence (source_atCode bound w r s a b c d n q i)

theorem native_atCode {m} (bound : Bool) (w r s a b c d n q i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (atCodeSentence bound w r s a b c d n q i)) := ZFReplay.replay (atCode_kernel_certificate bound w r s a b c d n q i)

def imageGraphExistsSentence {m} {p} (P : Formula (p+2)) (ρ : Fin p → Fin m) (w a c d : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem a w).imp ((SyntaxTermSyntax.contexts w c d).imp ((ReplacementPredicates.total P ρ a).imp ((SyntaxTermImageGraph.outputsTyped P ρ w a c d).imp ((.ex ((SyntaxTermImageSyntax.imageMap w.castSucc (Fin.last m) a.castSucc c.castSucc d.castSucc).conj (RelationGraphSyntax.functionGraph P (ReplacementPredicates.paramsUp ρ) a.castSucc (Fin.last m)))))))))).close

theorem source_imageGraphExists {m} {p} (P : Formula (p+2)) (ρ : Fin p → Fin m) (w a c d : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (imageGraphExistsSentence P ρ w a c d) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTermImageGraph.outputsTyped P ρ w a c d) (Context.add (ReplacementPredicates.total P ρ a) (Context.add (SyntaxTermSyntax.contexts w c d) (Context.add (Formula.mem a w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (Formula.mem a w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (SyntaxTermSyntax.contexts w c d) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (ReplacementPredicates.total P ρ a) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (SyntaxTermImageGraph.outputsTyped P ρ w a c d) := .hyp (Or.inl rfl)
  exact SyntaxTermImageGraph.exists_image hZ P ρ w a c d h0 h1 h2 h3 h4

theorem imageGraphExists_kernel_certificate {m} {p} (P : Formula (p+2)) (ρ : Fin p → Fin m) (w a c d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (imageGraphExistsSentence P ρ w a c d)) := TheoryTransport.sentence (source_imageGraphExists P ρ w a c d)

theorem native_imageGraphExists {m} {p} (P : Formula (p+2)) (ρ : Fin p → Fin m) (w a c d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (imageGraphExistsSentence P ρ w a c d)) := ZFReplay.replay (imageGraphExists_kernel_certificate P ρ w a c d)

def pushExistsSentence {m} (w R S c d C D f a : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxTermImageSyntax.imageMap w f a c d).imp ((SyntaxIndexMapSyntax.maps w R S c d C D).imp ((SyntaxTermImagePushSyntax.existsPush w R S c d C D f a))))).close

theorem source_pushExists {m} (w R S c d C D f a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (pushExistsSentence w R S c d C D f a) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxIndexMapSyntax.maps w R S c d C D) (Context.add (SyntaxTermImageSyntax.imageMap w f a c d) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxTermImageSyntax.imageMap w f a c d) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxIndexMapSyntax.maps w R S c d C D) := .hyp (Or.inl rfl)
  exact SyntaxTermImagePushGraph.exists_push hZ w R S c d C D f a h0 h1 h2

theorem pushExists_kernel_certificate {m} (w R S c d C D f a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (pushExistsSentence w R S c d C D f a)) := TheoryTransport.sentence (source_pushExists w R S c d C D f a)

theorem native_pushExists {m} (w R S c d C D f a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (pushExistsSentence w R S c d C D f a)) := ZFReplay.replay (pushExists_kernel_certificate w R S c d C D f a)

def pushUniqueSentence {m} (w R S c d C D f a g h : Fin m) : Source.Sentence := ((SyntaxTermImagePushSyntax.pushed w R S c d C D f a g).imp ((SyntaxTermImagePushSyntax.pushed w R S c d C D f a h).imp ((Formula.equal g h)))).close

theorem source_pushUnique {m} (w R S c d C D f a g h : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (pushUniqueSentence w R S c d C D f a g h) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTermImagePushSyntax.pushed w R S c d C D f a h) (Context.add (SyntaxTermImagePushSyntax.pushed w R S c d C D f a g) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (SyntaxTermImagePushSyntax.pushed w R S c d C D f a g) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxTermImagePushSyntax.pushed w R S c d C D f a h) := .hyp (Or.inl rfl)
  exact SyntaxTermImagePushGraph.unique hZ w R S c d C D f a g h h0 h1

theorem pushUnique_kernel_certificate {m} (w R S c d C D f a g h : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (pushUniqueSentence w R S c d C D f a g h)) := TheoryTransport.sentence (source_pushUnique w R S c d C D f a g h)

theorem native_pushUnique {m} (w R S c d C D f a g h : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (pushUniqueSentence w R S c d C D f a g h)) := ZFReplay.replay (pushUnique_kernel_certificate w R S c d C D f a g h)

def pushGuardedEdgesSentence {m} (w R S c d C D f a g i q : Fin m) : Source.Sentence := ((SyntaxTermImagePushSyntax.pushed w R S c d C D f a g).imp (((GraphSyntax.edge g i q).iff ((Formula.mem i a).conj (SyntaxTermImagePushSyntax.value w R S c d C D f i q))))).close

theorem source_pushGuardedEdges {m} (w R S c d C D f a g i q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (pushGuardedEdgesSentence w R S c d C D f a g i q) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTermImagePushSyntax.pushed w R S c d C D f a g) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (SyntaxTermImagePushSyntax.pushed w R S c d C D f a g) := .hyp (Or.inl rfl)
  exact SyntaxTermImagePushGraph.guarded_edges w R S c d C D f a g i q h0

theorem pushGuardedEdges_kernel_certificate {m} (w R S c d C D f a g i q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (pushGuardedEdgesSentence w R S c d C D f a g i q)) := TheoryTransport.sentence (source_pushGuardedEdges w R S c d C D f a g i q)

theorem native_pushGuardedEdges {m} (w R S c d C D f a g i q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (pushGuardedEdgesSentence w R S c d C D f a g i q)) := ZFReplay.replay (pushGuardedEdges_kernel_certificate w R S c d C D f a g i q)

def pushEdgesSentence {m} (w R S c d C D f a g i q : Fin m) : Source.Sentence := ((SyntaxTermImagePushSyntax.pushed w R S c d C D f a g).imp (((GraphSyntax.edge g i q).iff (SyntaxTermImagePushSyntax.value w R S c d C D f i q)))).close

theorem source_pushEdges {m} (w R S c d C D f a g i q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (pushEdgesSentence w R S c d C D f a g i q) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTermImagePushSyntax.pushed w R S c d C D f a g) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (SyntaxTermImagePushSyntax.pushed w R S c d C D f a g) := .hyp (Or.inl rfl)
  exact SyntaxTermImagePushGraph.edge_iff hZ w R S c d C D f a g i q h0

theorem pushEdges_kernel_certificate {m} (w R S c d C D f a g i q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (pushEdgesSentence w R S c d C D f a g i q)) := TheoryTransport.sentence (source_pushEdges w R S c d C D f a g i q)

theorem native_pushEdges {m} (w R S c d C D f a g i q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (pushEdgesSentence w R S c d C D f a g i q)) := ZFReplay.replay (pushEdges_kernel_certificate w R S c d C D f a g i q)

def pushAtValueSentence {m} (w R S c d C D f a g i t q : Fin m) : Source.Sentence := ((SyntaxTermImagePushSyntax.pushed w R S c d C D f a g).imp ((GraphSyntax.edge f i t).imp (((GraphSyntax.edge g i q).iff (SyntaxRenameTermSyntax.renamed w R S c d C D t q))))).close

theorem source_pushAtValue {m} (w R S c d C D f a g i t q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (pushAtValueSentence w R S c d C D f a g i t q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (GraphSyntax.edge f i t) (Context.add (SyntaxTermImagePushSyntax.pushed w R S c d C D f a g) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (SyntaxTermImagePushSyntax.pushed w R S c d C D f a g) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (GraphSyntax.edge f i t) := .hyp (Or.inl rfl)
  exact SyntaxTermImagePushGraph.at_value hZ w R S c d C D f a g i t q h0 h1

theorem pushAtValue_kernel_certificate {m} (w R S c d C D f a g i t q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (pushAtValueSentence w R S c d C D f a g i t q)) := TheoryTransport.sentence (source_pushAtValue w R S c d C D f a g i t q)

theorem native_pushAtValue {m} (w R S c d C D f a g i t q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (pushAtValueSentence w R S c d C D f a g i t q)) := ZFReplay.replay (pushAtValue_kernel_certificate w R S c d C D f a g i t q)

def bothExistSentence {m} (w R S c d C D r s a b : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxIndexMapSyntax.maps w R S c d C D).imp ((SyntaxTermImageSyntax.maps w r s a b c d).imp ((SyntaxTermImagePushBoth.existsBoth w R S c d C D r s a b))))).close

theorem source_bothExist {m} (w R S c d C D r s a b : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (bothExistSentence w R S c d C D r s a b) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTermImageSyntax.maps w r s a b c d) (Context.add (SyntaxIndexMapSyntax.maps w R S c d C D) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxIndexMapSyntax.maps w R S c d C D) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxTermImageSyntax.maps w r s a b c d) := .hyp (Or.inl rfl)
  exact SyntaxTermImagePushBoth.exists_both hZ w R S c d C D r s a b h0 h1 h2

theorem bothExist_kernel_certificate {m} (w R S c d C D r s a b : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (bothExistSentence w R S c d C D r s a b)) := TheoryTransport.sentence (source_bothExist w R S c d C D r s a b)

theorem native_bothExist {m} (w R S c d C D r s a b : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (bothExistSentence w R S c d C D r s a b)) := ZFReplay.replay (bothExist_kernel_certificate w R S c d C D r s a b)

def bothTargetSentence {m} (w R S c d C D r s a b g h : Fin m) : Source.Sentence := ((SyntaxTermImagePushBoth.both w R S c d C D r s a b g h).imp ((SyntaxTermImageSyntax.maps w g h a b C D))).close

theorem source_bothTarget {m} (w R S c d C D r s a b g h : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (bothTargetSentence w R S c d C D r s a b g h) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTermImagePushBoth.both w R S c d C D r s a b g h) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (SyntaxTermImagePushBoth.both w R S c d C D r s a b g h) := .hyp (Or.inl rfl)
  exact SyntaxTermImagePushBoth.target_maps w R S c d C D r s a b g h h0

theorem bothTarget_kernel_certificate {m} (w R S c d C D r s a b g h : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (bothTargetSentence w R S c d C D r s a b g h)) := TheoryTransport.sentence (source_bothTarget w R S c d C D r s a b g h)

theorem native_bothTarget {m} (w R S c d C D r s a b g h : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (bothTargetSentence w R S c d C D r s a b g h)) := ZFReplay.replay (bothTarget_kernel_certificate w R S c d C D r s a b g h)

def bothUniqueSentence {m} (w R S c d C D r s a b g h G H : Fin m) : Source.Sentence := ((SyntaxTermImagePushBoth.both w R S c d C D r s a b g h).imp ((SyntaxTermImagePushBoth.both w R S c d C D r s a b G H).imp (((Formula.equal g G).conj (Formula.equal h H))))).close

theorem source_bothUnique {m} (w R S c d C D r s a b g h G H : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (bothUniqueSentence w R S c d C D r s a b g h G H) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTermImagePushBoth.both w R S c d C D r s a b G H) (Context.add (SyntaxTermImagePushBoth.both w R S c d C D r s a b g h) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (SyntaxTermImagePushBoth.both w R S c d C D r s a b g h) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxTermImagePushBoth.both w R S c d C D r s a b G H) := .hyp (Or.inl rfl)
  exact SyntaxTermImagePushBoth.unique_pair hZ w R S c d C D r s a b g h G H h0 h1

theorem bothUnique_kernel_certificate {m} (w R S c d C D r s a b g h G H : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (bothUniqueSentence w R S c d C D r s a b g h G H)) := TheoryTransport.sentence (source_bothUnique w R S c d C D r s a b g h G H)

theorem native_bothUnique {m} (w R S c d C D r s a b g h G H : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (bothUniqueSentence w R S c d C D r s a b g h G H)) := ZFReplay.replay (bothUnique_kernel_certificate w R S c d C D r s a b g h G H)

def boundShiftExistsSentence {m} (w r s a b c d C : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxTermImageSyntax.maps w r s a b c d).imp ((OmegaSyntax.successor C c).imp ((SyntaxTermImageBoundShift.existsShift w r s a b c d C))))).close

theorem source_boundShiftExists {m} (w r s a b c d C : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (boundShiftExistsSentence w r s a b c d C) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (OmegaSyntax.successor C c) (Context.add (SyntaxTermImageSyntax.maps w r s a b c d) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxTermImageSyntax.maps w r s a b c d) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (OmegaSyntax.successor C c) := .hyp (Or.inl rfl)
  exact SyntaxTermImageBoundShift.exists_shift hZ w r s a b c d C h0 h1 h2

theorem boundShiftExists_kernel_certificate {m} (w r s a b c d C : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (boundShiftExistsSentence w r s a b c d C)) := TheoryTransport.sentence (source_boundShiftExists w r s a b c d C)

theorem native_boundShiftExists {m} (w r s a b c d C : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (boundShiftExistsSentence w r s a b c d C)) := ZFReplay.replay (boundShiftExists_kernel_certificate w r s a b c d C)

end PPAC.Migration.Internal.ObjectMixedTerm
