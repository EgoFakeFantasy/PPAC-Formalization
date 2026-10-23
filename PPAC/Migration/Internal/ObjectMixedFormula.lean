import PPAC.Migration.Internal.SyntaxMixedFormulaEndpoints

/-! 全内部混合公式替换实际总唯一、精确端点及递归状态的原YesMetaZFC核证书。 -/
namespace PPAC.Migration.Internal.ObjectMixedFormula
open Source SourceAlgebra SourceLogic OmegaSyntax

def stateExistsSentence {m} (w r s a b c d q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMixedFormulaStateSyntax.legal w r s a b c d q).imp ((SyntaxMixedFormulaStateSyntax.existsState w r s a b c d q)))).close

theorem source_stateExists {m} (w r s a b c d q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (stateExistsSentence w r s a b c d q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMixedFormulaStateSyntax.legal w r s a b c d q) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxMixedFormulaStateSyntax.legal w r s a b c d q) := .hyp (Or.inl rfl)
  exact SyntaxMixedFormulaStateExistence.actual_exists hZ w r s a b c d q h0 h1

theorem stateExists_kernel_certificate {m} (w r s a b c d q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (stateExistsSentence w r s a b c d q)) := TheoryTransport.sentence (source_stateExists w r s a b c d q)

theorem native_stateExists {m} (w r s a b c d q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (stateExistsSentence w r s a b c d q)) := ZFReplay.replay (stateExists_kernel_certificate w r s a b c d q)

def stateInputIffSentence {m} (w r s a b c d q : Fin m) : Source.Sentence := ((omega w).imp (((SyntaxMixedFormulaStateSyntax.existsState w r s a b c d q).iff (SyntaxMixedFormulaStateSyntax.legal w r s a b c d q)))).close

theorem source_stateInputIff {m} (w r s a b c d q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (stateInputIffSentence w r s a b c d q) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact SyntaxMixedFormulaStateExistence.exists_iff_legal hZ w r s a b c d q h0

theorem stateInputIff_kernel_certificate {m} (w r s a b c d q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (stateInputIffSentence w r s a b c d q)) := TheoryTransport.sentence (source_stateInputIff w r s a b c d q)

theorem native_stateInputIff {m} (w r s a b c d q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (stateInputIffSentence w r s a b c d q)) := ZFReplay.replay (stateInputIff_kernel_certificate w r s a b c d q)

def stateNaturalSentence {m} (w r s a b c d q t : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMixedFormulaStateSyntax.cell w r s a b c d q t).imp ((Formula.mem t w)))).close

theorem source_stateNatural {m} (w r s a b c d q t : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (stateNaturalSentence w r s a b c d q t) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMixedFormulaStateSyntax.cell w r s a b c d q t) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxMixedFormulaStateSyntax.cell w r s a b c d q t) := .hyp (Or.inl rfl)
  exact SyntaxMixedFormulaState.natural hZ w r s a b c d q t h0 h1

theorem stateNatural_kernel_certificate {m} (w r s a b c d q t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (stateNaturalSentence w r s a b c d q t)) := TheoryTransport.sentence (source_stateNatural w r s a b c d q t)

theorem native_stateNatural {m} (w r s a b c d q t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (stateNaturalSentence w r s a b c d q t)) := ZFReplay.replay (stateNatural_kernel_certificate w r s a b c d q t)

def stateUniqueSentence {m} (w r s a b c d q t v : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMixedFormulaStateSyntax.cell w r s a b c d q t).imp ((SyntaxMixedFormulaStateSyntax.cell w r s a b c d q v).imp ((Formula.equal t v))))).close

theorem source_stateUnique {m} (w r s a b c d q t v : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (stateUniqueSentence w r s a b c d q t v) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMixedFormulaStateSyntax.cell w r s a b c d q v) (Context.add (SyntaxMixedFormulaStateSyntax.cell w r s a b c d q t) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxMixedFormulaStateSyntax.cell w r s a b c d q t) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxMixedFormulaStateSyntax.cell w r s a b c d q v) := .hyp (Or.inl rfl)
  exact SyntaxMixedFormulaState.unique hZ w r s a b c d q t v h0 h1 h2

theorem stateUnique_kernel_certificate {m} (w r s a b c d q t v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (stateUniqueSentence w r s a b c d q t v)) := TheoryTransport.sentence (source_stateUnique w r s a b c d q t v)

theorem native_stateUnique {m} (w r s a b c d q t v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (stateUniqueSentence w r s a b c d q t v)) := ZFReplay.replay (stateUnique_kernel_certificate w r s a b c d q t v)

def stateDecodeSentence {m} (w t : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMixedFormulaStateSyntax.recognized w t).imp ((SyntaxMixedFormulaStateSyntax.decodedFiber w t)))).close

theorem source_stateDecode {m} (w t : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (stateDecodeSentence w t) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMixedFormulaStateSyntax.recognized w t) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxMixedFormulaStateSyntax.recognized w t) := .hyp (Or.inl rfl)
  exact SyntaxMixedFormulaStateDecode.actual_decode hZ w t h0 h1

theorem stateDecode_kernel_certificate {m} (w t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (stateDecodeSentence w t)) := TheoryTransport.sentence (source_stateDecode w t)

theorem native_stateDecode {m} (w t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (stateDecodeSentence w t)) := ZFReplay.replay (stateDecode_kernel_certificate w t)

def stateParamsUniqueSentence {m} (w t r s a b c d q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMixedFormulaStateSyntax.cell w r s a b c d q t).imp ((SyntaxMixedFormulaStateSyntax.uniqueParams w t r s a b c d q)))).close

theorem source_stateParamsUnique {m} (w t r s a b c d q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (stateParamsUniqueSentence w t r s a b c d q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMixedFormulaStateSyntax.cell w r s a b c d q t) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxMixedFormulaStateSyntax.cell w r s a b c d q t) := .hyp (Or.inl rfl)
  exact SyntaxMixedFormulaStateDecode.unique_params hZ w t r s a b c d q h0 h1

theorem stateParamsUnique_kernel_certificate {m} (w t r s a b c d q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (stateParamsUniqueSentence w t r s a b c d q)) := TheoryTransport.sentence (source_stateParamsUnique w t r s a b c d q)

theorem native_stateParamsUnique {m} (w t r s a b c d q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (stateParamsUniqueSentence w t r s a b c d q)) := ZFReplay.replay (stateParamsUnique_kernel_certificate w t r s a b c d q)

def containsAtStateSentence {m} (w v r s a b c d q t : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMixedFormulaStateSyntax.state w r s a b c d q t).imp (((SyntaxMixedFormulaQuerySyntax.contains w v r s a b c d q).iff (Formula.mem t v))))).close

theorem source_containsAtState {m} (w v r s a b c d q t : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (containsAtStateSentence w v r s a b c d q t) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMixedFormulaStateSyntax.state w r s a b c d q t) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxMixedFormulaStateSyntax.state w r s a b c d q t) := .hyp (Or.inl rfl)
  exact SyntaxMixedFormulaQuery.contains_at_state hZ w v r s a b c d q t h0 h1

theorem containsAtState_kernel_certificate {m} (w v r s a b c d q t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (containsAtStateSentence w v r s a b c d q t)) := TheoryTransport.sentence (source_containsAtState w v r s a b c d q t)

theorem native_containsAtState {m} (w v r s a b c d q t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (containsAtStateSentence w v r s a b c d q t)) := ZFReplay.replay (containsAtState_kernel_certificate w v r s a b c d q t)

def readAtValueSentence {m} (w h D x v r s a b c d q : Fin m) : Source.Sentence := ((GraphSyntax.functionOn h D).imp ((GraphSyntax.edge h x v).imp (((SyntaxMixedFormulaQuerySyntax.read w h x r s a b c d q).iff (SyntaxMixedFormulaQuerySyntax.contains w v r s a b c d q))))).close

theorem source_readAtValue {m} (w h D x v r s a b c d q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (readAtValueSentence w h D x v r s a b c d q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (GraphSyntax.edge h x v) (Context.add (GraphSyntax.functionOn h D) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (GraphSyntax.functionOn h D) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (GraphSyntax.edge h x v) := .hyp (Or.inl rfl)
  exact SyntaxMixedFormulaQuery.at_value hZ w h D x v r s a b c d q h0 h1

theorem readAtValue_kernel_certificate {m} (w h D x v r s a b c d q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (readAtValueSentence w h D x v r s a b c d q)) := TheoryTransport.sentence (source_readAtValue w h D x v r s a b c d q)

theorem native_readAtValue {m} (w h D x v r s a b c d q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (readAtValueSentence w h D x v r s a b c d q)) := ZFReplay.replay (readAtValue_kernel_certificate w h D x v r s a b c d q)

def readAtStateSentence {m} (w h D x v r s a b c d q t : Fin m) : Source.Sentence := ((omega w).imp ((GraphSyntax.functionOn h D).imp ((GraphSyntax.edge h x v).imp ((SyntaxMixedFormulaStateSyntax.state w r s a b c d q t).imp (((SyntaxMixedFormulaQuerySyntax.read w h x r s a b c d q).iff (Formula.mem t v))))))).close

theorem source_readAtState {m} (w h D x v r s a b c d q t : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (readAtStateSentence w h D x v r s a b c d q t) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMixedFormulaStateSyntax.state w r s a b c d q t) (Context.add (GraphSyntax.edge h x v) (Context.add (GraphSyntax.functionOn h D) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (GraphSyntax.functionOn h D) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (GraphSyntax.edge h x v) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxMixedFormulaStateSyntax.state w r s a b c d q t) := .hyp (Or.inl rfl)
  exact SyntaxMixedFormulaQuery.at_state hZ w h D x v r s a b c d q t h0 h1 h2 h3

theorem readAtState_kernel_certificate {m} (w h D x v r s a b c d q t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (readAtStateSentence w h D x v r s a b c d q t)) := TheoryTransport.sentence (source_readAtState w h D x v r s a b c d q t)

theorem native_readAtState {m} (w h D x v r s a b c d q t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (readAtStateSentence w h D x v r s a b c d q t)) := ZFReplay.replay (readAtState_kernel_certificate w h D x v r s a b c d q t)

def advancedQuerySentence {m} (w h x r s a b c d q A C K H : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxCodedMixedBinderSyntax.lifted w r s a b c d A C K H).imp (((SyntaxMixedFormulaQuerySyntax.advanced w h x r s a b c d q).iff (SyntaxMixedFormulaQuerySyntax.read w h x K H A b C d q))))).close

theorem source_advancedQuery {m} (w h x r s a b c d q A C K H : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (advancedQuerySentence w h x r s a b c d q A C K H) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxCodedMixedBinderSyntax.lifted w r s a b c d A C K H) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxCodedMixedBinderSyntax.lifted w r s a b c d A C K H) := .hyp (Or.inl rfl)
  exact SyntaxMixedFormulaAdvancedKnown.at_lift hZ w h x r s a b c d q A C K H h0 h1

theorem advancedQuery_kernel_certificate {m} (w h x r s a b c d q A C K H : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (advancedQuerySentence w h x r s a b c d q A C K H)) := TheoryTransport.sentence (source_advancedQuery w h x r s a b c d q A C K H)

theorem native_advancedQuery {m} (w h x r s a b c d q A C K H : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (advancedQuerySentence w h x r s a b c d q A C K H)) := ZFReplay.replay (advancedQuery_kernel_certificate w h x r s a b c d q A C K H)

def operatorExistsSentence {m} (w n h : Fin m) : Source.Sentence := ((SyntaxMixedFormulaOperatorSyntax.existsValue w n h)).close

theorem source_operatorExists {m} (w n h : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (operatorExistsSentence w n h) := by
  apply close_derives
  let Δ : Context m := Source.SetLanguage.ZF.at m
  have hZ : ZFContext.Evidence Δ := by
    exact ZFContext.source_ZF m
  exact SyntaxMixedFormulaOperatorExistence.exists_value hZ w n h

theorem operatorExists_kernel_certificate {m} (w n h : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (operatorExistsSentence w n h)) := TheoryTransport.sentence (source_operatorExists w n h)

theorem native_operatorExists {m} (w n h : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (operatorExistsSentence w n h)) := ZFReplay.replay (operatorExists_kernel_certificate w n h)

def operatorFiberSentence {m} (w n h : Fin m) : Source.Sentence := ((SyntaxMixedFormulaOperatorSyntax.fiber w n h)).close

theorem source_operatorFiber {m} (w n h : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (operatorFiberSentence w n h) := by
  apply close_derives
  let Δ : Context m := Source.SetLanguage.ZF.at m
  have hZ : ZFContext.Evidence Δ := by
    exact ZFContext.source_ZF m
  exact SyntaxMixedFormulaOperatorExistence.actual_fiber hZ w n h

theorem operatorFiber_kernel_certificate {m} (w n h : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (operatorFiberSentence w n h)) := TheoryTransport.sentence (source_operatorFiber w n h)

theorem native_operatorFiber {m} (w n h : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (operatorFiberSentence w n h)) := ZFReplay.replay (operatorFiber_kernel_certificate w n h)

def operatorUniqueSentence {m} (w n h v t : Fin m) : Source.Sentence := ((SyntaxMixedFormulaOperatorSyntax.value w n h v).imp ((SyntaxMixedFormulaOperatorSyntax.value w n h t).imp ((Formula.equal v t)))).close

theorem source_operatorUnique {m} (w n h v t : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (operatorUniqueSentence w n h v t) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMixedFormulaOperatorSyntax.value w n h t) (Context.add (SyntaxMixedFormulaOperatorSyntax.value w n h v) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (SyntaxMixedFormulaOperatorSyntax.value w n h v) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxMixedFormulaOperatorSyntax.value w n h t) := .hyp (Or.inl rfl)
  exact SyntaxMixedFormulaOperatorExistence.unique hZ w n h v t h0 h1

theorem operatorUnique_kernel_certificate {m} (w n h v t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (operatorUniqueSentence w n h v t)) := TheoryTransport.sentence (source_operatorUnique w n h v t)

theorem native_operatorUnique {m} (w n h v t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (operatorUniqueSentence w n h v t)) := ZFReplay.replay (operatorUnique_kernel_certificate w n h v t)

def operatorSubsetSentence {m} (w n h v : Fin m) : Source.Sentence := ((SyntaxMixedFormulaOperatorSyntax.value w n h v).imp ((RestrictionSyntax.subset v w))).close

theorem source_operatorSubset {m} (w n h v : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (operatorSubsetSentence w n h v) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMixedFormulaOperatorSyntax.value w n h v) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (SyntaxMixedFormulaOperatorSyntax.value w n h v) := .hyp (Or.inl rfl)
  exact SyntaxMixedFormulaOperatorExistence.subset w n h v h0

theorem operatorSubset_kernel_certificate {m} (w n h v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (operatorSubsetSentence w n h v)) := TheoryTransport.sentence (source_operatorSubset w n h v)

theorem native_operatorSubset {m} (w n h v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (operatorSubsetSentence w n h v)) := ZFReplay.replay (operatorSubset_kernel_certificate w n h v)

def operatorRecognizedSentence {m} (w n h v p : Fin m) : Source.Sentence := ((SyntaxMixedFormulaOperatorSyntax.value w n h v).imp ((Formula.mem p v).imp ((SyntaxMixedFormulaStateSyntax.recognized w p)))).close

theorem source_operatorRecognized {m} (w n h v p : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (operatorRecognizedSentence w n h v p) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem p v) (Context.add (SyntaxMixedFormulaOperatorSyntax.value w n h v) (Source.SetLanguage.ZF.at m))
  have h0 : Derives Δ (SyntaxMixedFormulaOperatorSyntax.value w n h v) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (Formula.mem p v) := .hyp (Or.inl rfl)
  exact SyntaxMixedFormulaOperatorMembership.member_recognized w n h v p h0 h1

theorem operatorRecognized_kernel_certificate {m} (w n h v p : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (operatorRecognizedSentence w n h v p)) := TheoryTransport.sentence (source_operatorRecognized w n h v p)

theorem native_operatorRecognized {m} (w n h v p : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (operatorRecognizedSentence w n h v p)) := ZFReplay.replay (operatorRecognized_kernel_certificate w n h v p)

def operatorMembershipSentence {m} (w n h v p r s a b c d q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMixedFormulaOperatorSyntax.value w n h v).imp ((SyntaxMixedFormulaStateSyntax.state w r s a b c d q p).imp (((Formula.mem p v).iff (SyntaxMixedFormulaLocalSyntax.content w r s a b c d h n q)))))).close

theorem source_operatorMembership {m} (w n h v p r s a b c d q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (operatorMembershipSentence w n h v p r s a b c d q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMixedFormulaStateSyntax.state w r s a b c d q p) (Context.add (SyntaxMixedFormulaOperatorSyntax.value w n h v) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxMixedFormulaOperatorSyntax.value w n h v) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxMixedFormulaStateSyntax.state w r s a b c d q p) := .hyp (Or.inl rfl)
  exact SyntaxMixedFormulaOperatorMembership.at_state hZ w n h v p r s a b c d q h0 h1 h2

theorem operatorMembership_kernel_certificate {m} (w n h v p r s a b c d q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (operatorMembershipSentence w n h v p r s a b c d q)) := TheoryTransport.sentence (source_operatorMembership w n h v p r s a b c d q)

theorem native_operatorMembership {m} (w n h v p r s a b c d q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (operatorMembershipSentence w n h v p r s a b c d q)) := ZFReplay.replay (operatorMembership_kernel_certificate w n h v p r s a b c d q)

def recursorsSentence {m} (w : Fin m) : Source.Sentence := ((SyntaxMixedFormulaRecursionSyntax.recursors w)).close

theorem source_recursors {m} (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (recursorsSentence w) := by
  apply close_derives
  let Δ : Context m := Source.SetLanguage.ZF.at m
  have hZ : ZFContext.Evidence Δ := by
    exact ZFContext.source_ZF m
  exact SyntaxMixedFormulaRecursors.all_unique hZ w

theorem recursors_kernel_certificate {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (recursorsSentence w)) := TheoryTransport.sentence (source_recursors w)

theorem native_recursors {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (recursorsSentence w)) := ZFReplay.replay (recursors_kernel_certificate w)

def carrierSentence {m} (w : Fin m) : Source.Sentence := ((SyntaxMixedFormulaRecursionSyntax.actualRecursors w)).close

theorem source_carrier {m} (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (carrierSentence w) := by
  apply close_derives
  let Δ : Context m := Source.SetLanguage.ZF.at m
  have hZ : ZFContext.Evidence Δ := by
    exact ZFContext.source_ZF m
  exact SyntaxMixedFormulaRecursors.actual_carrier_recursors hZ w

theorem carrier_kernel_certificate {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (carrierSentence w)) := TheoryTransport.sentence (source_carrier w)

theorem native_carrier {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (carrierSentence w)) := ZFReplay.replay (carrier_kernel_certificate w)

def graphExistsSentence {m} (w D : Fin m) : Source.Sentence := ((OrdinalSyntax.ordinal D).imp ((SyntaxMixedFormulaRecursionSyntax.graphExists w D))).close

theorem source_graphExists {m} (w D : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (graphExistsSentence w D) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (OrdinalSyntax.ordinal D) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (OrdinalSyntax.ordinal D) := .hyp (Or.inl rfl)
  exact SyntaxMixedFormulaRecursors.exists_graph hZ w D h0

theorem graphExists_kernel_certificate {m} (w D : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (graphExistsSentence w D)) := TheoryTransport.sentence (source_graphExists w D)

theorem native_graphExists {m} (w D : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (graphExistsSentence w D)) := ZFReplay.replay (graphExists_kernel_certificate w D)

def evaluationExistsSentence {m} (w n : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem n w).imp ((SyntaxMixedFormulaEvaluationSyntax.existsValue w n)))).close

theorem source_evaluationExists {m} (w n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (evaluationExistsSentence w n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem n w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (Formula.mem n w) := .hyp (Or.inl rfl)
  exact SyntaxMixedFormulaEvaluationExistence.at_natural hZ w n h0 h1

theorem evaluationExists_kernel_certificate {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (evaluationExistsSentence w n)) := TheoryTransport.sentence (source_evaluationExists w n)

theorem native_evaluationExists {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (evaluationExistsSentence w n)) := ZFReplay.replay (evaluationExists_kernel_certificate w n)

def evaluationFiberSentence {m} (w n : Fin m) : Source.Sentence := ((OrdinalSyntax.ordinal n).imp ((SyntaxMixedFormulaEvaluationSyntax.fiber w n))).close

theorem source_evaluationFiber {m} (w n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (evaluationFiberSentence w n) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (OrdinalSyntax.ordinal n) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (OrdinalSyntax.ordinal n) := .hyp (Or.inl rfl)
  exact SyntaxMixedFormulaEvaluationUnique.exists_unique hZ w n h0

theorem evaluationFiber_kernel_certificate {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (evaluationFiberSentence w n)) := TheoryTransport.sentence (source_evaluationFiber w n)

theorem native_evaluationFiber {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (evaluationFiberSentence w n)) := ZFReplay.replay (evaluationFiber_kernel_certificate w n)

def evaluationUniqueSentence {m} (w n v t : Fin m) : Source.Sentence := ((OrdinalSyntax.ordinal n).imp ((SyntaxMixedFormulaEvaluationSyntax.evaluation w n v).imp ((SyntaxMixedFormulaEvaluationSyntax.evaluation w n t).imp ((Formula.equal v t))))).close

theorem source_evaluationUnique {m} (w n v t : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (evaluationUniqueSentence w n v t) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMixedFormulaEvaluationSyntax.evaluation w n t) (Context.add (SyntaxMixedFormulaEvaluationSyntax.evaluation w n v) (Context.add (OrdinalSyntax.ordinal n) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (OrdinalSyntax.ordinal n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxMixedFormulaEvaluationSyntax.evaluation w n v) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxMixedFormulaEvaluationSyntax.evaluation w n t) := .hyp (Or.inl rfl)
  exact SyntaxMixedFormulaEvaluationUnique.unique hZ w n v t h0 h1 h2

theorem evaluationUnique_kernel_certificate {m} (w n v t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (evaluationUniqueSentence w n v t)) := TheoryTransport.sentence (source_evaluationUnique w n v t)

theorem native_evaluationUnique {m} (w n v t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (evaluationUniqueSentence w n v t)) := ZFReplay.replay (evaluationUnique_kernel_certificate w n v t)

def historySentence {m} (w n v : Fin m) : Source.Sentence := ((OrdinalSyntax.ordinal n).imp ((SyntaxMixedFormulaEvaluationSyntax.evaluation w n v).imp ((SyntaxMixedFormulaHistory.stepHistory w n v)))).close

theorem source_history {m} (w n v : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (historySentence w n v) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMixedFormulaEvaluationSyntax.evaluation w n v) (Context.add (OrdinalSyntax.ordinal n) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (OrdinalSyntax.ordinal n) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxMixedFormulaEvaluationSyntax.evaluation w n v) := .hyp (Or.inl rfl)
  exact SyntaxMixedFormulaHistory.from_value hZ w n v h0 h1

theorem history_kernel_certificate {m} (w n v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (historySentence w n v)) := TheoryTransport.sentence (source_history w n v)

theorem native_history {m} (w n v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (historySentence w n v)) := ZFReplay.replay (history_kernel_certificate w n v)

def judgmentReadSentence {m} (w h D x r s a b c d q : Fin m) : Source.Sentence := ((OrdinalSyntax.ordinal D).imp ((Formula.mem x D).imp ((SyntaxMixedFormulaRecursionSyntax.graph w h D).imp (((SyntaxMixedFormulaQuerySyntax.read w h x r s a b c d q).iff (SyntaxMixedFormulaJudgmentSyntax.substituted w r s a b c d x q)))))).close

theorem source_judgmentRead {m} (w h D x r s a b c d q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (judgmentReadSentence w h D x r s a b c d q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMixedFormulaRecursionSyntax.graph w h D) (Context.add (Formula.mem x D) (Context.add (OrdinalSyntax.ordinal D) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (OrdinalSyntax.ordinal D) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (Formula.mem x D) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxMixedFormulaRecursionSyntax.graph w h D) := .hyp (Or.inl rfl)
  exact SyntaxMixedFormulaJudgment.read_iff hZ w h D x r s a b c d q h0 h1 h2

theorem judgmentRead_kernel_certificate {m} (w h D x r s a b c d q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (judgmentReadSentence w h D x r s a b c d q)) := TheoryTransport.sentence (source_judgmentRead w h D x r s a b c d q)

theorem native_judgmentRead {m} (w h D x r s a b c d q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (judgmentReadSentence w h D x r s a b c d q)) := ZFReplay.replay (judgmentRead_kernel_certificate w h D x r s a b c d q)

def formulaSourceSentence {m} (w r s a b c d n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMixedFormulaJudgmentSyntax.substituted w r s a b c d n q).imp ((FormulaCodeSyntax.formulaCode w n a b)))).close

theorem source_formulaSource {m} (w r s a b c d n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (formulaSourceSentence w r s a b c d n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMixedFormulaJudgmentSyntax.substituted w r s a b c d n q) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxMixedFormulaJudgmentSyntax.substituted w r s a b c d n q) := .hyp (Or.inl rfl)
  exact SyntaxMixedFormulaRecursive.source_type hZ w r s a b c d n q h0 h1

theorem formulaSource_kernel_certificate {m} (w r s a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (formulaSourceSentence w r s a b c d n q)) := TheoryTransport.sentence (source_formulaSource w r s a b c d n q)

theorem native_formulaSource {m} (w r s a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (formulaSourceSentence w r s a b c d n q)) := ZFReplay.replay (formulaSource_kernel_certificate w r s a b c d n q)

def formulaTargetSentence {m} (w r s a b c d n q : Fin m) : Source.Sentence := ((SyntaxMixedFormulaJudgmentSyntax.substituted w r s a b c d n q).imp ((FormulaCodeSyntax.formulaCode w q c d))).close

theorem source_formulaTarget {m} (w r s a b c d n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (formulaTargetSentence w r s a b c d n q) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMixedFormulaJudgmentSyntax.substituted w r s a b c d n q) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (SyntaxMixedFormulaJudgmentSyntax.substituted w r s a b c d n q) := .hyp (Or.inl rfl)
  exact SyntaxMixedFormulaJudgment.target_type w r s a b c d n q h0

theorem formulaTarget_kernel_certificate {m} (w r s a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (formulaTargetSentence w r s a b c d n q)) := TheoryTransport.sentence (source_formulaTarget w r s a b c d n q)

theorem native_formulaTarget {m} (w r s a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (formulaTargetSentence w r s a b c d n q)) := ZFReplay.replay (formulaTarget_kernel_certificate w r s a b c d n q)

def formulaLegalSentence {m} (w r s a b c d n q : Fin m) : Source.Sentence := ((SyntaxMixedFormulaJudgmentSyntax.substituted w r s a b c d n q).imp ((SyntaxMixedFormulaStateSyntax.legal w r s a b c d q))).close

theorem source_formulaLegal {m} (w r s a b c d n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (formulaLegalSentence w r s a b c d n q) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMixedFormulaJudgmentSyntax.substituted w r s a b c d n q) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (SyntaxMixedFormulaJudgmentSyntax.substituted w r s a b c d n q) := .hyp (Or.inl rfl)
  exact SyntaxMixedFormulaJudgment.legal w r s a b c d n q h0

theorem formulaLegal_kernel_certificate {m} (w r s a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (formulaLegalSentence w r s a b c d n q)) := TheoryTransport.sentence (source_formulaLegal w r s a b c d n q)

theorem native_formulaLegal {m} (w r s a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (formulaLegalSentence w r s a b c d n q)) := ZFReplay.replay (formulaLegal_kernel_certificate w r s a b c d n q)

def formulaInputSentence {m} (w r s a b c d n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMixedFormulaJudgmentSyntax.substituted w r s a b c d n q).imp ((SyntaxMixedFormulaOutputSyntax.input w r s a b c d n)))).close

theorem source_formulaInput {m} (w r s a b c d n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (formulaInputSentence w r s a b c d n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMixedFormulaJudgmentSyntax.substituted w r s a b c d n q) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxMixedFormulaJudgmentSyntax.substituted w r s a b c d n q) := .hyp (Or.inl rfl)
  exact SyntaxMixedFormulaOutput.input_of_substituted hZ w r s a b c d n q h0 h1

theorem formulaInput_kernel_certificate {m} (w r s a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (formulaInputSentence w r s a b c d n q)) := TheoryTransport.sentence (source_formulaInput w r s a b c d n q)

theorem native_formulaInput {m} (w r s a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (formulaInputSentence w r s a b c d n q)) := ZFReplay.replay (formulaInput_kernel_certificate w r s a b c d n q)

def formulaNaturalSentence {m} (w r s a b c d n q : Fin m) : Source.Sentence := ((SyntaxMixedFormulaJudgmentSyntax.substituted w r s a b c d n q).imp ((Formula.mem q w))).close

theorem source_formulaNatural {m} (w r s a b c d n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (formulaNaturalSentence w r s a b c d n q) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMixedFormulaJudgmentSyntax.substituted w r s a b c d n q) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (SyntaxMixedFormulaJudgmentSyntax.substituted w r s a b c d n q) := .hyp (Or.inl rfl)
  exact SyntaxMixedFormulaOutput.output_natural w r s a b c d n q h0

theorem formulaNatural_kernel_certificate {m} (w r s a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (formulaNaturalSentence w r s a b c d n q)) := TheoryTransport.sentence (source_formulaNatural w r s a b c d n q)

theorem native_formulaNatural {m} (w r s a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (formulaNaturalSentence w r s a b c d n q)) := ZFReplay.replay (formulaNatural_kernel_certificate w r s a b c d n q)

def recursiveIffSentence {m} (w r s a b c d n q : Fin m) : Source.Sentence := ((omega w).imp (((SyntaxMixedFormulaJudgmentSyntax.substituted w r s a b c d n q).iff (SyntaxMixedFormulaRecursiveSyntax.criterion w r s a b c d n q)))).close

theorem source_recursiveIff {m} (w r s a b c d n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (recursiveIffSentence w r s a b c d n q) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact SyntaxMixedFormulaRecursive.recursive_iff hZ w r s a b c d n q h0

theorem recursiveIff_kernel_certificate {m} (w r s a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (recursiveIffSentence w r s a b c d n q)) := TheoryTransport.sentence (source_recursiveIff w r s a b c d n q)

theorem native_recursiveIff {m} (w r s a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (recursiveIffSentence w r s a b c d n q)) := ZFReplay.replay (recursiveIff_kernel_certificate w r s a b c d n q)

def formulaFiberSentence {m} (w r s a b c d n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMixedFormulaOutputSyntax.input w r s a b c d n).imp ((SyntaxMixedFormulaOutputSyntax.fiber w r s a b c d n)))).close

theorem source_formulaFiber {m} (w r s a b c d n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (formulaFiberSentence w r s a b c d n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMixedFormulaOutputSyntax.input w r s a b c d n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxMixedFormulaOutputSyntax.input w r s a b c d n) := .hyp (Or.inl rfl)
  exact SyntaxMixedFormulaOutputInduction.actual_fiber hZ w r s a b c d n h0 h1

theorem formulaFiber_kernel_certificate {m} (w r s a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (formulaFiberSentence w r s a b c d n)) := TheoryTransport.sentence (source_formulaFiber w r s a b c d n)

theorem native_formulaFiber {m} (w r s a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (formulaFiberSentence w r s a b c d n)) := ZFReplay.replay (formulaFiber_kernel_certificate w r s a b c d n)

def formulaExistsSentence {m} (w r s a b c d n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMixedFormulaOutputSyntax.input w r s a b c d n).imp ((SyntaxMixedFormulaOutputSyntax.existsOutput w r s a b c d n)))).close

theorem source_formulaExists {m} (w r s a b c d n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (formulaExistsSentence w r s a b c d n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMixedFormulaOutputSyntax.input w r s a b c d n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxMixedFormulaOutputSyntax.input w r s a b c d n) := .hyp (Or.inl rfl)
  exact SyntaxMixedFormulaOutputInduction.actual_exists hZ w r s a b c d n h0 h1

theorem formulaExists_kernel_certificate {m} (w r s a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (formulaExistsSentence w r s a b c d n)) := TheoryTransport.sentence (source_formulaExists w r s a b c d n)

theorem native_formulaExists {m} (w r s a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (formulaExistsSentence w r s a b c d n)) := ZFReplay.replay (formulaExists_kernel_certificate w r s a b c d n)

def formulaUniqueSentence {m} (w r s a b c d n q v : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMixedFormulaJudgmentSyntax.substituted w r s a b c d n q).imp ((SyntaxMixedFormulaJudgmentSyntax.substituted w r s a b c d n v).imp ((Formula.equal q v))))).close

theorem source_formulaUnique {m} (w r s a b c d n q v : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (formulaUniqueSentence w r s a b c d n q v) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMixedFormulaJudgmentSyntax.substituted w r s a b c d n v) (Context.add (SyntaxMixedFormulaJudgmentSyntax.substituted w r s a b c d n q) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxMixedFormulaJudgmentSyntax.substituted w r s a b c d n q) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxMixedFormulaJudgmentSyntax.substituted w r s a b c d n v) := .hyp (Or.inl rfl)
  exact SyntaxMixedFormulaOutputInduction.unique hZ w r s a b c d n q v h0 h1 h2

theorem formulaUnique_kernel_certificate {m} (w r s a b c d n q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (formulaUniqueSentence w r s a b c d n q v)) := TheoryTransport.sentence (source_formulaUnique w r s a b c d n q v)

theorem native_formulaUnique {m} (w r s a b c d n q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (formulaUniqueSentence w r s a b c d n q v)) := ZFReplay.replay (formulaUnique_kernel_certificate w r s a b c d n q v)

def formulaUniqueOutputSentence {m} (w r s a b c d n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMixedFormulaJudgmentSyntax.substituted w r s a b c d n q).imp ((SyntaxMixedFormulaOutputSyntax.uniqueOutput w r s a b c d n q)))).close

theorem source_formulaUniqueOutput {m} (w r s a b c d n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (formulaUniqueOutputSentence w r s a b c d n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMixedFormulaJudgmentSyntax.substituted w r s a b c d n q) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxMixedFormulaJudgmentSyntax.substituted w r s a b c d n q) := .hyp (Or.inl rfl)
  exact SyntaxMixedFormulaOutputClassify.unique_output_of_substituted hZ w r s a b c d n q h0 h1

theorem formulaUniqueOutput_kernel_certificate {m} (w r s a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (formulaUniqueOutputSentence w r s a b c d n q)) := TheoryTransport.sentence (source_formulaUniqueOutput w r s a b c d n q)

theorem native_formulaUniqueOutput {m} (w r s a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (formulaUniqueOutputSentence w r s a b c d n q)) := ZFReplay.replay (formulaUniqueOutput_kernel_certificate w r s a b c d n q)

def formulaExistsIffSentence {m} (w r s a b c d n : Fin m) : Source.Sentence := ((omega w).imp (((SyntaxMixedFormulaOutputSyntax.existsOutput w r s a b c d n).iff (SyntaxMixedFormulaOutputSyntax.input w r s a b c d n)))).close

theorem source_formulaExistsIff {m} (w r s a b c d n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (formulaExistsIffSentence w r s a b c d n) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact SyntaxMixedFormulaOutputClassify.exists_iff_input hZ w r s a b c d n h0

theorem formulaExistsIff_kernel_certificate {m} (w r s a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (formulaExistsIffSentence w r s a b c d n)) := TheoryTransport.sentence (source_formulaExistsIff w r s a b c d n)

theorem native_formulaExistsIff {m} (w r s a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (formulaExistsIffSentence w r s a b c d n)) := ZFReplay.replay (formulaExistsIff_kernel_certificate w r s a b c d n)

def formulaFiberIffSentence {m} (w r s a b c d n : Fin m) : Source.Sentence := ((omega w).imp (((SyntaxMixedFormulaOutputSyntax.fiber w r s a b c d n).iff (SyntaxMixedFormulaOutputSyntax.input w r s a b c d n)))).close

theorem source_formulaFiberIff {m} (w r s a b c d n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (formulaFiberIffSentence w r s a b c d n) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact SyntaxMixedFormulaOutputClassify.fiber_iff_input hZ w r s a b c d n h0

theorem formulaFiberIff_kernel_certificate {m} (w r s a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (formulaFiberIffSentence w r s a b c d n)) := TheoryTransport.sentence (source_formulaFiberIff w r s a b c d n)

theorem native_formulaFiberIff {m} (w r s a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (formulaFiberIffSentence w r s a b c d n)) := ZFReplay.replay (formulaFiberIff_kernel_certificate w r s a b c d n)

def formulaRejectInvalidSentence {m} (w r s a b c d n : Fin m) : Source.Sentence := ((omega w).imp (((SyntaxMixedFormulaOutputSyntax.input w r s a b c d n).neg).imp (((SyntaxMixedFormulaOutputSyntax.existsOutput w r s a b c d n).neg)))).close

theorem source_formulaRejectInvalid {m} (w r s a b c d n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (formulaRejectInvalidSentence w r s a b c d n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add ((SyntaxMixedFormulaOutputSyntax.input w r s a b c d n).neg) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ ((SyntaxMixedFormulaOutputSyntax.input w r s a b c d n).neg) := .hyp (Or.inl rfl)
  exact SyntaxMixedFormulaOutputClassify.reject_input hZ w r s a b c d n h0 h1

theorem formulaRejectInvalid_kernel_certificate {m} (w r s a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (formulaRejectInvalidSentence w r s a b c d n)) := TheoryTransport.sentence (source_formulaRejectInvalid w r s a b c d n)

theorem native_formulaRejectInvalid {m} (w r s a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (formulaRejectInvalidSentence w r s a b c d n)) := ZFReplay.replay (formulaRejectInvalid_kernel_certificate w r s a b c d n)

def nullaryFalseSentence {m} (w r s a b c d n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMixedFormulaOutputSyntax.input w r s a b c d n).imp ((SyntaxNodeSyntax.constructor 0 (SyntaxAtomSyntax.nullaryTag false) w Fin.elim0 n).imp (((SyntaxMixedFormulaJudgmentSyntax.substituted w r s a b c d n q).iff (Formula.equal q n)))))).close

theorem source_nullaryFalse {m} (w r s a b c d n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (nullaryFalseSentence w r s a b c d n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNodeSyntax.constructor 0 (SyntaxAtomSyntax.nullaryTag false) w Fin.elim0 n) (Context.add (SyntaxMixedFormulaOutputSyntax.input w r s a b c d n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxMixedFormulaOutputSyntax.input w r s a b c d n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxNodeSyntax.constructor 0 (SyntaxAtomSyntax.nullaryTag false) w Fin.elim0 n) := .hyp (Or.inl rfl)
  exact SyntaxMixedFormulaEndpoints.nullary_iff hZ false w r s a b c d n q h0 h1 h2

theorem nullaryFalse_kernel_certificate {m} (w r s a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (nullaryFalseSentence w r s a b c d n q)) := TheoryTransport.sentence (source_nullaryFalse w r s a b c d n q)

theorem native_nullaryFalse {m} (w r s a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (nullaryFalseSentence w r s a b c d n q)) := ZFReplay.replay (nullaryFalse_kernel_certificate w r s a b c d n q)

def nullaryTrueSentence {m} (w r s a b c d n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMixedFormulaOutputSyntax.input w r s a b c d n).imp ((SyntaxNodeSyntax.constructor 0 (SyntaxAtomSyntax.nullaryTag true) w Fin.elim0 n).imp (((SyntaxMixedFormulaJudgmentSyntax.substituted w r s a b c d n q).iff (Formula.equal q n)))))).close

theorem source_nullaryTrue {m} (w r s a b c d n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (nullaryTrueSentence w r s a b c d n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNodeSyntax.constructor 0 (SyntaxAtomSyntax.nullaryTag true) w Fin.elim0 n) (Context.add (SyntaxMixedFormulaOutputSyntax.input w r s a b c d n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxMixedFormulaOutputSyntax.input w r s a b c d n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxNodeSyntax.constructor 0 (SyntaxAtomSyntax.nullaryTag true) w Fin.elim0 n) := .hyp (Or.inl rfl)
  exact SyntaxMixedFormulaEndpoints.nullary_iff hZ true w r s a b c d n q h0 h1 h2

theorem nullaryTrue_kernel_certificate {m} (w r s a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (nullaryTrueSentence w r s a b c d n q)) := TheoryTransport.sentence (source_nullaryTrue w r s a b c d n q)

theorem native_nullaryTrue {m} (w r s a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (nullaryTrueSentence w r s a b c d n q)) := ZFReplay.replay (nullaryTrue_kernel_certificate w r s a b c d n q)

def equalityFieldsSentence {m} (w r s a b c d n q x y X Y : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMixedFormulaOutputSyntax.input w r s a b c d n).imp ((SyntaxAtomSyntax.equalCode w x y n).imp ((SyntaxAtomSyntax.equalCode w X Y q).imp (((SyntaxMixedFormulaJudgmentSyntax.substituted w r s a b c d n q).iff (SyntaxMixedFormulaKnownFieldsSyntax.equalOperands w r s a b c d x y X Y))))))).close

theorem source_equalityFields {m} (w r s a b c d n q x y X Y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (equalityFieldsSentence w r s a b c d n q x y X Y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxAtomSyntax.equalCode w X Y q) (Context.add (SyntaxAtomSyntax.equalCode w x y n) (Context.add (SyntaxMixedFormulaOutputSyntax.input w r s a b c d n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxMixedFormulaOutputSyntax.input w r s a b c d n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxAtomSyntax.equalCode w x y n) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxAtomSyntax.equalCode w X Y q) := .hyp (Or.inl rfl)
  exact SyntaxMixedFormulaEndpoints.equality_iff hZ w r s a b c d n q x y X Y h0 h1 h2 h3

theorem equalityFields_kernel_certificate {m} (w r s a b c d n q x y X Y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (equalityFieldsSentence w r s a b c d n q x y X Y)) := TheoryTransport.sentence (source_equalityFields w r s a b c d n q x y X Y)

theorem native_equalityFields {m} (w r s a b c d n q x y X Y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (equalityFieldsSentence w r s a b c d n q x y X Y)) := ZFReplay.replay (equalityFields_kernel_certificate w r s a b c d n q x y X Y)

def membershipFieldsSentence {m} (w r s a b c d n q z Z x y X Y : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMixedFormulaOutputSyntax.input w r s a b c d n).imp ((SyntaxAtomSyntax.memberCode w z x y n).imp ((SyntaxAtomSyntax.memberCode w Z X Y q).imp (((SyntaxMixedFormulaJudgmentSyntax.substituted w r s a b c d n q).iff (SyntaxMixedFormulaKnownFieldsSyntax.memberOperands w r s a b c d z Z x y X Y))))))).close

theorem source_membershipFields {m} (w r s a b c d n q z Z x y X Y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (membershipFieldsSentence w r s a b c d n q z Z x y X Y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxAtomSyntax.memberCode w Z X Y q) (Context.add (SyntaxAtomSyntax.memberCode w z x y n) (Context.add (SyntaxMixedFormulaOutputSyntax.input w r s a b c d n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxMixedFormulaOutputSyntax.input w r s a b c d n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxAtomSyntax.memberCode w z x y n) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxAtomSyntax.memberCode w Z X Y q) := .hyp (Or.inl rfl)
  exact SyntaxMixedFormulaEndpoints.membership_iff hZ w r s a b c d n q z Z x y X Y h0 h1 h2 h3

theorem membershipFields_kernel_certificate {m} (w r s a b c d n q z Z x y X Y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (membershipFieldsSentence w r s a b c d n q z Z x y X Y)) := TheoryTransport.sentence (source_membershipFields w r s a b c d n q z Z x y X Y)

theorem native_membershipFields {m} (w r s a b c d n q z Z x y X Y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (membershipFieldsSentence w r s a b c d n q z Z x y X Y)) := ZFReplay.replay (membershipFields_kernel_certificate w r s a b c d n q z Z x y X Y)

def negationFieldsSentence {m} (w r s a b c d n q x X : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMixedFormulaOutputSyntax.input w r s a b c d n).imp ((SyntaxLogicalSyntax.singleCode 4 w x n).imp ((SyntaxLogicalSyntax.singleCode 4 w X q).imp (((SyntaxMixedFormulaJudgmentSyntax.substituted w r s a b c d n q).iff (SyntaxMixedFormulaJudgmentSyntax.substituted w r s a b c d x X))))))).close

theorem source_negationFields {m} (w r s a b c d n q x X : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (negationFieldsSentence w r s a b c d n q x X) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxLogicalSyntax.singleCode 4 w X q) (Context.add (SyntaxLogicalSyntax.singleCode 4 w x n) (Context.add (SyntaxMixedFormulaOutputSyntax.input w r s a b c d n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxMixedFormulaOutputSyntax.input w r s a b c d n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxLogicalSyntax.singleCode 4 w x n) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxLogicalSyntax.singleCode 4 w X q) := .hyp (Or.inl rfl)
  exact SyntaxMixedFormulaEndpoints.single_iff hZ 4 false (Or.inl ⟨rfl, rfl⟩) w r s a b c d n q x X h0 h1 h2 h3

theorem negationFields_kernel_certificate {m} (w r s a b c d n q x X : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (negationFieldsSentence w r s a b c d n q x X)) := TheoryTransport.sentence (source_negationFields w r s a b c d n q x X)

theorem native_negationFields {m} (w r s a b c d n q x X : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (negationFieldsSentence w r s a b c d n q x X)) := ZFReplay.replay (negationFields_kernel_certificate w r s a b c d n q x X)

def binary0FieldsSentence {m} (w r s a b c d n q x y X Y : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMixedFormulaOutputSyntax.input w r s a b c d n).imp ((SyntaxLogicalSyntax.binaryCode 0 w x y n).imp ((SyntaxLogicalSyntax.binaryCode 0 w X Y q).imp (((SyntaxMixedFormulaJudgmentSyntax.substituted w r s a b c d n q).iff ((SyntaxMixedFormulaJudgmentSyntax.substituted w r s a b c d x X).conj (SyntaxMixedFormulaJudgmentSyntax.substituted w r s a b c d y Y)))))))).close

theorem source_binary0Fields {m} (w r s a b c d n q x y X Y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binary0FieldsSentence w r s a b c d n q x y X Y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxLogicalSyntax.binaryCode 0 w X Y q) (Context.add (SyntaxLogicalSyntax.binaryCode 0 w x y n) (Context.add (SyntaxMixedFormulaOutputSyntax.input w r s a b c d n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxMixedFormulaOutputSyntax.input w r s a b c d n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxLogicalSyntax.binaryCode 0 w x y n) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxLogicalSyntax.binaryCode 0 w X Y q) := .hyp (Or.inl rfl)
  exact SyntaxMixedFormulaEndpoints.binary_iff hZ 0 w r s a b c d n q x y X Y h0 h1 h2 h3

theorem binary0Fields_kernel_certificate {m} (w r s a b c d n q x y X Y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binary0FieldsSentence w r s a b c d n q x y X Y)) := TheoryTransport.sentence (source_binary0Fields w r s a b c d n q x y X Y)

theorem native_binary0Fields {m} (w r s a b c d n q x y X Y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binary0FieldsSentence w r s a b c d n q x y X Y)) := ZFReplay.replay (binary0Fields_kernel_certificate w r s a b c d n q x y X Y)

def binary1FieldsSentence {m} (w r s a b c d n q x y X Y : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMixedFormulaOutputSyntax.input w r s a b c d n).imp ((SyntaxLogicalSyntax.binaryCode 1 w x y n).imp ((SyntaxLogicalSyntax.binaryCode 1 w X Y q).imp (((SyntaxMixedFormulaJudgmentSyntax.substituted w r s a b c d n q).iff ((SyntaxMixedFormulaJudgmentSyntax.substituted w r s a b c d x X).conj (SyntaxMixedFormulaJudgmentSyntax.substituted w r s a b c d y Y)))))))).close

theorem source_binary1Fields {m} (w r s a b c d n q x y X Y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binary1FieldsSentence w r s a b c d n q x y X Y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxLogicalSyntax.binaryCode 1 w X Y q) (Context.add (SyntaxLogicalSyntax.binaryCode 1 w x y n) (Context.add (SyntaxMixedFormulaOutputSyntax.input w r s a b c d n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxMixedFormulaOutputSyntax.input w r s a b c d n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxLogicalSyntax.binaryCode 1 w x y n) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxLogicalSyntax.binaryCode 1 w X Y q) := .hyp (Or.inl rfl)
  exact SyntaxMixedFormulaEndpoints.binary_iff hZ 1 w r s a b c d n q x y X Y h0 h1 h2 h3

theorem binary1Fields_kernel_certificate {m} (w r s a b c d n q x y X Y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binary1FieldsSentence w r s a b c d n q x y X Y)) := TheoryTransport.sentence (source_binary1Fields w r s a b c d n q x y X Y)

theorem native_binary1Fields {m} (w r s a b c d n q x y X Y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binary1FieldsSentence w r s a b c d n q x y X Y)) := ZFReplay.replay (binary1Fields_kernel_certificate w r s a b c d n q x y X Y)

def binary2FieldsSentence {m} (w r s a b c d n q x y X Y : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMixedFormulaOutputSyntax.input w r s a b c d n).imp ((SyntaxLogicalSyntax.binaryCode 2 w x y n).imp ((SyntaxLogicalSyntax.binaryCode 2 w X Y q).imp (((SyntaxMixedFormulaJudgmentSyntax.substituted w r s a b c d n q).iff ((SyntaxMixedFormulaJudgmentSyntax.substituted w r s a b c d x X).conj (SyntaxMixedFormulaJudgmentSyntax.substituted w r s a b c d y Y)))))))).close

theorem source_binary2Fields {m} (w r s a b c d n q x y X Y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binary2FieldsSentence w r s a b c d n q x y X Y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxLogicalSyntax.binaryCode 2 w X Y q) (Context.add (SyntaxLogicalSyntax.binaryCode 2 w x y n) (Context.add (SyntaxMixedFormulaOutputSyntax.input w r s a b c d n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxMixedFormulaOutputSyntax.input w r s a b c d n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxLogicalSyntax.binaryCode 2 w x y n) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxLogicalSyntax.binaryCode 2 w X Y q) := .hyp (Or.inl rfl)
  exact SyntaxMixedFormulaEndpoints.binary_iff hZ 2 w r s a b c d n q x y X Y h0 h1 h2 h3

theorem binary2Fields_kernel_certificate {m} (w r s a b c d n q x y X Y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binary2FieldsSentence w r s a b c d n q x y X Y)) := TheoryTransport.sentence (source_binary2Fields w r s a b c d n q x y X Y)

theorem native_binary2Fields {m} (w r s a b c d n q x y X Y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binary2FieldsSentence w r s a b c d n q x y X Y)) := ZFReplay.replay (binary2Fields_kernel_certificate w r s a b c d n q x y X Y)

def binary3FieldsSentence {m} (w r s a b c d n q x y X Y : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMixedFormulaOutputSyntax.input w r s a b c d n).imp ((SyntaxLogicalSyntax.binaryCode 3 w x y n).imp ((SyntaxLogicalSyntax.binaryCode 3 w X Y q).imp (((SyntaxMixedFormulaJudgmentSyntax.substituted w r s a b c d n q).iff ((SyntaxMixedFormulaJudgmentSyntax.substituted w r s a b c d x X).conj (SyntaxMixedFormulaJudgmentSyntax.substituted w r s a b c d y Y)))))))).close

theorem source_binary3Fields {m} (w r s a b c d n q x y X Y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binary3FieldsSentence w r s a b c d n q x y X Y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxLogicalSyntax.binaryCode 3 w X Y q) (Context.add (SyntaxLogicalSyntax.binaryCode 3 w x y n) (Context.add (SyntaxMixedFormulaOutputSyntax.input w r s a b c d n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxMixedFormulaOutputSyntax.input w r s a b c d n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxLogicalSyntax.binaryCode 3 w x y n) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxLogicalSyntax.binaryCode 3 w X Y q) := .hyp (Or.inl rfl)
  exact SyntaxMixedFormulaEndpoints.binary_iff hZ 3 w r s a b c d n q x y X Y h0 h1 h2 h3

theorem binary3Fields_kernel_certificate {m} (w r s a b c d n q x y X Y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binary3FieldsSentence w r s a b c d n q x y X Y)) := TheoryTransport.sentence (source_binary3Fields w r s a b c d n q x y X Y)

theorem native_binary3Fields {m} (w r s a b c d n q x y X Y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binary3FieldsSentence w r s a b c d n q x y X Y)) := ZFReplay.replay (binary3Fields_kernel_certificate w r s a b c d n q x y X Y)

def forallFieldsSentence {m} (w r s a b c d n q x X : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMixedFormulaOutputSyntax.input w r s a b c d n).imp ((SyntaxLogicalSyntax.singleCode 9 w x n).imp ((SyntaxLogicalSyntax.singleCode 9 w X q).imp (((SyntaxMixedFormulaJudgmentSyntax.substituted w r s a b c d n q).iff (SyntaxMixedFormulaRecursiveSyntax.advanced w x r s a b c d X))))))).close

theorem source_forallFields {m} (w r s a b c d n q x X : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (forallFieldsSentence w r s a b c d n q x X) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxLogicalSyntax.singleCode 9 w X q) (Context.add (SyntaxLogicalSyntax.singleCode 9 w x n) (Context.add (SyntaxMixedFormulaOutputSyntax.input w r s a b c d n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxMixedFormulaOutputSyntax.input w r s a b c d n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxLogicalSyntax.singleCode 9 w x n) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxLogicalSyntax.singleCode 9 w X q) := .hyp (Or.inl rfl)
  exact SyntaxMixedFormulaEndpoints.single_iff hZ 9 true (Or.inr (Or.inl ⟨rfl, rfl⟩)) w r s a b c d n q x X h0 h1 h2 h3

theorem forallFields_kernel_certificate {m} (w r s a b c d n q x X : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (forallFieldsSentence w r s a b c d n q x X)) := TheoryTransport.sentence (source_forallFields w r s a b c d n q x X)

theorem native_forallFields {m} (w r s a b c d n q x X : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (forallFieldsSentence w r s a b c d n q x X)) := ZFReplay.replay (forallFields_kernel_certificate w r s a b c d n q x X)

def forallAtLiftSentence {m} (w r s a b c d n q x X A C K H : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMixedFormulaOutputSyntax.input w r s a b c d n).imp ((SyntaxCodedMixedBinderSyntax.lifted w r s a b c d A C K H).imp ((SyntaxLogicalSyntax.singleCode 9 w x n).imp ((SyntaxLogicalSyntax.singleCode 9 w X q).imp (((SyntaxMixedFormulaJudgmentSyntax.substituted w r s a b c d n q).iff (SyntaxMixedFormulaJudgmentSyntax.substituted w K H A b C d x X)))))))).close

theorem source_forallAtLift {m} (w r s a b c d n q x X A C K H : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (forallAtLiftSentence w r s a b c d n q x X A C K H) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxLogicalSyntax.singleCode 9 w X q) (Context.add (SyntaxLogicalSyntax.singleCode 9 w x n) (Context.add (SyntaxCodedMixedBinderSyntax.lifted w r s a b c d A C K H) (Context.add (SyntaxMixedFormulaOutputSyntax.input w r s a b c d n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxMixedFormulaOutputSyntax.input w r s a b c d n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (SyntaxCodedMixedBinderSyntax.lifted w r s a b c d A C K H) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (SyntaxLogicalSyntax.singleCode 9 w x n) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (SyntaxLogicalSyntax.singleCode 9 w X q) := .hyp (Or.inl rfl)
  exact SyntaxMixedFormulaEndpoints.quantified_at_lift hZ true w r s a b c d n q x X A C K H h0 h1 h2 h3 h4

theorem forallAtLift_kernel_certificate {m} (w r s a b c d n q x X A C K H : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (forallAtLiftSentence w r s a b c d n q x X A C K H)) := TheoryTransport.sentence (source_forallAtLift w r s a b c d n q x X A C K H)

theorem native_forallAtLift {m} (w r s a b c d n q x X A C K H : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (forallAtLiftSentence w r s a b c d n q x X A C K H)) := ZFReplay.replay (forallAtLift_kernel_certificate w r s a b c d n q x X A C K H)

def existsFieldsSentence {m} (w r s a b c d n q x X : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMixedFormulaOutputSyntax.input w r s a b c d n).imp ((SyntaxLogicalSyntax.singleCode 10 w x n).imp ((SyntaxLogicalSyntax.singleCode 10 w X q).imp (((SyntaxMixedFormulaJudgmentSyntax.substituted w r s a b c d n q).iff (SyntaxMixedFormulaRecursiveSyntax.advanced w x r s a b c d X))))))).close

theorem source_existsFields {m} (w r s a b c d n q x X : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (existsFieldsSentence w r s a b c d n q x X) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxLogicalSyntax.singleCode 10 w X q) (Context.add (SyntaxLogicalSyntax.singleCode 10 w x n) (Context.add (SyntaxMixedFormulaOutputSyntax.input w r s a b c d n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxMixedFormulaOutputSyntax.input w r s a b c d n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxLogicalSyntax.singleCode 10 w x n) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxLogicalSyntax.singleCode 10 w X q) := .hyp (Or.inl rfl)
  exact SyntaxMixedFormulaEndpoints.single_iff hZ 10 true (Or.inr (Or.inr ⟨rfl, rfl⟩)) w r s a b c d n q x X h0 h1 h2 h3

theorem existsFields_kernel_certificate {m} (w r s a b c d n q x X : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (existsFieldsSentence w r s a b c d n q x X)) := TheoryTransport.sentence (source_existsFields w r s a b c d n q x X)

theorem native_existsFields {m} (w r s a b c d n q x X : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (existsFieldsSentence w r s a b c d n q x X)) := ZFReplay.replay (existsFields_kernel_certificate w r s a b c d n q x X)

def existsAtLiftSentence {m} (w r s a b c d n q x X A C K H : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMixedFormulaOutputSyntax.input w r s a b c d n).imp ((SyntaxCodedMixedBinderSyntax.lifted w r s a b c d A C K H).imp ((SyntaxLogicalSyntax.singleCode 10 w x n).imp ((SyntaxLogicalSyntax.singleCode 10 w X q).imp (((SyntaxMixedFormulaJudgmentSyntax.substituted w r s a b c d n q).iff (SyntaxMixedFormulaJudgmentSyntax.substituted w K H A b C d x X)))))))).close

theorem source_existsAtLift {m} (w r s a b c d n q x X A C K H : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (existsAtLiftSentence w r s a b c d n q x X A C K H) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxLogicalSyntax.singleCode 10 w X q) (Context.add (SyntaxLogicalSyntax.singleCode 10 w x n) (Context.add (SyntaxCodedMixedBinderSyntax.lifted w r s a b c d A C K H) (Context.add (SyntaxMixedFormulaOutputSyntax.input w r s a b c d n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxMixedFormulaOutputSyntax.input w r s a b c d n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (SyntaxCodedMixedBinderSyntax.lifted w r s a b c d A C K H) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (SyntaxLogicalSyntax.singleCode 10 w x n) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (SyntaxLogicalSyntax.singleCode 10 w X q) := .hyp (Or.inl rfl)
  exact SyntaxMixedFormulaEndpoints.quantified_at_lift hZ false w r s a b c d n q x X A C K H h0 h1 h2 h3 h4

theorem existsAtLift_kernel_certificate {m} (w r s a b c d n q x X A C K H : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (existsAtLiftSentence w r s a b c d n q x X A C K H)) := TheoryTransport.sentence (source_existsAtLift w r s a b c d n q x X A C K H)

theorem native_existsAtLift {m} (w r s a b c d n q x X A C K H : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (existsAtLiftSentence w r s a b c d n q x X A C K H)) := ZFReplay.replay (existsAtLift_kernel_certificate w r s a b c d n q x X A C K H)

end PPAC.Migration.Internal.ObjectMixedFormula
