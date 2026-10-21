import PPAC.Migration.Internal.SyntaxTypeJudgment

/-! 实际上下文状态、集合值递归和内部类型判断的闭句模式及原nativeZF证明。 -/
namespace PPAC.Migration.Internal.ObjectSyntaxTypeStates
open Source SourceAlgebra SourceLogic OmegaSyntax PairSyntax PowerSetSyntax GraphSyntax OrdinalSyntax SyntaxAtomSyntax SyntaxTermSyntax SyntaxFormulaLocalSyntax SyntaxTypeStateSyntax SyntaxTypeRecursionSyntax SyntaxTypeEvaluationSyntax SyntaxTypeJudgmentSyntax

def localContextSentence {m} (w b f h n : Fin m) : Source.Sentence := ((localType w b f h n).imp (contexts w b f)).close

theorem source_localContext {m} (w b f h n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (localContextSentence w b f h n) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (localType w b f h n) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (localType w b f h n) := .hyp (Or.inl rfl)
  exact SyntaxFormulaLocal.context w b f h n h0

theorem localContext_kernel_certificate {m} (w b f h n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (localContextSentence w b f h n)) := TheoryTransport.sentence (source_localContext w b f h n)

theorem native_localContext {m} (w b f h n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (localContextSentence w b f h n)) := ZFReplay.replay (localContext_kernel_certificate w b f h n)

def localRangeSentence {m} (w b f h n : Fin m) : Source.Sentence := ((omega w).imp ((localType w b f h n).imp (Formula.mem n w))).close

theorem source_localRange {m} (w b f h n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (localRangeSentence w b f h n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (localType w b f h n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (localType w b f h n) := .hyp (Or.inl rfl)
  exact SyntaxFormulaLocal.range hZ w b f h n h0 h1

theorem localRange_kernel_certificate {m} (w b f h n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (localRangeSentence w b f h n)) := TheoryTransport.sentence (source_localRange w b f h n)

theorem native_localRange {m} (w b f h n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (localRangeSentence w b f h n)) := ZFReplay.replay (localRange_kernel_certificate w b f h n)

def rowAtPairSentence {m} (w n h p b f : Fin m) : Source.Sentence := ((ordered p b f).imp ((row w n h p).iff (localType w b f h n))).close

theorem source_rowAtPair {m} (w n h p b f : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (rowAtPairSentence w n h p b f) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (ordered p b f) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (ordered p b f) := .hyp (Or.inl rfl)
  exact SyntaxTypeStateRows.pair_iff hZ w n h p b f h0

theorem rowAtPair_kernel_certificate {m} (w n h p b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (rowAtPairSentence w n h p b f)) := TheoryTransport.sentence (source_rowAtPair w n h p b f)

theorem native_rowAtPair {m} (w n h p b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (rowAtPairSentence w n h p b f)) := ZFReplay.replay (rowAtPair_kernel_certificate w n h p b f)

def stateExistsSentence {m} (w c n h : Fin m) : Source.Sentence := (existsState w c n h).close

theorem source_stateExists {m} (w c n h : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (stateExistsSentence w c n h) := by
  apply close_derives
  let Δ : Context m := Source.SetLanguage.ZF.at m
  have hZ : ZFContext.Evidence Δ := by
    exact ZFContext.source_ZF m
  exact SyntaxTypeStateExistence.exists_state hZ w c n h

theorem stateExists_kernel_certificate {m} (w c n h : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (stateExistsSentence w c n h)) := TheoryTransport.sentence (source_stateExists w c n h)

theorem native_stateExists {m} (w c n h : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (stateExistsSentence w c n h)) := ZFReplay.replay (stateExists_kernel_certificate w c n h)

def stateFiberSentence {m} (w c n h : Fin m) : Source.Sentence := (SyntaxTypeStateSyntax.fiber w c n h).close

theorem source_stateFiber {m} (w c n h : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (stateFiberSentence w c n h) := by
  apply close_derives
  let Δ : Context m := Source.SetLanguage.ZF.at m
  have hZ : ZFContext.Evidence Δ := by
    exact ZFContext.source_ZF m
  exact SyntaxTypeStateExistence.actual_fiber hZ w c n h

theorem stateFiber_kernel_certificate {m} (w c n h : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (stateFiberSentence w c n h)) := TheoryTransport.sentence (source_stateFiber w c n h)

theorem native_stateFiber {m} (w c n h : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (stateFiberSentence w c n h)) := ZFReplay.replay (stateFiber_kernel_certificate w c n h)

def stateUniqueSentence {m} (w c n h v t : Fin m) : Source.Sentence := ((state w c n h v).imp ((state w c n h t).imp (Formula.equal v t))).close

theorem source_stateUnique {m} (w c n h v t : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (stateUniqueSentence w c n h v t) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (state w c n h t) (Context.add (state w c n h v) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (state w c n h v) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (state w c n h t) := .hyp (Or.inl rfl)
  exact SyntaxTypeStateExistence.unique hZ w c n h v t h0 h1

theorem stateUnique_kernel_certificate {m} (w c n h v t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (stateUniqueSentence w c n h v t)) := TheoryTransport.sentence (source_stateUnique w c n h v t)

theorem native_stateUnique {m} (w c n h v t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (stateUniqueSentence w c n h v t)) := ZFReplay.replay (stateUnique_kernel_certificate w c n h v t)

def stateSubsetSentence {m} (w c n h v : Fin m) : Source.Sentence := ((state w c n h v).imp (RestrictionSyntax.subset v c)).close

theorem source_stateSubset {m} (w c n h v : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (stateSubsetSentence w c n h v) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (state w c n h v) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (state w c n h v) := .hyp (Or.inl rfl)
  exact SyntaxTypeStateExistence.subset w c n h v h0

theorem stateSubset_kernel_certificate {m} (w c n h v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (stateSubsetSentence w c n h v)) := TheoryTransport.sentence (source_stateSubset w c n h v)

theorem native_stateSubset {m} (w c n h v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (stateSubsetSentence w c n h v)) := ZFReplay.replay (stateSubset_kernel_certificate w c n h v)

def stateUniverseSentence {m} (w c u n h v : Fin m) : Source.Sentence := ((powerOf u c).imp ((state w c n h v).imp (Formula.mem v u))).close

theorem source_stateUniverse {m} (w c u n h v : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (stateUniverseSentence w c u n h v) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (state w c n h v) (Context.add (powerOf u c) (Source.SetLanguage.ZF.at m))
  have h0 : Derives Δ (powerOf u c) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (state w c n h v) := .hyp (Or.inl rfl)
  exact SyntaxTypeStateExistence.member_universe w c u n h v h0 h1

theorem stateUniverse_kernel_certificate {m} (w c u n h v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (stateUniverseSentence w c u n h v)) := TheoryTransport.sentence (source_stateUniverse w c u n h v)

theorem native_stateUniverse {m} (w c u n h v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (stateUniverseSentence w c u n h v)) := ZFReplay.replay (stateUniverse_kernel_certificate w c u n h v)

def noJunkSentence {m} (w c n h v p : Fin m) : Source.Sentence := ((state w c n h v).imp ((Formula.mem p v).imp ((Formula.mem p c).conj (row w n h p)))).close

theorem source_noJunk {m} (w c n h v p : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (noJunkSentence w c n h v p) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem p v) (Context.add (state w c n h v) (Source.SetLanguage.ZF.at m))
  have h0 : Derives Δ (state w c n h v) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (Formula.mem p v) := .hyp (Or.inl rfl)
  exact SyntaxTypeStateMembership.no_junk w c n h v p h0 h1

theorem noJunk_kernel_certificate {m} (w c n h v p : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (noJunkSentence w c n h v p)) := TheoryTransport.sentence (source_noJunk w c n h v p)

theorem native_noJunk {m} (w c n h v p : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (noJunkSentence w c n h v p)) := ZFReplay.replay (noJunk_kernel_certificate w c n h v p)

def stateEdgeSentence {m} (w a c n h v b f : Fin m) : Source.Sentence := ((powerOf a w).imp ((powerOf c a).imp ((state w c n h v).imp ((edge v b f).iff (localType w b f h n))))).close

theorem source_stateEdge {m} (w a c n h v b f : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (stateEdgeSentence w a c n h v b f) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (state w c n h v) (Context.add (powerOf c a) (Context.add (powerOf a w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (powerOf a w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (powerOf c a) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (state w c n h v) := .hyp (Or.inl rfl)
  exact SyntaxTypeStateMembership.edge_iff hZ w a c n h v b f h0 h1 h2

theorem stateEdge_kernel_certificate {m} (w a c n h v b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (stateEdgeSentence w a c n h v b f)) := TheoryTransport.sentence (source_stateEdge w a c n h v b f)

theorem native_stateEdge {m} (w a c n h v b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (stateEdgeSentence w a c n h v b f)) := ZFReplay.replay (stateEdge_kernel_certificate w a c n h v b f)

def badContextSentence {m} (w c n h v b f : Fin m) : Source.Sentence := ((state w c n h v).imp (((contexts w b f).neg).imp ((edge v b f).neg))).close

theorem source_badContext {m} (w c n h v b f : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (badContextSentence w c n h v b f) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add ((contexts w b f).neg) (Context.add (state w c n h v) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (state w c n h v) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ ((contexts w b f).neg) := .hyp (Or.inl rfl)
  exact SyntaxTypeStateMembership.bad_context hZ w c n h v b f h0 h1

theorem badContext_kernel_certificate {m} (w c n h v b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (badContextSentence w c n h v b f)) := TheoryTransport.sentence (source_badContext w c n h v b f)

theorem native_badContext {m} (w c n h v b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (badContextSentence w c n h v b f)) := ZFReplay.replay (badContext_kernel_certificate w c n h v b f)

def offNaturalSentence {m} (w c n h v : Fin m) : Source.Sentence := ((omega w).imp (((Formula.mem n w).neg).imp ((state w c n h v).imp (empty v)))).close

theorem source_offNatural {m} (w c n h v : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (offNaturalSentence w c n h v) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (state w c n h v) (Context.add ((Formula.mem n w).neg) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ ((Formula.mem n w).neg) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (state w c n h v) := .hyp (Or.inl rfl)
  exact SyntaxTypeStateMembership.off_natural hZ w c n h v h0 h1 h2

theorem offNatural_kernel_certificate {m} (w c n h v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (offNaturalSentence w c n h v)) := TheoryTransport.sentence (source_offNatural w c n h v)

theorem native_offNatural {m} (w c n h v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (offNaturalSentence w c n h v)) := ZFReplay.replay (offNatural_kernel_certificate w c n h v)

def totalSentence {m} (w c : Fin m) : Source.Sentence := (OrdinalRecursionTotal.total SyntaxTypeRecursionSyntax.matrix (two w c)).close

theorem source_total {m} (w c : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (totalSentence w c) := by
  apply close_derives
  let Δ : Context m := Source.SetLanguage.ZF.at m
  have hZ : ZFContext.Evidence Δ := by
    exact ZFContext.source_ZF m
  exact SyntaxTypeRecursionStep.total hZ (two w c)

theorem total_kernel_certificate {m} (w c : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (totalSentence w c)) := TheoryTransport.sentence (source_total w c)

theorem native_total {m} (w c : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (totalSentence w c)) := ZFReplay.replay (total_kernel_certificate w c)

def deterministicSentence {m} (w c : Fin m) : Source.Sentence := (OrdinalRecursionDeterminism.deterministic SyntaxTypeRecursionSyntax.matrix (two w c)).close

theorem source_deterministic {m} (w c : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (deterministicSentence w c) := by
  apply close_derives
  let Δ : Context m := Source.SetLanguage.ZF.at m
  have hZ : ZFContext.Evidence Δ := by
    exact ZFContext.source_ZF m
  exact SyntaxTypeRecursionStep.deterministic hZ (two w c)

theorem deterministic_kernel_certificate {m} (w c : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (deterministicSentence w c)) := TheoryTransport.sentence (source_deterministic w c)

theorem native_deterministic {m} (w c : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (deterministicSentence w c)) := ZFReplay.replay (deterministic_kernel_certificate w c)

def recursorsSentence {m} (w c : Fin m) : Source.Sentence := (recursors w c).close

theorem source_recursors {m} (w c : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (recursorsSentence w c) := by
  apply close_derives
  let Δ : Context m := Source.SetLanguage.ZF.at m
  have hZ : ZFContext.Evidence Δ := by
    exact ZFContext.source_ZF m
  exact SyntaxTypeRecursors.all_unique hZ w c

theorem recursors_kernel_certificate {m} (w c : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (recursorsSentence w c)) := TheoryTransport.sentence (source_recursors w c)

theorem native_recursors {m} (w c : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (recursorsSentence w c)) := ZFReplay.replay (recursors_kernel_certificate w c)

def ordinalFiberSentence {m} (w c d : Fin m) : Source.Sentence := ((ordinal d).imp (OrdinalRecursionExistenceSyntax.fiber SyntaxTypeRecursionSyntax.matrix (two w c) d)).close

theorem source_ordinalFiber {m} (w c d : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (ordinalFiberSentence w c d) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (ordinal d) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (ordinal d) := .hyp (Or.inl rfl)
  exact SyntaxTypeRecursors.at_ordinal hZ w c d h0

theorem ordinalFiber_kernel_certificate {m} (w c d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (ordinalFiberSentence w c d)) := TheoryTransport.sentence (source_ordinalFiber w c d)

theorem native_ordinalFiber {m} (w c d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (ordinalFiberSentence w c d)) := ZFReplay.replay (ordinalFiber_kernel_certificate w c d)

def actualCarriersSentence {m} (w : Fin m) : Source.Sentence := (actualRecursors w).close

theorem source_actualCarriers {m} (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (actualCarriersSentence w) := by
  apply close_derives
  let Δ : Context m := Source.SetLanguage.ZF.at m
  have hZ : ZFContext.Evidence Δ := by
    exact ZFContext.source_ZF m
  exact SyntaxTypeRecursors.actual_carrier_recursors hZ w

theorem actualCarriers_kernel_certificate {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (actualCarriersSentence w)) := TheoryTransport.sentence (source_actualCarriers w)

theorem native_actualCarriers {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (actualCarriersSentence w)) := ZFReplay.replay (actualCarriers_kernel_certificate w)

def evaluationExistsSentence {m} (w c n : Fin m) : Source.Sentence := ((ordinal n).imp (existsValue w c n)).close

theorem source_evaluationExists {m} (w c n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (evaluationExistsSentence w c n) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (ordinal n) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (ordinal n) := .hyp (Or.inl rfl)
  exact SyntaxTypeEvaluationExistence.exists_value hZ w c n h0

theorem evaluationExists_kernel_certificate {m} (w c n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (evaluationExistsSentence w c n)) := TheoryTransport.sentence (source_evaluationExists w c n)

theorem native_evaluationExists {m} (w c n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (evaluationExistsSentence w c n)) := ZFReplay.replay (evaluationExists_kernel_certificate w c n)

def naturalEvaluationSentence {m} (w c n : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem n w).imp (existsValue w c n))).close

theorem source_naturalEvaluation {m} (w c n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (naturalEvaluationSentence w c n) := by
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
  exact SyntaxTypeEvaluationExistence.at_natural hZ w c n h0 h1

theorem naturalEvaluation_kernel_certificate {m} (w c n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (naturalEvaluationSentence w c n)) := TheoryTransport.sentence (source_naturalEvaluation w c n)

theorem native_naturalEvaluation {m} (w c n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (naturalEvaluationSentence w c n)) := ZFReplay.replay (naturalEvaluation_kernel_certificate w c n)

def evaluationUniqueSentence {m} (w c n v t : Fin m) : Source.Sentence := ((ordinal n).imp ((evaluation w c n v).imp ((evaluation w c n t).imp (Formula.equal v t)))).close

theorem source_evaluationUnique {m} (w c n v t : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (evaluationUniqueSentence w c n v t) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (evaluation w c n t) (Context.add (evaluation w c n v) (Context.add (ordinal n) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (ordinal n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (evaluation w c n v) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (evaluation w c n t) := .hyp (Or.inl rfl)
  exact SyntaxTypeEvaluationUnique.unique hZ w c n v t h0 h1 h2

theorem evaluationUnique_kernel_certificate {m} (w c n v t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (evaluationUniqueSentence w c n v t)) := TheoryTransport.sentence (source_evaluationUnique w c n v t)

theorem native_evaluationUnique {m} (w c n v t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (evaluationUniqueSentence w c n v t)) := ZFReplay.replay (evaluationUnique_kernel_certificate w c n v t)

def evaluationFiberSentence {m} (w c n : Fin m) : Source.Sentence := ((ordinal n).imp (SyntaxTypeEvaluationSyntax.fiber w c n)).close

theorem source_evaluationFiber {m} (w c n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (evaluationFiberSentence w c n) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (ordinal n) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (ordinal n) := .hyp (Or.inl rfl)
  exact SyntaxTypeEvaluationUnique.exists_unique hZ w c n h0

theorem evaluationFiber_kernel_certificate {m} (w c n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (evaluationFiberSentence w c n)) := TheoryTransport.sentence (source_evaluationFiber w c n)

theorem native_evaluationFiber {m} (w c n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (evaluationFiberSentence w c n)) := ZFReplay.replay (evaluationFiber_kernel_certificate w c n)

def graphsAgreeSentence {m} (w c f g d t : Fin m) : Source.Sentence := ((ordinal d).imp ((ordinal t).imp ((graph w c f d).imp ((graph w c g t).imp (GraphFamilySyntax.agrees f g))))).close

theorem source_graphsAgree {m} (w c f g d t : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (graphsAgreeSentence w c f g d t) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (graph w c g t) (Context.add (graph w c f d) (Context.add (ordinal t) (Context.add (ordinal d) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (ordinal d) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (ordinal t) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (graph w c f d) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (graph w c g t) := .hyp (Or.inl rfl)
  exact SyntaxTypeEvaluationUnique.graphs_agree hZ w c f g d t h0 h1 h2 h3

theorem graphsAgree_kernel_certificate {m} (w c f g d t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (graphsAgreeSentence w c f g d t)) := TheoryTransport.sentence (source_graphsAgree w c f g d t)

theorem native_graphsAgree {m} (w c f g d t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (graphsAgreeSentence w c f g d t)) := ZFReplay.replay (graphsAgree_kernel_certificate w c f g d t)

def graphValueSentence {m} (w c f d n v : Fin m) : Source.Sentence := ((ordinal d).imp ((Formula.mem n d).imp ((graph w c f d).imp ((edge f n v).iff (evaluation w c n v))))).close

theorem source_graphValue {m} (w c f d n v : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (graphValueSentence w c f d n v) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (graph w c f d) (Context.add (Formula.mem n d) (Context.add (ordinal d) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (ordinal d) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (Formula.mem n d) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (graph w c f d) := .hyp (Or.inl rfl)
  exact SyntaxTypeGraphValues.edge_iff_value hZ w c f d n v h0 h1 h2

theorem graphValue_kernel_certificate {m} (w c f d n v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (graphValueSentence w c f d n v)) := TheoryTransport.sentence (source_graphValue w c f d n v)

theorem native_graphValue {m} (w c f d n v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (graphValueSentence w c f d n v)) := ZFReplay.replay (graphValue_kernel_certificate w c f d n v)

def historySentence {m} (w c n v : Fin m) : Source.Sentence := ((ordinal n).imp ((evaluation w c n v).imp (SyntaxTypeHistory.stepHistory w c n v))).close

theorem source_history {m} (w c n v : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (historySentence w c n v) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (evaluation w c n v) (Context.add (ordinal n) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (ordinal n) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (evaluation w c n v) := .hyp (Or.inl rfl)
  exact SyntaxTypeHistory.from_value hZ w c n v h0 h1

theorem history_kernel_certificate {m} (w c n v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (historySentence w c n v)) := TheoryTransport.sentence (source_history w c n v)

theorem native_history {m} (w c n v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (historySentence w c n v)) := ZFReplay.replay (history_kernel_certificate w c n v)

def evaluationSubsetSentence {m} (w c n v : Fin m) : Source.Sentence := ((ordinal n).imp ((evaluation w c n v).imp (RestrictionSyntax.subset v c))).close

theorem source_evaluationSubset {m} (w c n v : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (evaluationSubsetSentence w c n v) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (evaluation w c n v) (Context.add (ordinal n) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (ordinal n) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (evaluation w c n v) := .hyp (Or.inl rfl)
  exact SyntaxTypeHistory.range_subset hZ w c n v h0 h1

theorem evaluationSubset_kernel_certificate {m} (w c n v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (evaluationSubsetSentence w c n v)) := TheoryTransport.sentence (source_evaluationSubset w c n v)

theorem native_evaluationSubset {m} (w c n v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (evaluationSubsetSentence w c n v)) := ZFReplay.replay (evaluationSubset_kernel_certificate w c n v)

def evaluationUniverseSentence {m} (w c u n v : Fin m) : Source.Sentence := ((powerOf u c).imp ((ordinal n).imp ((evaluation w c n v).imp (Formula.mem v u)))).close

theorem source_evaluationUniverse {m} (w c u n v : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (evaluationUniverseSentence w c u n v) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (evaluation w c n v) (Context.add (ordinal n) (Context.add (powerOf u c) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (powerOf u c) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (ordinal n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (evaluation w c n v) := .hyp (Or.inl rfl)
  exact SyntaxTypeHistory.range_member hZ w c u n v h0 h1 h2

theorem evaluationUniverse_kernel_certificate {m} (w c u n v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (evaluationUniverseSentence w c u n v)) := TheoryTransport.sentence (source_evaluationUniverse w c u n v)

theorem native_evaluationUniverse {m} (w c u n v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (evaluationUniverseSentence w c u n v)) := ZFReplay.replay (evaluationUniverse_kernel_certificate w c u n v)

def evaluationOffNaturalSentence {m} (w c n v : Fin m) : Source.Sentence := ((omega w).imp ((ordinal n).imp (((Formula.mem n w).neg).imp ((evaluation w c n v).imp (empty v))))).close

theorem source_evaluationOffNatural {m} (w c n v : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (evaluationOffNaturalSentence w c n v) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (evaluation w c n v) (Context.add ((Formula.mem n w).neg) (Context.add (ordinal n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (ordinal n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ ((Formula.mem n w).neg) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (evaluation w c n v) := .hyp (Or.inl rfl)
  exact SyntaxTypeHistory.off_natural hZ w c n v h0 h1 h2 h3

theorem evaluationOffNatural_kernel_certificate {m} (w c n v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (evaluationOffNaturalSentence w c n v)) := TheoryTransport.sentence (source_evaluationOffNatural w c n v)

theorem native_evaluationOffNatural {m} (w c n v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (evaluationOffNaturalSentence w c n v)) := ZFReplay.replay (evaluationOffNatural_kernel_certificate w c n v)

def typedAtValueSentence {m} (w c n b f v : Fin m) : Source.Sentence := ((ordinal n).imp ((Formula.mem n w).imp ((evaluation w c n v).imp ((typed w c n b f).iff (edge v b f))))).close

theorem source_typedAtValue {m} (w c n b f v : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (typedAtValueSentence w c n b f v) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (evaluation w c n v) (Context.add (Formula.mem n w) (Context.add (ordinal n) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (ordinal n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (Formula.mem n w) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (evaluation w c n v) := .hyp (Or.inl rfl)
  exact SyntaxTypeJudgment.at_value hZ w c n b f v h0 h1 h2

theorem typedAtValue_kernel_certificate {m} (w c n b f v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (typedAtValueSentence w c n b f v)) := TheoryTransport.sentence (source_typedAtValue w c n b f v)

theorem native_typedAtValue {m} (w c n b f v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (typedAtValueSentence w c n b f v)) := ZFReplay.replay (typedAtValue_kernel_certificate w c n b f v)

def readTypedSentence {m} (w c h d x b f : Fin m) : Source.Sentence := ((ordinal d).imp ((Formula.mem x d).imp ((Formula.mem x w).imp ((graph w c h d).imp ((SyntaxContextReadSyntax.read h x b f).iff (typed w c x b f)))))).close

theorem source_readTyped {m} (w c h d x b f : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (readTypedSentence w c h d x b f) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (graph w c h d) (Context.add (Formula.mem x w) (Context.add (Formula.mem x d) (Context.add (ordinal d) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (ordinal d) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (Formula.mem x d) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (Formula.mem x w) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (graph w c h d) := .hyp (Or.inl rfl)
  exact SyntaxTypeJudgment.read_iff hZ w c h d x b f h0 h1 h2 h3

theorem readTyped_kernel_certificate {m} (w c h d x b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (readTypedSentence w c h d x b f)) := TheoryTransport.sentence (source_readTyped w c h d x b f)

theorem native_readTyped {m} (w c h d x b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (readTypedSentence w c h d x b f)) := ZFReplay.replay (readTyped_kernel_certificate w c h d x b f)

def typedRejectCodeSentence {m} (w c n b f : Fin m) : Source.Sentence := (((Formula.mem n w).neg).imp ((typed w c n b f).neg)).close

theorem source_typedRejectCode {m} (w c n b f : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (typedRejectCodeSentence w c n b f) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add ((Formula.mem n w).neg) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ ((Formula.mem n w).neg) := .hyp (Or.inl rfl)
  exact SyntaxTypeJudgmentSyntax.reject_code w c n b f h0

theorem typedRejectCode_kernel_certificate {m} (w c n b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (typedRejectCodeSentence w c n b f)) := TheoryTransport.sentence (source_typedRejectCode w c n b f)

theorem native_typedRejectCode {m} (w c n b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (typedRejectCodeSentence w c n b f)) := ZFReplay.replay (typedRejectCode_kernel_certificate w c n b f)

def typedRejectContextSentence {m} (w c n b f : Fin m) : Source.Sentence := (((contexts w b f).neg).imp ((typed w c n b f).neg)).close

theorem source_typedRejectContext {m} (w c n b f : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (typedRejectContextSentence w c n b f) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add ((contexts w b f).neg) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ ((contexts w b f).neg) := .hyp (Or.inl rfl)
  exact SyntaxTypeJudgmentSyntax.reject_context w c n b f h0

theorem typedRejectContext_kernel_certificate {m} (w c n b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (typedRejectContextSentence w c n b f)) := TheoryTransport.sentence (source_typedRejectContext w c n b f)

theorem native_typedRejectContext {m} (w c n b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (typedRejectContextSentence w c n b f)) := ZFReplay.replay (typedRejectContext_kernel_certificate w c n b f)

def introduceAtomicSentence {m} (w b f h n : Fin m) : Source.Sentence := ((SyntaxAtomSyntax.atomic w b f n).imp (localType w b f h n)).close

theorem source_introduceAtomic {m} (w b f h n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (introduceAtomicSentence w b f h n) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxAtomSyntax.atomic w b f n) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (SyntaxAtomSyntax.atomic w b f n) := .hyp (Or.inl rfl)
  exact SyntaxFormulaLocalSyntax.intro_atomic w b f h n h0

theorem introduceAtomic_kernel_certificate {m} (w b f h n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (introduceAtomicSentence w b f h n)) := TheoryTransport.sentence (source_introduceAtomic w b f h n)

theorem native_introduceAtomic {m} (w b f h n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (introduceAtomicSentence w b f h n)) := ZFReplay.replay (introduceAtomic_kernel_certificate w b f h n)

def introduceNegationSentence {m} (w b f h n : Fin m) : Source.Sentence := ((SyntaxLogicalSyntax.negation w b f h n).imp (localType w b f h n)).close

theorem source_introduceNegation {m} (w b f h n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (introduceNegationSentence w b f h n) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxLogicalSyntax.negation w b f h n) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (SyntaxLogicalSyntax.negation w b f h n) := .hyp (Or.inl rfl)
  exact SyntaxFormulaLocalSyntax.intro_negation w b f h n h0

theorem introduceNegation_kernel_certificate {m} (w b f h n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (introduceNegationSentence w b f h n)) := TheoryTransport.sentence (source_introduceNegation w b f h n)

theorem native_introduceNegation {m} (w b f h n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (introduceNegationSentence w b f h n)) := ZFReplay.replay (introduceNegation_kernel_certificate w b f h n)

def introduceBinarySentence {m} (kind : Fin 4) (w b f h n : Fin m) : Source.Sentence := ((SyntaxLogicalSyntax.binary kind w b f h n).imp (localType w b f h n)).close

theorem source_introduceBinary {m} (kind : Fin 4) (w b f h n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (introduceBinarySentence kind w b f h n) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxLogicalSyntax.binary kind w b f h n) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (SyntaxLogicalSyntax.binary kind w b f h n) := .hyp (Or.inl rfl)
  exact SyntaxFormulaLocalSyntax.intro_binary kind w b f h n h0

theorem introduceBinary_kernel_certificate {m} (kind : Fin 4) (w b f h n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (introduceBinarySentence kind w b f h n)) := TheoryTransport.sentence (source_introduceBinary kind w b f h n)

theorem native_introduceBinary {m} (kind : Fin 4) (w b f h n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (introduceBinarySentence kind w b f h n)) := ZFReplay.replay (introduceBinary_kernel_certificate kind w b f h n)

def introduceQuantifierSentence {m} (universal : Bool) (w b f h n : Fin m) : Source.Sentence := ((SyntaxLogicalSyntax.quantified universal w b f h n).imp (localType w b f h n)).close

theorem source_introduceQuantifier {m} (universal : Bool) (w b f h n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (introduceQuantifierSentence universal w b f h n) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxLogicalSyntax.quantified universal w b f h n) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (SyntaxLogicalSyntax.quantified universal w b f h n) := .hyp (Or.inl rfl)
  exact SyntaxFormulaLocalSyntax.intro_quantified universal w b f h n h0

theorem introduceQuantifier_kernel_certificate {m} (universal : Bool) (w b f h n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (introduceQuantifierSentence universal w b f h n)) := TheoryTransport.sentence (source_introduceQuantifier universal w b f h n)

theorem native_introduceQuantifier {m} (universal : Bool) (w b f h n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (introduceQuantifierSentence universal w b f h n)) := ZFReplay.replay (introduceQuantifier_kernel_certificate universal w b f h n)
end PPAC.Migration.Internal.ObjectSyntaxTypeStates
