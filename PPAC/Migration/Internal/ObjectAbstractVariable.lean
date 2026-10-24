import PPAC.Migration.Internal.AbstractVariableRun

/-! 原mode1变量全部内部候选输出的数值双条件及整条运行的原核闭句。 -/
namespace PPAC.Migration.Internal.ObjectAbstractVariable
open Source SourceAlgebra SourceLogic OmegaSyntax

def originalVariableIndexGraphSentence {m} (n : Nat) (bound : Bool) (e : YesMetaZFC.Automation.ObjectHorn.Expr n) (env : Fin n → Fin m) (w idx x : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat n w env).imp ((HornExprSyntax.graph (HornVariableExpr.expression bound e) w env x).imp ((SyntaxVariableSyntax.code bound w idx x).imp ((HornExprSyntax.graph e w env idx)))))).close

theorem source_originalVariableIndexGraph {m} (n : Nat) (bound : Bool) (e : YesMetaZFC.Automation.ObjectHorn.Expr n) (env : Fin n → Fin m) (w idx x : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalVariableIndexGraphSentence n bound e env w idx x) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxVariableSyntax.code bound w idx x) (Context.add (HornExprSyntax.graph (HornVariableExpr.expression bound e) w env x) (Context.add (HornExprSyntax.environmentNat n w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (HornExprSyntax.environmentNat n w env) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (HornExprSyntax.graph (HornVariableExpr.expression bound e) w env x) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxVariableSyntax.code bound w idx x) := .hyp (Or.inl rfl)
  exact AbstractVariableIndex.index_graph hZ bound e w idx x env h0 h1 h2 h3

theorem originalVariableIndexGraph_kernel_certificate {m} (n : Nat) (bound : Bool) (e : YesMetaZFC.Automation.ObjectHorn.Expr n) (env : Fin n → Fin m) (w idx x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalVariableIndexGraphSentence n bound e env w idx x)) := TheoryTransport.sentence (source_originalVariableIndexGraph n bound e env w idx x)

theorem native_originalVariableIndexGraph {m} (n : Nat) (bound : Bool) (e : YesMetaZFC.Automation.ObjectHorn.Expr n) (env : Fin n → Fin m) (w idx x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalVariableIndexGraphSentence n bound e env w idx x)) := ZFReplay.replay (originalVariableIndexGraph_kernel_certificate n bound e env w idx x)

def modeOneBoundVariableNumericIffSentence {m} (xs : Fin 5 → Fin m) (w r idx : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNodeSyntax.constructor 5 1 w xs r).imp ((SyntaxNumeralSyntax.numeral 1 (xs 0)).imp ((SyntaxVariableSyntax.code true w idx (xs 3)).imp (((HornLookupConditionSyntax.condition w r).iff (AbstractVariableValueSyntax.boundValue w (xs 1) idx (xs 3) (xs 4)))))))).close

theorem source_modeOneBoundVariableNumericIff {m} (xs : Fin 5 → Fin m) (w r idx : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeOneBoundVariableNumericIffSentence xs w r idx) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxVariableSyntax.code true w idx (xs 3)) (Context.add (SyntaxNumeralSyntax.numeral 1 (xs 0)) (Context.add (SyntaxNodeSyntax.constructor 5 1 w xs r) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNodeSyntax.constructor 5 1 w xs r) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral 1 (xs 0)) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxVariableSyntax.code true w idx (xs 3)) := .hyp (Or.inl rfl)
  exact AbstractVariableNumeric.bound_iff hZ w r idx xs h0 h1 h2 h3

theorem modeOneBoundVariableNumericIff_kernel_certificate {m} (xs : Fin 5 → Fin m) (w r idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeOneBoundVariableNumericIffSentence xs w r idx)) := TheoryTransport.sentence (source_modeOneBoundVariableNumericIff xs w r idx)

theorem native_modeOneBoundVariableNumericIff {m} (xs : Fin 5 → Fin m) (w r idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeOneBoundVariableNumericIffSentence xs w r idx)) := ZFReplay.replay (modeOneBoundVariableNumericIff_kernel_certificate xs w r idx)

def modeOneBoundVariableNumericSoundSentence {m} (xs : Fin 5 → Fin m) (w r idx : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNodeSyntax.constructor 5 1 w xs r).imp ((SyntaxNumeralSyntax.numeral 1 (xs 0)).imp ((SyntaxVariableSyntax.code true w idx (xs 3)).imp ((HornLookupConditionSyntax.condition w r).imp ((AbstractVariableValueSyntax.boundValue w (xs 1) idx (xs 3) (xs 4)))))))).close

theorem source_modeOneBoundVariableNumericSound {m} (xs : Fin 5 → Fin m) (w r idx : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeOneBoundVariableNumericSoundSentence xs w r idx) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornLookupConditionSyntax.condition w r) (Context.add (SyntaxVariableSyntax.code true w idx (xs 3)) (Context.add (SyntaxNumeralSyntax.numeral 1 (xs 0)) (Context.add (SyntaxNodeSyntax.constructor 5 1 w xs r) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxNodeSyntax.constructor 5 1 w xs r) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral 1 (xs 0)) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (SyntaxVariableSyntax.code true w idx (xs 3)) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (HornLookupConditionSyntax.condition w r) := .hyp (Or.inl rfl)
  exact AbstractVariableNumeric.bound_sound hZ w r idx xs h0 h1 h2 h3 h4

theorem modeOneBoundVariableNumericSound_kernel_certificate {m} (xs : Fin 5 → Fin m) (w r idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeOneBoundVariableNumericSoundSentence xs w r idx)) := TheoryTransport.sentence (source_modeOneBoundVariableNumericSound xs w r idx)

theorem native_modeOneBoundVariableNumericSound {m} (xs : Fin 5 → Fin m) (w r idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeOneBoundVariableNumericSoundSentence xs w r idx)) := ZFReplay.replay (modeOneBoundVariableNumericSound_kernel_certificate xs w r idx)

def modeOneBoundVariableNumericCompleteSentence {m} (xs : Fin 5 → Fin m) (w r idx : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNodeSyntax.constructor 5 1 w xs r).imp ((SyntaxNumeralSyntax.numeral 1 (xs 0)).imp ((SyntaxVariableSyntax.code true w idx (xs 3)).imp ((AbstractVariableValueSyntax.boundValue w (xs 1) idx (xs 3) (xs 4)).imp ((HornLookupConditionSyntax.condition w r))))))).close

theorem source_modeOneBoundVariableNumericComplete {m} (xs : Fin 5 → Fin m) (w r idx : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeOneBoundVariableNumericCompleteSentence xs w r idx) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (AbstractVariableValueSyntax.boundValue w (xs 1) idx (xs 3) (xs 4)) (Context.add (SyntaxVariableSyntax.code true w idx (xs 3)) (Context.add (SyntaxNumeralSyntax.numeral 1 (xs 0)) (Context.add (SyntaxNodeSyntax.constructor 5 1 w xs r) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxNodeSyntax.constructor 5 1 w xs r) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral 1 (xs 0)) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (SyntaxVariableSyntax.code true w idx (xs 3)) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (AbstractVariableValueSyntax.boundValue w (xs 1) idx (xs 3) (xs 4)) := .hyp (Or.inl rfl)
  exact AbstractVariableNumeric.bound_complete hZ w r idx xs h0 h1 h2 h3 h4

theorem modeOneBoundVariableNumericComplete_kernel_certificate {m} (xs : Fin 5 → Fin m) (w r idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeOneBoundVariableNumericCompleteSentence xs w r idx)) := TheoryTransport.sentence (source_modeOneBoundVariableNumericComplete xs w r idx)

theorem native_modeOneBoundVariableNumericComplete {m} (xs : Fin 5 → Fin m) (w r idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeOneBoundVariableNumericCompleteSentence xs w r idx)) := ZFReplay.replay (modeOneBoundVariableNumericComplete_kernel_certificate xs w r idx)

def modeOneFreeVariableNumericIffSentence {m} (xs : Fin 5 → Fin m) (w r idx : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNodeSyntax.constructor 5 1 w xs r).imp ((SyntaxNumeralSyntax.numeral 1 (xs 0)).imp ((SyntaxVariableSyntax.code false w idx (xs 3)).imp (((HornLookupConditionSyntax.condition w r).iff (AbstractVariableValueSyntax.freeValue w (xs 1) idx (xs 4)))))))).close

theorem source_modeOneFreeVariableNumericIff {m} (xs : Fin 5 → Fin m) (w r idx : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeOneFreeVariableNumericIffSentence xs w r idx) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxVariableSyntax.code false w idx (xs 3)) (Context.add (SyntaxNumeralSyntax.numeral 1 (xs 0)) (Context.add (SyntaxNodeSyntax.constructor 5 1 w xs r) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNodeSyntax.constructor 5 1 w xs r) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral 1 (xs 0)) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxVariableSyntax.code false w idx (xs 3)) := .hyp (Or.inl rfl)
  exact AbstractVariableNumeric.free_iff hZ w r idx xs h0 h1 h2 h3

theorem modeOneFreeVariableNumericIff_kernel_certificate {m} (xs : Fin 5 → Fin m) (w r idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeOneFreeVariableNumericIffSentence xs w r idx)) := TheoryTransport.sentence (source_modeOneFreeVariableNumericIff xs w r idx)

theorem native_modeOneFreeVariableNumericIff {m} (xs : Fin 5 → Fin m) (w r idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeOneFreeVariableNumericIffSentence xs w r idx)) := ZFReplay.replay (modeOneFreeVariableNumericIff_kernel_certificate xs w r idx)

def modeOneFreeVariableNumericSoundSentence {m} (xs : Fin 5 → Fin m) (w r idx : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNodeSyntax.constructor 5 1 w xs r).imp ((SyntaxNumeralSyntax.numeral 1 (xs 0)).imp ((SyntaxVariableSyntax.code false w idx (xs 3)).imp ((HornLookupConditionSyntax.condition w r).imp ((AbstractVariableValueSyntax.freeValue w (xs 1) idx (xs 4)))))))).close

theorem source_modeOneFreeVariableNumericSound {m} (xs : Fin 5 → Fin m) (w r idx : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeOneFreeVariableNumericSoundSentence xs w r idx) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornLookupConditionSyntax.condition w r) (Context.add (SyntaxVariableSyntax.code false w idx (xs 3)) (Context.add (SyntaxNumeralSyntax.numeral 1 (xs 0)) (Context.add (SyntaxNodeSyntax.constructor 5 1 w xs r) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxNodeSyntax.constructor 5 1 w xs r) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral 1 (xs 0)) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (SyntaxVariableSyntax.code false w idx (xs 3)) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (HornLookupConditionSyntax.condition w r) := .hyp (Or.inl rfl)
  exact AbstractVariableNumeric.free_sound hZ w r idx xs h0 h1 h2 h3 h4

theorem modeOneFreeVariableNumericSound_kernel_certificate {m} (xs : Fin 5 → Fin m) (w r idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeOneFreeVariableNumericSoundSentence xs w r idx)) := TheoryTransport.sentence (source_modeOneFreeVariableNumericSound xs w r idx)

theorem native_modeOneFreeVariableNumericSound {m} (xs : Fin 5 → Fin m) (w r idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeOneFreeVariableNumericSoundSentence xs w r idx)) := ZFReplay.replay (modeOneFreeVariableNumericSound_kernel_certificate xs w r idx)

def modeOneFreeVariableNumericCompleteSentence {m} (xs : Fin 5 → Fin m) (w r idx : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNodeSyntax.constructor 5 1 w xs r).imp ((SyntaxNumeralSyntax.numeral 1 (xs 0)).imp ((SyntaxVariableSyntax.code false w idx (xs 3)).imp ((AbstractVariableValueSyntax.freeValue w (xs 1) idx (xs 4)).imp ((HornLookupConditionSyntax.condition w r))))))).close

theorem source_modeOneFreeVariableNumericComplete {m} (xs : Fin 5 → Fin m) (w r idx : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeOneFreeVariableNumericCompleteSentence xs w r idx) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (AbstractVariableValueSyntax.freeValue w (xs 1) idx (xs 4)) (Context.add (SyntaxVariableSyntax.code false w idx (xs 3)) (Context.add (SyntaxNumeralSyntax.numeral 1 (xs 0)) (Context.add (SyntaxNodeSyntax.constructor 5 1 w xs r) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxNodeSyntax.constructor 5 1 w xs r) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral 1 (xs 0)) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (SyntaxVariableSyntax.code false w idx (xs 3)) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (AbstractVariableValueSyntax.freeValue w (xs 1) idx (xs 4)) := .hyp (Or.inl rfl)
  exact AbstractVariableNumeric.free_complete hZ w r idx xs h0 h1 h2 h3 h4

theorem modeOneFreeVariableNumericComplete_kernel_certificate {m} (xs : Fin 5 → Fin m) (w r idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeOneFreeVariableNumericCompleteSentence xs w r idx)) := TheoryTransport.sentence (source_modeOneFreeVariableNumericComplete xs w r idx)

theorem native_modeOneFreeVariableNumericComplete {m} (xs : Fin 5 → Fin m) (w r idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeOneFreeVariableNumericCompleteSentence xs w r idx)) := ZFReplay.replay (modeOneFreeVariableNumericComplete_kernel_certificate xs w r idx)

def modeOneAllVariableNumericTraceIffSentence {m} (bound : Bool) (xs : Fin 5 → Fin m) (w r idx : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNodeSyntax.constructor 5 1 w xs r).imp ((SyntaxNumeralSyntax.numeral 1 (xs 0)).imp ((SyntaxVariableSyntax.code bound w idx (xs 3)).imp (((HornLookupConditionSyntax.condition w r).iff (AbstractVariableValueSyntax.valueSpec bound w (xs 1) idx (xs 3) (xs 4)))))))).close

theorem source_modeOneAllVariableNumericTraceIff {m} (bound : Bool) (xs : Fin 5 → Fin m) (w r idx : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeOneAllVariableNumericTraceIffSentence bound xs w r idx) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxVariableSyntax.code bound w idx (xs 3)) (Context.add (SyntaxNumeralSyntax.numeral 1 (xs 0)) (Context.add (SyntaxNodeSyntax.constructor 5 1 w xs r) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNodeSyntax.constructor 5 1 w xs r) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral 1 (xs 0)) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxVariableSyntax.code bound w idx (xs 3)) := .hyp (Or.inl rfl)
  exact AbstractVariableRun.trace_iff_value hZ bound w r idx xs h0 h1 h2 h3

theorem modeOneAllVariableNumericTraceIff_kernel_certificate {m} (bound : Bool) (xs : Fin 5 → Fin m) (w r idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeOneAllVariableNumericTraceIffSentence bound xs w r idx)) := TheoryTransport.sentence (source_modeOneAllVariableNumericTraceIff bound xs w r idx)

theorem native_modeOneAllVariableNumericTraceIff {m} (bound : Bool) (xs : Fin 5 → Fin m) (w r idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeOneAllVariableNumericTraceIffSentence bound xs w r idx)) := ZFReplay.replay (modeOneAllVariableNumericTraceIff_kernel_certificate bound xs w r idx)

def modeOneAllVariableNumericRunIffSentence {m} (bound : Bool) (w mode depth P x idx y : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 1 mode).imp ((OriginalTermTraceSyntax.metadata w depth P).imp ((SyntaxVariableSyntax.code bound w idx x).imp (((OriginalTransformRowSyntax.run 1 w mode depth P x y).iff (AbstractVariableValueSyntax.valueSpec bound w depth idx x y))))))).close

theorem source_modeOneAllVariableNumericRunIff {m} (bound : Bool) (w mode depth P x idx y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeOneAllVariableNumericRunIffSentence bound w mode depth P x idx y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxVariableSyntax.code bound w idx x) (Context.add (OriginalTermTraceSyntax.metadata w depth P) (Context.add (SyntaxNumeralSyntax.numeral 1 mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 1 mode) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (OriginalTermTraceSyntax.metadata w depth P) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxVariableSyntax.code bound w idx x) := .hyp (Or.inl rfl)
  exact AbstractVariableRun.run_iff hZ bound w mode depth P x idx y h0 h1 h2 h3

theorem modeOneAllVariableNumericRunIff_kernel_certificate {m} (bound : Bool) (w mode depth P x idx y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeOneAllVariableNumericRunIffSentence bound w mode depth P x idx y)) := TheoryTransport.sentence (source_modeOneAllVariableNumericRunIff bound w mode depth P x idx y)

theorem native_modeOneAllVariableNumericRunIff {m} (bound : Bool) (w mode depth P x idx y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeOneAllVariableNumericRunIffSentence bound w mode depth P x idx y)) := ZFReplay.replay (modeOneAllVariableNumericRunIff_kernel_certificate bound w mode depth P x idx y)

def modeOneVariableNumericOutputNaturalSentence {m} (bound : Bool) (w d i x y : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem x w).imp ((AbstractVariableValueSyntax.valueSpec bound w d i x y).imp ((Formula.mem y w))))).close

theorem source_modeOneVariableNumericOutputNatural {m} (bound : Bool) (w d i x y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeOneVariableNumericOutputNaturalSentence bound w d i x y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (AbstractVariableValueSyntax.valueSpec bound w d i x y) (Context.add (Formula.mem x w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (Formula.mem x w) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (AbstractVariableValueSyntax.valueSpec bound w d i x y) := .hyp (Or.inl rfl)
  exact AbstractVariableRun.output_natural hZ bound w d i x y h0 h1 h2

theorem modeOneVariableNumericOutputNatural_kernel_certificate {m} (bound : Bool) (w d i x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeOneVariableNumericOutputNaturalSentence bound w d i x y)) := TheoryTransport.sentence (source_modeOneVariableNumericOutputNatural bound w d i x y)

theorem native_modeOneVariableNumericOutputNatural {m} (bound : Bool) (w d i x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeOneVariableNumericOutputNaturalSentence bound w d i x y)) := ZFReplay.replay (modeOneVariableNumericOutputNatural_kernel_certificate bound w d i x y)

def modeOnePreservedValueConstructsTraceSentence {m} (xs : Fin 5 → Fin m) (w r idx : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNodeSyntax.constructor 5 1 w xs r).imp ((SyntaxNumeralSyntax.numeral 1 (xs 0)).imp ((SyntaxVariableSyntax.code true w idx (xs 3)).imp ((Formula.mem idx (xs 1)).imp ((Formula.equal (xs 4) (xs 3)).imp ((HornLookupConditionSyntax.condition w r)))))))).close

theorem source_modeOnePreservedValueConstructsTrace {m} (xs : Fin 5 → Fin m) (w r idx : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeOnePreservedValueConstructsTraceSentence xs w r idx) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.equal (xs 4) (xs 3)) (Context.add (Formula.mem idx (xs 1)) (Context.add (SyntaxVariableSyntax.code true w idx (xs 3)) (Context.add (SyntaxNumeralSyntax.numeral 1 (xs 0)) (Context.add (SyntaxNodeSyntax.constructor 5 1 w xs r) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (SyntaxNodeSyntax.constructor 5 1 w xs r) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral 1 (xs 0)) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (SyntaxVariableSyntax.code true w idx (xs 3)) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (Formula.mem idx (xs 1)) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (Formula.equal (xs 4) (xs 3)) := .hyp (Or.inl rfl)
  exact AbstractVariableComplete.bound_preserved hZ w r idx xs h0 h1 h2 h3 h4 h5

theorem modeOnePreservedValueConstructsTrace_kernel_certificate {m} (xs : Fin 5 → Fin m) (w r idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeOnePreservedValueConstructsTraceSentence xs w r idx)) := TheoryTransport.sentence (source_modeOnePreservedValueConstructsTrace xs w r idx)

theorem native_modeOnePreservedValueConstructsTrace {m} (xs : Fin 5 → Fin m) (w r idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeOnePreservedValueConstructsTraceSentence xs w r idx)) := ZFReplay.replay (modeOnePreservedValueConstructsTrace_kernel_certificate xs w r idx)

def modeOneShiftedValueConstructsTraceSentence {m} (xs : Fin 5 → Fin m) (w r idx s : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNodeSyntax.constructor 5 1 w xs r).imp ((SyntaxNumeralSyntax.numeral 1 (xs 0)).imp ((SyntaxVariableSyntax.code true w idx (xs 3)).imp ((successor s idx).imp ((Formula.mem (xs 1) s).imp ((SyntaxVariableSyntax.code true w s (xs 4)).imp ((HornLookupConditionSyntax.condition w r))))))))).close

theorem source_modeOneShiftedValueConstructsTrace {m} (xs : Fin 5 → Fin m) (w r idx s : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeOneShiftedValueConstructsTraceSentence xs w r idx s) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxVariableSyntax.code true w s (xs 4)) (Context.add (Formula.mem (xs 1) s) (Context.add (successor s idx) (Context.add (SyntaxVariableSyntax.code true w idx (xs 3)) (Context.add (SyntaxNumeralSyntax.numeral 1 (xs 0)) (Context.add (SyntaxNodeSyntax.constructor 5 1 w xs r) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))
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
  have h1 : Derives Δ (SyntaxNodeSyntax.constructor 5 1 w xs r) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral 1 (xs 0)) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h3 : Derives Δ (SyntaxVariableSyntax.code true w idx (xs 3)) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : Derives Δ (successor s idx) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h5 : Derives Δ (Formula.mem (xs 1) s) := .hyp (Or.inr (Or.inl rfl))
  have h6 : Derives Δ (SyntaxVariableSyntax.code true w s (xs 4)) := .hyp (Or.inl rfl)
  exact AbstractVariableComplete.bound_shifted hZ w r idx s xs h0 h1 h2 h3 h4 h5 h6

theorem modeOneShiftedValueConstructsTrace_kernel_certificate {m} (xs : Fin 5 → Fin m) (w r idx s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeOneShiftedValueConstructsTraceSentence xs w r idx s)) := TheoryTransport.sentence (source_modeOneShiftedValueConstructsTrace xs w r idx s)

theorem native_modeOneShiftedValueConstructsTrace {m} (xs : Fin 5 → Fin m) (w r idx s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeOneShiftedValueConstructsTraceSentence xs w r idx s)) := ZFReplay.replay (modeOneShiftedValueConstructsTrace_kernel_certificate xs w r idx s)

def modeOneFreeHeadValueConstructsTraceSentence {m} (xs : Fin 5 → Fin m) (w r idx : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNodeSyntax.constructor 5 1 w xs r).imp ((SyntaxNumeralSyntax.numeral 1 (xs 0)).imp ((SyntaxVariableSyntax.code false w idx (xs 3)).imp ((empty idx).imp ((SyntaxVariableSyntax.code true w (xs 1) (xs 4)).imp ((HornLookupConditionSyntax.condition w r)))))))).close

theorem source_modeOneFreeHeadValueConstructsTrace {m} (xs : Fin 5 → Fin m) (w r idx : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeOneFreeHeadValueConstructsTraceSentence xs w r idx) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxVariableSyntax.code true w (xs 1) (xs 4)) (Context.add (empty idx) (Context.add (SyntaxVariableSyntax.code false w idx (xs 3)) (Context.add (SyntaxNumeralSyntax.numeral 1 (xs 0)) (Context.add (SyntaxNodeSyntax.constructor 5 1 w xs r) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (SyntaxNodeSyntax.constructor 5 1 w xs r) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral 1 (xs 0)) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (SyntaxVariableSyntax.code false w idx (xs 3)) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (empty idx) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (SyntaxVariableSyntax.code true w (xs 1) (xs 4)) := .hyp (Or.inl rfl)
  exact AbstractVariableComplete.free_head hZ w r idx xs h0 h1 h2 h3 h4 h5

theorem modeOneFreeHeadValueConstructsTrace_kernel_certificate {m} (xs : Fin 5 → Fin m) (w r idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeOneFreeHeadValueConstructsTraceSentence xs w r idx)) := TheoryTransport.sentence (source_modeOneFreeHeadValueConstructsTrace xs w r idx)

theorem native_modeOneFreeHeadValueConstructsTrace {m} (xs : Fin 5 → Fin m) (w r idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeOneFreeHeadValueConstructsTraceSentence xs w r idx)) := ZFReplay.replay (modeOneFreeHeadValueConstructsTrace_kernel_certificate xs w r idx)

def modeOneFreeTailValueConstructsTraceSentence {m} (xs : Fin 5 → Fin m) (w r idx k : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNodeSyntax.constructor 5 1 w xs r).imp ((SyntaxNumeralSyntax.numeral 1 (xs 0)).imp ((SyntaxVariableSyntax.code false w idx (xs 3)).imp ((successor idx k).imp ((SyntaxVariableSyntax.code false w k (xs 4)).imp ((HornLookupConditionSyntax.condition w r)))))))).close

theorem source_modeOneFreeTailValueConstructsTrace {m} (xs : Fin 5 → Fin m) (w r idx k : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeOneFreeTailValueConstructsTraceSentence xs w r idx k) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxVariableSyntax.code false w k (xs 4)) (Context.add (successor idx k) (Context.add (SyntaxVariableSyntax.code false w idx (xs 3)) (Context.add (SyntaxNumeralSyntax.numeral 1 (xs 0)) (Context.add (SyntaxNodeSyntax.constructor 5 1 w xs r) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (SyntaxNodeSyntax.constructor 5 1 w xs r) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral 1 (xs 0)) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (SyntaxVariableSyntax.code false w idx (xs 3)) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (successor idx k) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (SyntaxVariableSyntax.code false w k (xs 4)) := .hyp (Or.inl rfl)
  exact AbstractVariableComplete.free_tail hZ w r idx k xs h0 h1 h2 h3 h4 h5

theorem modeOneFreeTailValueConstructsTrace_kernel_certificate {m} (xs : Fin 5 → Fin m) (w r idx k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeOneFreeTailValueConstructsTraceSentence xs w r idx k)) := TheoryTransport.sentence (source_modeOneFreeTailValueConstructsTrace xs w r idx k)

theorem native_modeOneFreeTailValueConstructsTrace {m} (xs : Fin 5 → Fin m) (w r idx k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeOneFreeTailValueConstructsTraceSentence xs w r idx k)) := ZFReplay.replay (modeOneFreeTailValueConstructsTrace_kernel_certificate xs w r idx k)

end PPAC.Migration.Internal.ObjectAbstractVariable
