import PPAC.Migration.Internal.HornExprBounds

/-! 上游原Horn表达式的全部内部求值及真实lookup局部矩阵的原YesMetaZFC核证书。 -/
namespace PPAC.Migration.Internal.ObjectOriginalLookupRules
open Source SourceAlgebra SourceLogic OmegaSyntax

def expressionActualValueSentence {m} {n} (e : YesMetaZFC.Automation.ObjectHorn.Expr n) (env : Fin n → Fin m) (w : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat n w env).imp ((HornExprSyntax.existsValue e w env)))).close

theorem source_expressionActualValue {m} {n} (e : YesMetaZFC.Automation.ObjectHorn.Expr n) (env : Fin n → Fin m) (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (expressionActualValueSentence e env w) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.environmentNat n w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (HornExprSyntax.environmentNat n w env) := .hyp (Or.inl rfl)
  exact HornExprExistence.exists_value hZ e w env h0 h1

theorem expressionActualValue_kernel_certificate {m} {n} (e : YesMetaZFC.Automation.ObjectHorn.Expr n) (env : Fin n → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (expressionActualValueSentence e env w)) := TheoryTransport.sentence (source_expressionActualValue e env w)

theorem native_expressionActualValue {m} {n} (e : YesMetaZFC.Automation.ObjectHorn.Expr n) (env : Fin n → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (expressionActualValueSentence e env w)) := ZFReplay.replay (expressionActualValue_kernel_certificate e env w)

def expressionNaturalRangeSentence {m} {n} (e : YesMetaZFC.Automation.ObjectHorn.Expr n) (env : Fin n → Fin m) (w y : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat n w env).imp ((HornExprSyntax.graph e w env y).imp ((Formula.mem y w))))).close

theorem source_expressionNaturalRange {m} {n} (e : YesMetaZFC.Automation.ObjectHorn.Expr n) (env : Fin n → Fin m) (w y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (expressionNaturalRangeSentence e env w y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.graph e w env y) (Context.add (HornExprSyntax.environmentNat n w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat n w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (HornExprSyntax.graph e w env y) := .hyp (Or.inl rfl)
  exact HornExprRange.range hZ e w y env h0 h1 h2

theorem expressionNaturalRange_kernel_certificate {m} {n} (e : YesMetaZFC.Automation.ObjectHorn.Expr n) (env : Fin n → Fin m) (w y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (expressionNaturalRangeSentence e env w y)) := TheoryTransport.sentence (source_expressionNaturalRange e env w y)

theorem native_expressionNaturalRange {m} {n} (e : YesMetaZFC.Automation.ObjectHorn.Expr n) (env : Fin n → Fin m) (w y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (expressionNaturalRangeSentence e env w y)) := ZFReplay.replay (expressionNaturalRange_kernel_certificate e env w y)

def expressionActualUniqueFiberSentence {m} {n} (e : YesMetaZFC.Automation.ObjectHorn.Expr n) (env : Fin n → Fin m) (w : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat n w env).imp ((HornExprSyntax.fiber e w env)))).close

theorem source_expressionActualUniqueFiber {m} {n} (e : YesMetaZFC.Automation.ObjectHorn.Expr n) (env : Fin n → Fin m) (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (expressionActualUniqueFiberSentence e env w) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.environmentNat n w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (HornExprSyntax.environmentNat n w env) := .hyp (Or.inl rfl)
  exact HornExprValue.actual_fiber hZ e w env h0 h1

theorem expressionActualUniqueFiber_kernel_certificate {m} {n} (e : YesMetaZFC.Automation.ObjectHorn.Expr n) (env : Fin n → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (expressionActualUniqueFiberSentence e env w)) := TheoryTransport.sentence (source_expressionActualUniqueFiber e env w)

theorem native_expressionActualUniqueFiber {m} {n} (e : YesMetaZFC.Automation.ObjectHorn.Expr n) (env : Fin n → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (expressionActualUniqueFiberSentence e env w)) := ZFReplay.replay (expressionActualUniqueFiber_kernel_certificate e env w)

def expressionUniqueValueSentence {m} {n} (e : YesMetaZFC.Automation.ObjectHorn.Expr n) (env : Fin n → Fin m) (w y : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat n w env).imp ((HornExprSyntax.graph e w env y).imp ((HornExprSyntax.uniqueValue e w env y))))).close

theorem source_expressionUniqueValue {m} {n} (e : YesMetaZFC.Automation.ObjectHorn.Expr n) (env : Fin n → Fin m) (w y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (expressionUniqueValueSentence e env w y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.graph e w env y) (Context.add (HornExprSyntax.environmentNat n w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat n w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (HornExprSyntax.graph e w env y) := .hyp (Or.inl rfl)
  exact HornExprValue.unique_value hZ e w y env h0 h1 h2

theorem expressionUniqueValue_kernel_certificate {m} {n} (e : YesMetaZFC.Automation.ObjectHorn.Expr n) (env : Fin n → Fin m) (w y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (expressionUniqueValueSentence e env w y)) := TheoryTransport.sentence (source_expressionUniqueValue e env w y)

theorem native_expressionUniqueValue {m} {n} (e : YesMetaZFC.Automation.ObjectHorn.Expr n) (env : Fin n → Fin m) (w y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (expressionUniqueValueSentence e env w y)) := ZFReplay.replay (expressionUniqueValue_kernel_certificate e env w y)

def expressionCandidateIffSentence {m} {n} (e : YesMetaZFC.Automation.ObjectHorn.Expr n) (env : Fin n → Fin m) (w y z : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat n w env).imp ((HornExprSyntax.graph e w env y).imp (((HornExprSyntax.graph e w env z).iff (.equal z y)))))).close

theorem source_expressionCandidateIff {m} {n} (e : YesMetaZFC.Automation.ObjectHorn.Expr n) (env : Fin n → Fin m) (w y z : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (expressionCandidateIffSentence e env w y z) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.graph e w env y) (Context.add (HornExprSyntax.environmentNat n w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat n w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (HornExprSyntax.graph e w env y) := .hyp (Or.inl rfl)
  exact HornExprValue.at_value hZ e w y z env h0 h1 h2

theorem expressionCandidateIff_kernel_certificate {m} {n} (e : YesMetaZFC.Automation.ObjectHorn.Expr n) (env : Fin n → Fin m) (w y z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (expressionCandidateIffSentence e env w y z)) := TheoryTransport.sentence (source_expressionCandidateIff e env w y z)

theorem native_expressionCandidateIff {m} {n} (e : YesMetaZFC.Automation.ObjectHorn.Expr n) (env : Fin n → Fin m) (w y z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (expressionCandidateIffSentence e env w y z)) := ZFReplay.replay (expressionCandidateIff_kernel_certificate e env w y z)

def rawExpressionIffSentence {m} {n} (e f : YesMetaZFC.Automation.ObjectHorn.Expr n) (env : Fin n → Fin m) (w a b y : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat n w env).imp ((HornExprSyntax.graph e w env a).imp ((HornExprSyntax.graph f w env b).imp (((HornExprSyntax.graph (.succ (.pair e f)) w env y).iff (StructuralNodeSyntax.raw w a b y))))))).close

theorem source_rawExpressionIff {m} {n} (e f : YesMetaZFC.Automation.ObjectHorn.Expr n) (env : Fin n → Fin m) (w a b y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (rawExpressionIffSentence e f env w a b y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.graph f w env b) (Context.add (HornExprSyntax.graph e w env a) (Context.add (HornExprSyntax.environmentNat n w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (HornExprSyntax.environmentNat n w env) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (HornExprSyntax.graph e w env a) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (HornExprSyntax.graph f w env b) := .hyp (Or.inl rfl)
  exact HornExprStructural.raw_iff hZ e f w a b y env h0 h1 h2 h3

theorem rawExpressionIff_kernel_certificate {m} {n} (e f : YesMetaZFC.Automation.ObjectHorn.Expr n) (env : Fin n → Fin m) (w a b y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (rawExpressionIffSentence e f env w a b y)) := TheoryTransport.sentence (source_rawExpressionIff e f env w a b y)

theorem native_rawExpressionIff {m} {n} (e f : YesMetaZFC.Automation.ObjectHorn.Expr n) (env : Fin n → Fin m) (w a b y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (rawExpressionIffSentence e f env w a b y)) := ZFReplay.replay (rawExpressionIff_kernel_certificate e f env w a b y)

def consExpressionIffSentence {m} {n} (e f : YesMetaZFC.Automation.ObjectHorn.Expr n) (env : Fin n → Fin m) (w a b y : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat n w env).imp ((HornExprSyntax.graph e w env a).imp ((HornExprSyntax.graph f w env b).imp (((HornExprSyntax.graph (YesMetaZFC.Automation.ObjectSyntaxTransform.cons e f) w env y).iff (StructuralListSyntax.consCode w a b y))))))).close

theorem source_consExpressionIff {m} {n} (e f : YesMetaZFC.Automation.ObjectHorn.Expr n) (env : Fin n → Fin m) (w a b y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (consExpressionIffSentence e f env w a b y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.graph f w env b) (Context.add (HornExprSyntax.graph e w env a) (Context.add (HornExprSyntax.environmentNat n w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (HornExprSyntax.environmentNat n w env) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (HornExprSyntax.graph e w env a) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (HornExprSyntax.graph f w env b) := .hyp (Or.inl rfl)
  exact HornExprStructural.cons_iff hZ e f w a b y env h0 h1 h2 h3

theorem consExpressionIff_kernel_certificate {m} {n} (e f : YesMetaZFC.Automation.ObjectHorn.Expr n) (env : Fin n → Fin m) (w a b y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (consExpressionIffSentence e f env w a b y)) := TheoryTransport.sentence (source_consExpressionIff e f env w a b y)

theorem native_consExpressionIff {m} {n} (e f : YesMetaZFC.Automation.ObjectHorn.Expr n) (env : Fin n → Fin m) (w a b y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (consExpressionIffSentence e f env w a b y)) := ZFReplay.replay (consExpressionIff_kernel_certificate e f env w a b y)

def premiseAtValueSentence {m} {n} (e : YesMetaZFC.Automation.ObjectHorn.Expr n) (env : Fin n → Fin m) (w trace y : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat n w env).imp ((HornExprSyntax.graph e w env y).imp (((HornRuleSyntax.premise e w trace env).iff (.mem y trace)))))).close

theorem source_premiseAtValue {m} {n} (e : YesMetaZFC.Automation.ObjectHorn.Expr n) (env : Fin n → Fin m) (w trace y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (premiseAtValueSentence e env w trace y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.graph e w env y) (Context.add (HornExprSyntax.environmentNat n w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat n w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (HornExprSyntax.graph e w env y) := .hyp (Or.inl rfl)
  exact HornRuleValue.premise_at hZ e w trace y env h0 h1 h2

theorem premiseAtValue_kernel_certificate {m} {n} (e : YesMetaZFC.Automation.ObjectHorn.Expr n) (env : Fin n → Fin m) (w trace y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (premiseAtValueSentence e env w trace y)) := TheoryTransport.sentence (source_premiseAtValue e env w trace y)

theorem native_premiseAtValue {m} {n} (e : YesMetaZFC.Automation.ObjectHorn.Expr n) (env : Fin n → Fin m) (w trace y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (premiseAtValueSentence e env w trace y)) := ZFReplay.replay (premiseAtValue_kernel_certificate e env w trace y)

def guardAtValuesSentence {m} {n} (e f : YesMetaZFC.Automation.ObjectHorn.Expr n) (env : Fin n → Fin m) (w a b : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat n w env).imp ((HornExprSyntax.graph e w env a).imp ((HornExprSyntax.graph f w env b).imp (((HornRuleSyntax.guard e f w env).iff (.mem a b))))))).close

theorem source_guardAtValues {m} {n} (e f : YesMetaZFC.Automation.ObjectHorn.Expr n) (env : Fin n → Fin m) (w a b : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (guardAtValuesSentence e f env w a b) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.graph f w env b) (Context.add (HornExprSyntax.graph e w env a) (Context.add (HornExprSyntax.environmentNat n w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (HornExprSyntax.environmentNat n w env) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (HornExprSyntax.graph e w env a) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (HornExprSyntax.graph f w env b) := .hyp (Or.inl rfl)
  exact HornRuleValue.guard_at hZ e f w a b env h0 h1 h2 h3

theorem guardAtValues_kernel_certificate {m} {n} (e f : YesMetaZFC.Automation.ObjectHorn.Expr n) (env : Fin n → Fin m) (w a b : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (guardAtValuesSentence e f env w a b)) := TheoryTransport.sentence (source_guardAtValues e f env w a b)

theorem native_guardAtValues {m} {n} (e f : YesMetaZFC.Automation.ObjectHorn.Expr n) (env : Fin n → Fin m) (w a b : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (guardAtValuesSentence e f env w a b)) := ZFReplay.replay (guardAtValues_kernel_certificate e f env w a b)

def originalLookupHeadExpressionIffSentence {m} (env : Fin 2 → Fin m) (w n z row : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 2 w env).imp ((StructuralListSyntax.consCode w (env 0) (env 1) n).imp ((empty z).imp (((HornExprSyntax.graph YesMetaZFC.Automation.ObjectSyntaxTransform.lookupHead.head w env row).iff (SyntaxNodeSyntax.constructor 3 0 w (OriginalLookupExpr.rowFields n z (env 0)) row))))))).close

theorem source_originalLookupHeadExpressionIff {m} (env : Fin 2 → Fin m) (w n z row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalLookupHeadExpressionIffSentence env w n z row) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (empty z) (Context.add (StructuralListSyntax.consCode w (env 0) (env 1) n) (Context.add (HornExprSyntax.environmentNat 2 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 2 w env) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (StructuralListSyntax.consCode w (env 0) (env 1) n) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (empty z) := .hyp (Or.inl rfl)
  exact OriginalLookupExpr.head_iff hZ w n z row env h0 h1 h2 h3

theorem originalLookupHeadExpressionIff_kernel_certificate {m} (env : Fin 2 → Fin m) (w n z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalLookupHeadExpressionIffSentence env w n z row)) := TheoryTransport.sentence (source_originalLookupHeadExpressionIff env w n z row)

theorem native_originalLookupHeadExpressionIff {m} (env : Fin 2 → Fin m) (w n z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalLookupHeadExpressionIffSentence env w n z row)) := ZFReplay.replay (originalLookupHeadExpressionIff_kernel_certificate env w n z row)

def originalLookupTailExpressionIffSentence {m} (env : Fin 4 → Fin m) (w n s row : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 4 w env).imp ((StructuralListSyntax.consCode w (env 0) (env 1) n).imp ((successor s (env 2)).imp (((HornExprSyntax.graph YesMetaZFC.Automation.ObjectSyntaxTransform.lookupTail.head w env row).iff (SyntaxNodeSyntax.constructor 3 0 w (OriginalLookupExpr.rowFields n s (env 3)) row))))))).close

theorem source_originalLookupTailExpressionIff {m} (env : Fin 4 → Fin m) (w n s row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalLookupTailExpressionIffSentence env w n s row) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor s (env 2)) (Context.add (StructuralListSyntax.consCode w (env 0) (env 1) n) (Context.add (HornExprSyntax.environmentNat 4 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 4 w env) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (StructuralListSyntax.consCode w (env 0) (env 1) n) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (successor s (env 2)) := .hyp (Or.inl rfl)
  exact OriginalLookupExpr.tail_iff hZ w n s row env h0 h1 h2 h3

theorem originalLookupTailExpressionIff_kernel_certificate {m} (env : Fin 4 → Fin m) (w n s row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalLookupTailExpressionIffSentence env w n s row)) := TheoryTransport.sentence (source_originalLookupTailExpressionIff env w n s row)

theorem native_originalLookupTailExpressionIff {m} (env : Fin 4 → Fin m) (w n s row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalLookupTailExpressionIffSentence env w n s row)) := ZFReplay.replay (originalLookupTailExpressionIff_kernel_certificate env w n s row)

def originalLookupPremiseExpressionIffSentence {m} (env : Fin 4 → Fin m) (w row : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 4 w env).imp (((HornExprSyntax.graph OriginalLookupExpr.premiseExpr w env row).iff (SyntaxNodeSyntax.constructor 3 0 w (OriginalLookupExpr.rowFields (env 1) (env 2) (env 3)) row))))).close

theorem source_originalLookupPremiseExpressionIff {m} (env : Fin 4 → Fin m) (w row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalLookupPremiseExpressionIffSentence env w row) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.environmentNat 4 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 4 w env) := .hyp (Or.inl rfl)
  exact OriginalLookupExpr.premise_iff hZ w row env h0 h1

theorem originalLookupPremiseExpressionIff_kernel_certificate {m} (env : Fin 4 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalLookupPremiseExpressionIffSentence env w row)) := TheoryTransport.sentence (source_originalLookupPremiseExpressionIff env w row)

theorem native_originalLookupPremiseExpressionIff {m} (env : Fin 4 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalLookupPremiseExpressionIffSentence env w row)) := ZFReplay.replay (originalLookupPremiseExpressionIff_kernel_certificate env w row)

def originalLookupHeadMatrixIffSentence {m} (env : Fin 2 → Fin m) (w n z row trace : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 2 w env).imp ((StructuralListSyntax.consCode w (env 0) (env 1) n).imp ((empty z).imp (((HornRuleSyntax.matrix YesMetaZFC.Automation.ObjectSyntaxTransform.lookupHead w row trace env).iff (SyntaxNodeSyntax.constructor 3 0 w (OriginalLookupExpr.rowFields n z (env 0)) row))))))).close

theorem source_originalLookupHeadMatrixIff {m} (env : Fin 2 → Fin m) (w n z row trace : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalLookupHeadMatrixIffSentence env w n z row trace) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (empty z) (Context.add (StructuralListSyntax.consCode w (env 0) (env 1) n) (Context.add (HornExprSyntax.environmentNat 2 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 2 w env) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (StructuralListSyntax.consCode w (env 0) (env 1) n) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (empty z) := .hyp (Or.inl rfl)
  exact OriginalLookupRuleMatrix.head_matrix_iff hZ w n z row trace env h0 h1 h2 h3

theorem originalLookupHeadMatrixIff_kernel_certificate {m} (env : Fin 2 → Fin m) (w n z row trace : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalLookupHeadMatrixIffSentence env w n z row trace)) := TheoryTransport.sentence (source_originalLookupHeadMatrixIff env w n z row trace)

theorem native_originalLookupHeadMatrixIff {m} (env : Fin 2 → Fin m) (w n z row trace : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalLookupHeadMatrixIffSentence env w n z row trace)) := ZFReplay.replay (originalLookupHeadMatrixIff_kernel_certificate env w n z row trace)

def originalLookupTailMatrixIffSentence {m} (env : Fin 4 → Fin m) (w n s row trace : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 4 w env).imp ((StructuralListSyntax.consCode w (env 0) (env 1) n).imp ((successor s (env 2)).imp (((HornRuleSyntax.matrix YesMetaZFC.Automation.ObjectSyntaxTransform.lookupTail w row trace env).iff ((SyntaxNodeSyntax.constructor 3 0 w (OriginalLookupExpr.rowFields n s (env 3)) row).conj (OriginalLookupRuleMatrix.childMember w trace env)))))))).close

theorem source_originalLookupTailMatrixIff {m} (env : Fin 4 → Fin m) (w n s row trace : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalLookupTailMatrixIffSentence env w n s row trace) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor s (env 2)) (Context.add (StructuralListSyntax.consCode w (env 0) (env 1) n) (Context.add (HornExprSyntax.environmentNat 4 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 4 w env) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (StructuralListSyntax.consCode w (env 0) (env 1) n) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (successor s (env 2)) := .hyp (Or.inl rfl)
  exact OriginalLookupRuleMatrix.tail_matrix_iff hZ w n s row trace env h0 h1 h2 h3

theorem originalLookupTailMatrixIff_kernel_certificate {m} (env : Fin 4 → Fin m) (w n s row trace : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalLookupTailMatrixIffSentence env w n s row trace)) := TheoryTransport.sentence (source_originalLookupTailMatrixIff env w n s row trace)

theorem native_originalLookupTailMatrixIff {m} (env : Fin 4 → Fin m) (w n s row trace : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalLookupTailMatrixIffSentence env w n s row trace)) := ZFReplay.replay (originalLookupTailMatrixIff_kernel_certificate env w n s row trace)

def originalLookupChildMemberIffSentence {m} (env : Fin 4 → Fin m) (w trace : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 4 w env).imp (((HornRuleSyntax.premise OriginalLookupExpr.premiseExpr w trace env).iff (OriginalLookupRuleMatrix.childMember w trace env))))).close

theorem source_originalLookupChildMemberIff {m} (env : Fin 4 → Fin m) (w trace : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalLookupChildMemberIffSentence env w trace) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.environmentNat 4 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 4 w env) := .hyp (Or.inl rfl)
  exact OriginalLookupRuleMatrix.child_member_iff hZ w trace env h0 h1

theorem originalLookupChildMemberIff_kernel_certificate {m} (env : Fin 4 → Fin m) (w trace : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalLookupChildMemberIffSentence env w trace)) := TheoryTransport.sentence (source_originalLookupChildMemberIff env w trace)

theorem native_originalLookupChildMemberIff {m} (env : Fin 4 → Fin m) (w trace : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalLookupChildMemberIffSentence env w trace)) := ZFReplay.replay (originalLookupChildMemberIff_kernel_certificate env w trace)

def originalLookupHeadAssignmentBoundSentence {m} (env : Fin 2 → Fin m) (w row : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 2 w env).imp ((HornExprSyntax.graph YesMetaZFC.Automation.ObjectSyntaxTransform.lookupHead.head w env row).imp ((HornExprBounds.environmentBound 2 row env))))).close

theorem source_originalLookupHeadAssignmentBound {m} (env : Fin 2 → Fin m) (w row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalLookupHeadAssignmentBoundSentence env w row) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.graph YesMetaZFC.Automation.ObjectSyntaxTransform.lookupHead.head w env row) (Context.add (HornExprSyntax.environmentNat 2 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 2 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (HornExprSyntax.graph YesMetaZFC.Automation.ObjectSyntaxTransform.lookupHead.head w env row) := .hyp (Or.inl rfl)
  exact HornExprBounds.lookup_head_bound hZ w row env h0 h1 h2

theorem originalLookupHeadAssignmentBound_kernel_certificate {m} (env : Fin 2 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalLookupHeadAssignmentBoundSentence env w row)) := TheoryTransport.sentence (source_originalLookupHeadAssignmentBound env w row)

theorem native_originalLookupHeadAssignmentBound {m} (env : Fin 2 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalLookupHeadAssignmentBoundSentence env w row)) := ZFReplay.replay (originalLookupHeadAssignmentBound_kernel_certificate env w row)

def originalLookupTailAssignmentBoundSentence {m} (env : Fin 4 → Fin m) (w row : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 4 w env).imp ((HornExprSyntax.graph YesMetaZFC.Automation.ObjectSyntaxTransform.lookupTail.head w env row).imp ((HornExprBounds.environmentBound 4 row env))))).close

theorem source_originalLookupTailAssignmentBound {m} (env : Fin 4 → Fin m) (w row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalLookupTailAssignmentBoundSentence env w row) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.graph YesMetaZFC.Automation.ObjectSyntaxTransform.lookupTail.head w env row) (Context.add (HornExprSyntax.environmentNat 4 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 4 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (HornExprSyntax.graph YesMetaZFC.Automation.ObjectSyntaxTransform.lookupTail.head w env row) := .hyp (Or.inl rfl)
  exact HornExprBounds.lookup_tail_bound hZ w row env h0 h1 h2

theorem originalLookupTailAssignmentBound_kernel_certificate {m} (env : Fin 4 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalLookupTailAssignmentBoundSentence env w row)) := TheoryTransport.sentence (source_originalLookupTailAssignmentBound env w row)

theorem native_originalLookupTailAssignmentBound {m} (env : Fin 4 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalLookupTailAssignmentBoundSentence env w row)) := ZFReplay.replay (originalLookupTailAssignmentBound_kernel_certificate env w row)

end PPAC.Migration.Internal.ObjectOriginalLookupRules
