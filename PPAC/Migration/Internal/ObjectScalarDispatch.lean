import PPAC.Migration.Internal.OriginalBoundIdentity

/-! 原完整表变量精确分派、绑定变量全内部轨迹恒等与拒绝对应的原核证书。 -/
namespace PPAC.Migration.Internal.ObjectScalarDispatch
open Source SourceAlgebra SourceLogic OmegaSyntax

def originalDifferentNodeTagsSentence {m} {n} (tag target k : Nat) (_hne : tag ≠ target) (p : YesMetaZFC.Automation.ObjectHorn.Expr n) (env : Fin n → Fin m) (xs : Fin k → Fin m) (w r : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat n w env).imp ((HornExprSyntax.graph (YesMetaZFC.Automation.ObjectHorn.Expr.succ (.pair (.literal tag) p)) w env r).imp ((SyntaxNodeSyntax.constructor k target w xs r).imp ((.bot)))))).close

theorem source_originalDifferentNodeTags {m} {n} (tag target k : Nat) (_hne : tag ≠ target) (p : YesMetaZFC.Automation.ObjectHorn.Expr n) (env : Fin n → Fin m) (xs : Fin k → Fin m) (w r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalDifferentNodeTagsSentence tag target k _hne p env xs w r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNodeSyntax.constructor k target w xs r) (Context.add (HornExprSyntax.graph (YesMetaZFC.Automation.ObjectHorn.Expr.succ (.pair (.literal tag) p)) w env r) (Context.add (HornExprSyntax.environmentNat n w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (HornExprSyntax.environmentNat n w env) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (HornExprSyntax.graph (YesMetaZFC.Automation.ObjectHorn.Expr.succ (.pair (.literal tag) p)) w env r) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxNodeSyntax.constructor k target w xs r) := .hyp (Or.inl rfl)
  exact HornNodeDisjoint.node_contradiction hZ tag target k _hne p w r env xs h0 h1 h2 h3

theorem originalDifferentNodeTags_kernel_certificate {m} {n} (tag target k : Nat) (_hne : tag ≠ target) (p : YesMetaZFC.Automation.ObjectHorn.Expr n) (env : Fin n → Fin m) (xs : Fin k → Fin m) (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalDifferentNodeTagsSentence tag target k _hne p env xs w r)) := TheoryTransport.sentence (source_originalDifferentNodeTags tag target k _hne p env xs w r)

theorem native_originalDifferentNodeTags {m} {n} (tag target k : Nat) (_hne : tag ≠ target) (p : YesMetaZFC.Automation.ObjectHorn.Expr n) (env : Fin n → Fin m) (xs : Fin k → Fin m) (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalDifferentNodeTagsSentence tag target k _hne p env xs w r)) := ZFReplay.replay (originalDifferentNodeTags_kernel_certificate tag target k _hne p env xs w r)

def originalFiveFieldRecoverySentence {m} {n} (tag : Nat) (es : Fin 5 → YesMetaZFC.Automation.ObjectHorn.Expr n) (env : Fin n → Fin m) (xs : Fin 5 → Fin m) (i : Fin 5) (w r : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat n w env).imp ((HornExprSyntax.graph (YesMetaZFC.Automation.ObjectHorn.Expr.node (.literal tag) (List.ofFn es)) w env r).imp ((SyntaxNodeSyntax.constructor 5 tag w xs r).imp ((HornExprSyntax.graph (es i) w env (xs i))))))).close

theorem source_originalFiveFieldRecovery {m} {n} (tag : Nat) (es : Fin 5 → YesMetaZFC.Automation.ObjectHorn.Expr n) (env : Fin n → Fin m) (xs : Fin 5 → Fin m) (i : Fin 5) (w r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalFiveFieldRecoverySentence tag es env xs i w r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNodeSyntax.constructor 5 tag w xs r) (Context.add (HornExprSyntax.graph (YesMetaZFC.Automation.ObjectHorn.Expr.node (.literal tag) (List.ofFn es)) w env r) (Context.add (HornExprSyntax.environmentNat n w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (HornExprSyntax.environmentNat n w env) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (HornExprSyntax.graph (YesMetaZFC.Automation.ObjectHorn.Expr.node (.literal tag) (List.ofFn es)) w env r) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxNodeSyntax.constructor 5 tag w xs r) := .hyp (Or.inl rfl)
  exact HornRowFields.field_graph hZ tag es w r env xs i h0 h1 h2 h3

theorem originalFiveFieldRecovery_kernel_certificate {m} {n} (tag : Nat) (es : Fin 5 → YesMetaZFC.Automation.ObjectHorn.Expr n) (env : Fin n → Fin m) (xs : Fin 5 → Fin m) (i : Fin 5) (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalFiveFieldRecoverySentence tag es env xs i w r)) := TheoryTransport.sentence (source_originalFiveFieldRecovery tag es env xs i w r)

theorem native_originalFiveFieldRecovery {m} {n} (tag : Nat) (es : Fin 5 → YesMetaZFC.Automation.ObjectHorn.Expr n) (env : Fin n → Fin m) (xs : Fin 5 → Fin m) (i : Fin 5) (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalFiveFieldRecoverySentence tag es env xs i w r)) := ZFReplay.replay (originalFiveFieldRecovery_kernel_certificate tag es env xs i w r)

def originalModeWholeTableDispatchIffSentence {m} (three : Bool) (xs : Fin 5 → Fin m) (w r R : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNodeSyntax.constructor 5 1 w xs r).imp ((SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) (xs 0)).imp (((HornStepSyntax.originalStep w r R).iff (HornStepSyntax.step (OriginalScalarClasses.selected three) w r R)))))).close

theorem source_originalModeWholeTableDispatchIff {m} (three : Bool) (xs : Fin 5 → Fin m) (w r R : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalModeWholeTableDispatchIffSentence three xs w r R) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) (xs 0)) (Context.add (SyntaxNodeSyntax.constructor 5 1 w xs r) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxNodeSyntax.constructor 5 1 w xs r) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) (xs 0)) := .hyp (Or.inl rfl)
  exact OriginalModeDispatch.dispatch_iff hZ three w r R xs h0 h1 h2

theorem originalModeWholeTableDispatchIff_kernel_certificate {m} (three : Bool) (xs : Fin 5 → Fin m) (w r R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalModeWholeTableDispatchIffSentence three xs w r R)) := TheoryTransport.sentence (source_originalModeWholeTableDispatchIff three xs w r R)

theorem native_originalModeWholeTableDispatchIff {m} (three : Bool) (xs : Fin 5 → Fin m) (w r R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalModeWholeTableDispatchIffSentence three xs w r R)) := ZFReplay.replay (originalModeWholeTableDispatchIff_kernel_certificate three xs w r R)

def originalVariableWholeTableDispatchIffSentence {m} (three bound : Bool) (xs : Fin 5 → Fin m) (w r R idx : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNodeSyntax.constructor 5 1 w xs r).imp ((SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) (xs 0)).imp ((SyntaxVariableSyntax.code bound w idx (xs 3)).imp (((HornStepSyntax.originalStep w r R).iff (HornApplicationSyntax.application (OriginalScalarClasses.chosen three bound) w r R))))))).close

theorem source_originalVariableWholeTableDispatchIff {m} (three bound : Bool) (xs : Fin 5 → Fin m) (w r R idx : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalVariableWholeTableDispatchIffSentence three bound xs w r R idx) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxVariableSyntax.code bound w idx (xs 3)) (Context.add (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) (xs 0)) (Context.add (SyntaxNodeSyntax.constructor 5 1 w xs r) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNodeSyntax.constructor 5 1 w xs r) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) (xs 0)) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxVariableSyntax.code bound w idx (xs 3)) := .hyp (Or.inl rfl)
  exact OriginalVariableDispatch.dispatch_iff hZ three bound w r R idx xs h0 h1 h2 h3

theorem originalVariableWholeTableDispatchIff_kernel_certificate {m} (three bound : Bool) (xs : Fin 5 → Fin m) (w r R idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalVariableWholeTableDispatchIffSentence three bound xs w r R idx)) := TheoryTransport.sentence (source_originalVariableWholeTableDispatchIff three bound xs w r R idx)

theorem native_originalVariableWholeTableDispatchIff {m} (three bound : Bool) (xs : Fin 5 → Fin m) (w r R idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalVariableWholeTableDispatchIffSentence three bound xs w r R idx)) := ZFReplay.replay (originalVariableWholeTableDispatchIff_kernel_certificate three bound xs w r R idx)

def boundModeZeroDispatchIffSentence {m} (xs : Fin 5 → Fin m) (w r R idx : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNodeSyntax.constructor 5 1 w xs r).imp ((SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode false) (xs 0)).imp ((SyntaxVariableSyntax.code true w idx (xs 3)).imp (((HornStepSyntax.originalStep w r R).iff (HornApplicationSyntax.application (OriginalScalarClasses.chosen false true) w r R))))))).close

theorem source_boundModeZeroDispatchIff {m} (xs : Fin 5 → Fin m) (w r R idx : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (boundModeZeroDispatchIffSentence xs w r R idx) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxVariableSyntax.code true w idx (xs 3)) (Context.add (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode false) (xs 0)) (Context.add (SyntaxNodeSyntax.constructor 5 1 w xs r) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNodeSyntax.constructor 5 1 w xs r) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode false) (xs 0)) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxVariableSyntax.code true w idx (xs 3)) := .hyp (Or.inl rfl)
  exact OriginalVariableDispatch.dispatch_iff hZ false true w r R idx xs h0 h1 h2 h3

theorem boundModeZeroDispatchIff_kernel_certificate {m} (xs : Fin 5 → Fin m) (w r R idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (boundModeZeroDispatchIffSentence xs w r R idx)) := TheoryTransport.sentence (source_boundModeZeroDispatchIff xs w r R idx)

theorem native_boundModeZeroDispatchIff {m} (xs : Fin 5 → Fin m) (w r R idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (boundModeZeroDispatchIffSentence xs w r R idx)) := ZFReplay.replay (boundModeZeroDispatchIff_kernel_certificate xs w r R idx)

def boundModeThreeDispatchIffSentence {m} (xs : Fin 5 → Fin m) (w r R idx : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNodeSyntax.constructor 5 1 w xs r).imp ((SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode true) (xs 0)).imp ((SyntaxVariableSyntax.code true w idx (xs 3)).imp (((HornStepSyntax.originalStep w r R).iff (HornApplicationSyntax.application (OriginalScalarClasses.chosen true true) w r R))))))).close

theorem source_boundModeThreeDispatchIff {m} (xs : Fin 5 → Fin m) (w r R idx : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (boundModeThreeDispatchIffSentence xs w r R idx) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxVariableSyntax.code true w idx (xs 3)) (Context.add (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode true) (xs 0)) (Context.add (SyntaxNodeSyntax.constructor 5 1 w xs r) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNodeSyntax.constructor 5 1 w xs r) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode true) (xs 0)) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxVariableSyntax.code true w idx (xs 3)) := .hyp (Or.inl rfl)
  exact OriginalVariableDispatch.dispatch_iff hZ true true w r R idx xs h0 h1 h2 h3

theorem boundModeThreeDispatchIff_kernel_certificate {m} (xs : Fin 5 → Fin m) (w r R idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (boundModeThreeDispatchIffSentence xs w r R idx)) := TheoryTransport.sentence (source_boundModeThreeDispatchIff xs w r R idx)

theorem native_boundModeThreeDispatchIff {m} (xs : Fin 5 → Fin m) (w r R idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (boundModeThreeDispatchIffSentence xs w r R idx)) := ZFReplay.replay (boundModeThreeDispatchIff_kernel_certificate xs w r R idx)

def freeModeZeroDispatchIffSentence {m} (xs : Fin 5 → Fin m) (w r R idx : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNodeSyntax.constructor 5 1 w xs r).imp ((SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode false) (xs 0)).imp ((SyntaxVariableSyntax.code false w idx (xs 3)).imp (((HornStepSyntax.originalStep w r R).iff (HornApplicationSyntax.application (OriginalScalarClasses.chosen false false) w r R))))))).close

theorem source_freeModeZeroDispatchIff {m} (xs : Fin 5 → Fin m) (w r R idx : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (freeModeZeroDispatchIffSentence xs w r R idx) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxVariableSyntax.code false w idx (xs 3)) (Context.add (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode false) (xs 0)) (Context.add (SyntaxNodeSyntax.constructor 5 1 w xs r) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNodeSyntax.constructor 5 1 w xs r) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode false) (xs 0)) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxVariableSyntax.code false w idx (xs 3)) := .hyp (Or.inl rfl)
  exact OriginalVariableDispatch.dispatch_iff hZ false false w r R idx xs h0 h1 h2 h3

theorem freeModeZeroDispatchIff_kernel_certificate {m} (xs : Fin 5 → Fin m) (w r R idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (freeModeZeroDispatchIffSentence xs w r R idx)) := TheoryTransport.sentence (source_freeModeZeroDispatchIff xs w r R idx)

theorem native_freeModeZeroDispatchIff {m} (xs : Fin 5 → Fin m) (w r R idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (freeModeZeroDispatchIffSentence xs w r R idx)) := ZFReplay.replay (freeModeZeroDispatchIff_kernel_certificate xs w r R idx)

def freeModeThreeDispatchIffSentence {m} (xs : Fin 5 → Fin m) (w r R idx : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNodeSyntax.constructor 5 1 w xs r).imp ((SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode true) (xs 0)).imp ((SyntaxVariableSyntax.code false w idx (xs 3)).imp (((HornStepSyntax.originalStep w r R).iff (HornApplicationSyntax.application (OriginalScalarClasses.chosen true false) w r R))))))).close

theorem source_freeModeThreeDispatchIff {m} (xs : Fin 5 → Fin m) (w r R idx : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (freeModeThreeDispatchIffSentence xs w r R idx) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxVariableSyntax.code false w idx (xs 3)) (Context.add (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode true) (xs 0)) (Context.add (SyntaxNodeSyntax.constructor 5 1 w xs r) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNodeSyntax.constructor 5 1 w xs r) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode true) (xs 0)) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxVariableSyntax.code false w idx (xs 3)) := .hyp (Or.inl rfl)
  exact OriginalVariableDispatch.dispatch_iff hZ true false w r R idx xs h0 h1 h2 h3

theorem freeModeThreeDispatchIff_kernel_certificate {m} (xs : Fin 5 → Fin m) (w r R idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (freeModeThreeDispatchIffSentence xs w r R idx)) := TheoryTransport.sentence (source_freeModeThreeDispatchIff xs w r R idx)

theorem native_freeModeThreeDispatchIff {m} (xs : Fin 5 → Fin m) (w r R idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (freeModeThreeDispatchIffSentence xs w r R idx)) := ZFReplay.replay (freeModeThreeDispatchIff_kernel_certificate xs w r R idx)

def originalVariableActualSearchDispatchIffSentence {m} (three bound : Bool) (xs : Fin 5 → Fin m) (w r R idx : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNodeSyntax.constructor 5 1 w xs r).imp ((SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) (xs 0)).imp ((SyntaxVariableSyntax.code bound w idx (xs 3)).imp (((HornSearchSyntax.originalSearchStep w r R).iff (HornApplicationSyntax.application (OriginalScalarClasses.chosen three bound) w r R))))))).close

theorem source_originalVariableActualSearchDispatchIff {m} (three bound : Bool) (xs : Fin 5 → Fin m) (w r R idx : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalVariableActualSearchDispatchIffSentence three bound xs w r R idx) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxVariableSyntax.code bound w idx (xs 3)) (Context.add (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) (xs 0)) (Context.add (SyntaxNodeSyntax.constructor 5 1 w xs r) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNodeSyntax.constructor 5 1 w xs r) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) (xs 0)) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxVariableSyntax.code bound w idx (xs 3)) := .hyp (Or.inl rfl)
  exact OriginalVariableDispatch.search_dispatch_iff hZ three bound w r R idx xs h0 h1 h2 h3

theorem originalVariableActualSearchDispatchIff_kernel_certificate {m} (three bound : Bool) (xs : Fin 5 → Fin m) (w r R idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalVariableActualSearchDispatchIffSentence three bound xs w r R idx)) := TheoryTransport.sentence (source_originalVariableActualSearchDispatchIff three bound xs w r R idx)

theorem native_originalVariableActualSearchDispatchIff {m} (three bound : Bool) (xs : Fin 5 → Fin m) (w r R idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalVariableActualSearchDispatchIffSentence three bound xs w r R idx)) := ZFReplay.replay (originalVariableActualSearchDispatchIff_kernel_certificate three bound xs w r R idx)

def originalVariableCandidateRejectionIffSentence {m} (three bound : Bool) (xs : Fin 5 → Fin m) (w r R idx : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNodeSyntax.constructor 5 1 w xs r).imp ((SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) (xs 0)).imp ((SyntaxVariableSyntax.code bound w idx (xs 3)).imp (((HornStepSyntax.originalStep w r R).neg.iff (HornApplicationSyntax.application (OriginalScalarClasses.chosen three bound) w r R).neg)))))).close

theorem source_originalVariableCandidateRejectionIff {m} (three bound : Bool) (xs : Fin 5 → Fin m) (w r R idx : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalVariableCandidateRejectionIffSentence three bound xs w r R idx) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxVariableSyntax.code bound w idx (xs 3)) (Context.add (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) (xs 0)) (Context.add (SyntaxNodeSyntax.constructor 5 1 w xs r) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNodeSyntax.constructor 5 1 w xs r) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) (xs 0)) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxVariableSyntax.code bound w idx (xs 3)) := .hyp (Or.inl rfl)
  exact OriginalVariableDispatch.rejected_iff hZ three bound w r R idx xs h0 h1 h2 h3

theorem originalVariableCandidateRejectionIff_kernel_certificate {m} (three bound : Bool) (xs : Fin 5 → Fin m) (w r R idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalVariableCandidateRejectionIffSentence three bound xs w r R idx)) := TheoryTransport.sentence (source_originalVariableCandidateRejectionIff three bound xs w r R idx)

theorem native_originalVariableCandidateRejectionIff {m} (three bound : Bool) (xs : Fin 5 → Fin m) (w r R idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalVariableCandidateRejectionIffSentence three bound xs w r R idx)) := ZFReplay.replay (originalVariableCandidateRejectionIff_kernel_certificate three bound xs w r R idx)

def arbitraryClosedVariableTraceApplicationSentence {m} (three bound : Bool) (xs : Fin 5 → Fin m) (w r R idx : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNodeSyntax.constructor 5 1 w xs r).imp ((SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) (xs 0)).imp ((SyntaxVariableSyntax.code bound w idx (xs 3)).imp ((HornLookupSoundSyntax.closed w R).imp ((Formula.mem r R).imp ((HornApplicationSyntax.application (OriginalScalarClasses.chosen three bound) w r R)))))))).close

theorem source_arbitraryClosedVariableTraceApplication {m} (three bound : Bool) (xs : Fin 5 → Fin m) (w r R idx : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (arbitraryClosedVariableTraceApplicationSentence three bound xs w r R idx) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem r R) (Context.add (HornLookupSoundSyntax.closed w R) (Context.add (SyntaxVariableSyntax.code bound w idx (xs 3)) (Context.add (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) (xs 0)) (Context.add (SyntaxNodeSyntax.constructor 5 1 w xs r) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
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
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) (xs 0)) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (SyntaxVariableSyntax.code bound w idx (xs 3)) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (HornLookupSoundSyntax.closed w R) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (Formula.mem r R) := .hyp (Or.inl rfl)
  exact OriginalVariableDispatch.closed_member_application hZ three bound w r R idx xs h0 h1 h2 h3 h4 h5

theorem arbitraryClosedVariableTraceApplication_kernel_certificate {m} (three bound : Bool) (xs : Fin 5 → Fin m) (w r R idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (arbitraryClosedVariableTraceApplicationSentence three bound xs w r R idx)) := TheoryTransport.sentence (source_arbitraryClosedVariableTraceApplication three bound xs w r R idx)

theorem native_arbitraryClosedVariableTraceApplication {m} (three bound : Bool) (xs : Fin 5 → Fin m) (w r R idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (arbitraryClosedVariableTraceApplicationSentence three bound xs w r R idx)) := ZFReplay.replay (arbitraryClosedVariableTraceApplication_kernel_certificate three bound xs w r R idx)

def originalVariableExprFromCodeSentence {m} {n} (bound : Bool) (e : YesMetaZFC.Automation.ObjectHorn.Expr n) (env : Fin n → Fin m) (w idx y : Fin m) : Source.Sentence := ((HornExprSyntax.graph e w env idx).imp ((SyntaxVariableSyntax.code bound w idx y).imp ((HornExprSyntax.graph (HornVariableExpr.expression bound e) w env y)))).close

theorem source_originalVariableExprFromCode {m} {n} (bound : Bool) (e : YesMetaZFC.Automation.ObjectHorn.Expr n) (env : Fin n → Fin m) (w idx y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalVariableExprFromCodeSentence bound e env w idx y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxVariableSyntax.code bound w idx y) (Context.add (HornExprSyntax.graph e w env idx) (Source.SetLanguage.ZF.at m))
  have h0 : Derives Δ (HornExprSyntax.graph e w env idx) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxVariableSyntax.code bound w idx y) := .hyp (Or.inl rfl)
  exact HornVariableExpr.code_graph bound e w idx y env h0 h1

theorem originalVariableExprFromCode_kernel_certificate {m} {n} (bound : Bool) (e : YesMetaZFC.Automation.ObjectHorn.Expr n) (env : Fin n → Fin m) (w idx y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalVariableExprFromCodeSentence bound e env w idx y)) := TheoryTransport.sentence (source_originalVariableExprFromCode bound e env w idx y)

theorem native_originalVariableExprFromCode {m} {n} (bound : Bool) (e : YesMetaZFC.Automation.ObjectHorn.Expr n) (env : Fin n → Fin m) (w idx y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalVariableExprFromCodeSentence bound e env w idx y)) := ZFReplay.replay (originalVariableExprFromCode_kernel_certificate bound e env w idx y)

def originalBoundApplicationIdentitySentence {m} (three : Bool) (xs : Fin 5 → Fin m) (w r R : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNodeSyntax.constructor 5 1 w xs r).imp ((HornApplicationSyntax.application (YesMetaZFC.Automation.ObjectSyntaxTransform.boundIdentity (OriginalScalarClasses.mode three)) w r R).imp ((Formula.equal (xs 4) (xs 3)))))).close

theorem source_originalBoundApplicationIdentity {m} (three : Bool) (xs : Fin 5 → Fin m) (w r R : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalBoundApplicationIdentitySentence three xs w r R) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornApplicationSyntax.application (YesMetaZFC.Automation.ObjectSyntaxTransform.boundIdentity (OriginalScalarClasses.mode three)) w r R) (Context.add (SyntaxNodeSyntax.constructor 5 1 w xs r) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxNodeSyntax.constructor 5 1 w xs r) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (HornApplicationSyntax.application (YesMetaZFC.Automation.ObjectSyntaxTransform.boundIdentity (OriginalScalarClasses.mode three)) w r R) := .hyp (Or.inl rfl)
  exact OriginalBoundIdentity.application_identity hZ three w r R xs h0 h1 h2

theorem originalBoundApplicationIdentity_kernel_certificate {m} (three : Bool) (xs : Fin 5 → Fin m) (w r R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalBoundApplicationIdentitySentence three xs w r R)) := TheoryTransport.sentence (source_originalBoundApplicationIdentity three xs w r R)

theorem native_originalBoundApplicationIdentity {m} (three : Bool) (xs : Fin 5 → Fin m) (w r R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalBoundApplicationIdentitySentence three xs w r R)) := ZFReplay.replay (originalBoundApplicationIdentity_kernel_certificate three xs w r R)

def originalBoundTraceIdentityIffSentence {m} (three : Bool) (xs : Fin 5 → Fin m) (w r idx : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNodeSyntax.constructor 5 1 w xs r).imp ((SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) (xs 0)).imp ((SyntaxVariableSyntax.code true w idx (xs 3)).imp (((HornLookupConditionSyntax.condition w r).iff (Formula.equal (xs 4) (xs 3)))))))).close

theorem source_originalBoundTraceIdentityIff {m} (three : Bool) (xs : Fin 5 → Fin m) (w r idx : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalBoundTraceIdentityIffSentence three xs w r idx) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxVariableSyntax.code true w idx (xs 3)) (Context.add (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) (xs 0)) (Context.add (SyntaxNodeSyntax.constructor 5 1 w xs r) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNodeSyntax.constructor 5 1 w xs r) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) (xs 0)) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxVariableSyntax.code true w idx (xs 3)) := .hyp (Or.inl rfl)
  exact OriginalBoundIdentity.trace_iff_identity hZ three w r idx xs h0 h1 h2 h3

theorem originalBoundTraceIdentityIff_kernel_certificate {m} (three : Bool) (xs : Fin 5 → Fin m) (w r idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalBoundTraceIdentityIffSentence three xs w r idx)) := TheoryTransport.sentence (source_originalBoundTraceIdentityIff three xs w r idx)

theorem native_originalBoundTraceIdentityIff {m} (three : Bool) (xs : Fin 5 → Fin m) (w r idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalBoundTraceIdentityIffSentence three xs w r idx)) := ZFReplay.replay (originalBoundTraceIdentityIff_kernel_certificate three xs w r idx)

def originalBoundPowerTraceIdentityIffSentence {m} (three : Bool) (xs : Fin 5 → Fin m) (w r idx : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNodeSyntax.constructor 5 1 w xs r).imp ((SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) (xs 0)).imp ((SyntaxVariableSyntax.code true w idx (xs 3)).imp (((HornLookupPowerCondition.condition w r).iff (Formula.equal (xs 4) (xs 3)))))))).close

theorem source_originalBoundPowerTraceIdentityIff {m} (three : Bool) (xs : Fin 5 → Fin m) (w r idx : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalBoundPowerTraceIdentityIffSentence three xs w r idx) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxVariableSyntax.code true w idx (xs 3)) (Context.add (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) (xs 0)) (Context.add (SyntaxNodeSyntax.constructor 5 1 w xs r) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNodeSyntax.constructor 5 1 w xs r) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) (xs 0)) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxVariableSyntax.code true w idx (xs 3)) := .hyp (Or.inl rfl)
  exact OriginalBoundIdentity.power_trace_iff_identity hZ three w r idx xs h0 h1 h2 h3

theorem originalBoundPowerTraceIdentityIff_kernel_certificate {m} (three : Bool) (xs : Fin 5 → Fin m) (w r idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalBoundPowerTraceIdentityIffSentence three xs w r idx)) := TheoryTransport.sentence (source_originalBoundPowerTraceIdentityIff three xs w r idx)

theorem native_originalBoundPowerTraceIdentityIff {m} (three : Bool) (xs : Fin 5 → Fin m) (w r idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalBoundPowerTraceIdentityIffSentence three xs w r idx)) := ZFReplay.replay (originalBoundPowerTraceIdentityIff_kernel_certificate three xs w r idx)

def originalBoundTraceRejectionIffSentence {m} (three : Bool) (xs : Fin 5 → Fin m) (w r idx : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNodeSyntax.constructor 5 1 w xs r).imp ((SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) (xs 0)).imp ((SyntaxVariableSyntax.code true w idx (xs 3)).imp (((HornLookupConditionSyntax.condition w r).neg.iff (Formula.equal (xs 4) (xs 3)).neg)))))).close

theorem source_originalBoundTraceRejectionIff {m} (three : Bool) (xs : Fin 5 → Fin m) (w r idx : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalBoundTraceRejectionIffSentence three xs w r idx) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxVariableSyntax.code true w idx (xs 3)) (Context.add (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) (xs 0)) (Context.add (SyntaxNodeSyntax.constructor 5 1 w xs r) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNodeSyntax.constructor 5 1 w xs r) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) (xs 0)) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxVariableSyntax.code true w idx (xs 3)) := .hyp (Or.inl rfl)
  exact OriginalBoundIdentity.rejected_iff hZ three w r idx xs h0 h1 h2 h3

theorem originalBoundTraceRejectionIff_kernel_certificate {m} (three : Bool) (xs : Fin 5 → Fin m) (w r idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalBoundTraceRejectionIffSentence three xs w r idx)) := TheoryTransport.sentence (source_originalBoundTraceRejectionIff three xs w r idx)

theorem native_originalBoundTraceRejectionIff {m} (three : Bool) (xs : Fin 5 → Fin m) (w r idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalBoundTraceRejectionIffSentence three xs w r idx)) := ZFReplay.replay (originalBoundTraceRejectionIff_kernel_certificate three xs w r idx)

end PPAC.Migration.Internal.ObjectScalarDispatch
