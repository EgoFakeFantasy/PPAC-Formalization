import PPAC.Migration.Internal.AbstractFrameAtomic

/-! 小模式原完整公式运行方程及任意深度mode1四原子程序的原核闭句。 -/
namespace PPAC.Migration.Internal.ObjectAbstractAtomicFormula
open Source SourceAlgebra SourceLogic OmegaSyntax

def smallModeFormulaConstantGuardSentence {m} (modeIndex : Fin 4) (tag : Nat) (env : Fin 3 → Fin m) (w : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 3 w env).imp ((SyntaxNumeralSyntax.numeral modeIndex.val (env 0)).imp ((HornRuleSyntax.guards (YesMetaZFC.Automation.ObjectSyntaxTransform.constant tag).guards w env))))).close

theorem source_smallModeFormulaConstantGuard {m} (modeIndex : Fin 4) (tag : Nat) (env : Fin 3 → Fin m) (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (smallModeFormulaConstantGuardSentence modeIndex tag env w) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNumeralSyntax.numeral modeIndex.val (env 0)) (Context.add (HornExprSyntax.environmentNat 3 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 3 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral modeIndex.val (env 0)) := .hyp (Or.inl rfl)
  exact SmallModeFormulaMatrix.constant_guard hZ modeIndex.val modeIndex.isLt tag w env h0 h1 h2

theorem smallModeFormulaConstantGuard_kernel_certificate {m} (modeIndex : Fin 4) (tag : Nat) (env : Fin 3 → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (smallModeFormulaConstantGuardSentence modeIndex tag env w)) := TheoryTransport.sentence (source_smallModeFormulaConstantGuard modeIndex tag env w)

theorem native_smallModeFormulaConstantGuard {m} (modeIndex : Fin 4) (tag : Nat) (env : Fin 3 → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (smallModeFormulaConstantGuardSentence modeIndex tag env w)) := ZFReplay.replay (smallModeFormulaConstantGuard_kernel_certificate modeIndex tag env w)

def smallModeFormulaConstantMatrixIffSentence {m} (modeIndex : Fin 4) (tag : Nat) (env : Fin 3 → Fin m) (w n q r : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 3 w env).imp ((SyntaxNumeralSyntax.numeral modeIndex.val (env 0)).imp ((OriginalTransformRowSyntax.row 3 w (env 0) (env 1) (env 2) n q r).imp (((HornUniversalTraceRules.tracedMatrix (YesMetaZFC.Automation.ObjectSyntaxTransform.constant tag) w r env).iff (OriginalFormulaLocalData.constant tag w n q))))))).close

theorem source_smallModeFormulaConstantMatrixIff {m} (modeIndex : Fin 4) (tag : Nat) (env : Fin 3 → Fin m) (w n q r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (smallModeFormulaConstantMatrixIffSentence modeIndex tag env w n q r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (OriginalTransformRowSyntax.row 3 w (env 0) (env 1) (env 2) n q r) (Context.add (SyntaxNumeralSyntax.numeral modeIndex.val (env 0)) (Context.add (HornExprSyntax.environmentNat 3 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 3 w env) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral modeIndex.val (env 0)) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (OriginalTransformRowSyntax.row 3 w (env 0) (env 1) (env 2) n q r) := .hyp (Or.inl rfl)
  exact SmallModeFormulaMatrix.constant_at_row hZ modeIndex.val modeIndex.isLt tag w n q r env h0 h1 h2 h3

theorem smallModeFormulaConstantMatrixIff_kernel_certificate {m} (modeIndex : Fin 4) (tag : Nat) (env : Fin 3 → Fin m) (w n q r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (smallModeFormulaConstantMatrixIffSentence modeIndex tag env w n q r)) := TheoryTransport.sentence (source_smallModeFormulaConstantMatrixIff modeIndex tag env w n q r)

theorem native_smallModeFormulaConstantMatrixIff {m} (modeIndex : Fin 4) (tag : Nat) (env : Fin 3 → Fin m) (w n q r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (smallModeFormulaConstantMatrixIffSentence modeIndex tag env w n q r)) := ZFReplay.replay (smallModeFormulaConstantMatrixIff_kernel_certificate modeIndex tag env w n q r)

def smallModeFormulaConstantApplicationIffSentence {m} (modeIndex : Fin 4) (truth : Bool) (w mode depth P n q r V : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral modeIndex.val mode).imp ((OriginalTransformRowSyntax.row 3 w mode depth P n q r).imp ((HornUniversalTraceSyntax.value w V).imp (((HornApplicationSyntax.application (YesMetaZFC.Automation.ObjectSyntaxTransform.constant (if truth then 1 else 0)) w r V).iff (OriginalFormulaLocalData.constant (if truth then 1 else 0) w n q))))))).close

theorem source_smallModeFormulaConstantApplicationIff {m} (modeIndex : Fin 4) (truth : Bool) (w mode depth P n q r V : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (smallModeFormulaConstantApplicationIffSentence modeIndex truth w mode depth P n q r V) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornUniversalTraceSyntax.value w V) (Context.add (OriginalTransformRowSyntax.row 3 w mode depth P n q r) (Context.add (SyntaxNumeralSyntax.numeral modeIndex.val mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral modeIndex.val mode) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (OriginalTransformRowSyntax.row 3 w mode depth P n q r) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (HornUniversalTraceSyntax.value w V) := .hyp (Or.inl rfl)
  exact SmallModeFormulaConstantApplication.constant_iff hZ modeIndex.val modeIndex.isLt (if truth then 1 else 0) (by cases truth <;> simp [OriginalFormulaClasses.selected]) w mode depth P n q r V h0 h1 h2 h3

theorem smallModeFormulaConstantApplicationIff_kernel_certificate {m} (modeIndex : Fin 4) (truth : Bool) (w mode depth P n q r V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (smallModeFormulaConstantApplicationIffSentence modeIndex truth w mode depth P n q r V)) := TheoryTransport.sentence (source_smallModeFormulaConstantApplicationIff modeIndex truth w mode depth P n q r V)

theorem native_smallModeFormulaConstantApplicationIff {m} (modeIndex : Fin 4) (truth : Bool) (w mode depth P n q r V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (smallModeFormulaConstantApplicationIffSentence modeIndex truth w mode depth P n q r V)) := ZFReplay.replay (smallModeFormulaConstantApplicationIff_kernel_certificate modeIndex truth w mode depth P n q r V)

def smallModeCompleteFormulaTraceIffSentence {m} (modeIndex : Fin 4) (w mode depth P n q r : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral modeIndex.val mode).imp ((OriginalTransformRowSyntax.row 3 w mode depth P n q r).imp (((HornLookupConditionSyntax.condition w r).iff (OriginalFormulaTraceEquation.outcomes w mode depth P n q)))))).close

theorem source_smallModeCompleteFormulaTraceIff {m} (modeIndex : Fin 4) (w mode depth P n q r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (smallModeCompleteFormulaTraceIffSentence modeIndex w mode depth P n q r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (OriginalTransformRowSyntax.row 3 w mode depth P n q r) (Context.add (SyntaxNumeralSyntax.numeral modeIndex.val mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral modeIndex.val mode) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (OriginalTransformRowSyntax.row 3 w mode depth P n q r) := .hyp (Or.inl rfl)
  exact SmallModeFormulaTrace.at_row hZ modeIndex.val modeIndex.isLt w mode depth P n q r h0 h1 h2

theorem smallModeCompleteFormulaTraceIff_kernel_certificate {m} (modeIndex : Fin 4) (w mode depth P n q r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (smallModeCompleteFormulaTraceIffSentence modeIndex w mode depth P n q r)) := TheoryTransport.sentence (source_smallModeCompleteFormulaTraceIff modeIndex w mode depth P n q r)

theorem native_smallModeCompleteFormulaTraceIff {m} (modeIndex : Fin 4) (w mode depth P n q r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (smallModeCompleteFormulaTraceIffSentence modeIndex w mode depth P n q r)) := ZFReplay.replay (smallModeCompleteFormulaTraceIff_kernel_certificate modeIndex w mode depth P n q r)

def smallModeCompleteFormulaWholeRunIffSentence {m} (modeIndex : Fin 4) (w mode depth P n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral modeIndex.val mode).imp ((Formula.mem depth w).imp ((Formula.mem P w).imp (((OriginalTransformRowSyntax.run 3 w mode depth P n q).iff (OriginalFormulaTraceEquation.outcomes w mode depth P n q))))))).close

theorem source_smallModeCompleteFormulaWholeRunIff {m} (modeIndex : Fin 4) (w mode depth P n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (smallModeCompleteFormulaWholeRunIffSentence modeIndex w mode depth P n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem P w) (Context.add (Formula.mem depth w) (Context.add (SyntaxNumeralSyntax.numeral modeIndex.val mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral modeIndex.val mode) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (Formula.mem depth w) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (Formula.mem P w) := .hyp (Or.inl rfl)
  exact SmallModeFormulaRun.run_iff hZ modeIndex.val modeIndex.isLt w mode depth P n q h0 h1 h2 h3

theorem smallModeCompleteFormulaWholeRunIff_kernel_certificate {m} (modeIndex : Fin 4) (w mode depth P n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (smallModeCompleteFormulaWholeRunIffSentence modeIndex w mode depth P n q)) := TheoryTransport.sentence (source_smallModeCompleteFormulaWholeRunIff modeIndex w mode depth P n q)

theorem native_smallModeCompleteFormulaWholeRunIff {m} (modeIndex : Fin 4) (w mode depth P n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (smallModeCompleteFormulaWholeRunIffSentence modeIndex w mode depth P n q)) := ZFReplay.replay (smallModeCompleteFormulaWholeRunIff_kernel_certificate modeIndex w mode depth P n q)

def smallModeWholeFalseDispatchIffSentence {m} (modeIndex : Fin 4) (w mode depth P n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral modeIndex.val mode).imp ((Formula.mem depth w).imp ((Formula.mem P w).imp ((SyntaxNodeSyntax.constructor 0 0 w Fin.elim0 n).imp (((OriginalTransformRowSyntax.run 3 w mode depth P n q).iff (OriginalFormulaLocalData.constant 0 w n q)))))))).close

theorem source_smallModeWholeFalseDispatchIff {m} (modeIndex : Fin 4) (w mode depth P n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (smallModeWholeFalseDispatchIffSentence modeIndex w mode depth P n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNodeSyntax.constructor 0 0 w Fin.elim0 n) (Context.add (Formula.mem P w) (Context.add (Formula.mem depth w) (Context.add (SyntaxNumeralSyntax.numeral modeIndex.val mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral modeIndex.val mode) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (Formula.mem depth w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (Formula.mem P w) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (SyntaxNodeSyntax.constructor 0 0 w Fin.elim0 n) := .hyp (Or.inl rfl)
  exact SmallModeAtomicDispatch.run_iff_false hZ modeIndex.val modeIndex.isLt w mode depth P n q h0 h1 h2 h3 h4

theorem smallModeWholeFalseDispatchIff_kernel_certificate {m} (modeIndex : Fin 4) (w mode depth P n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (smallModeWholeFalseDispatchIffSentence modeIndex w mode depth P n q)) := TheoryTransport.sentence (source_smallModeWholeFalseDispatchIff modeIndex w mode depth P n q)

theorem native_smallModeWholeFalseDispatchIff {m} (modeIndex : Fin 4) (w mode depth P n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (smallModeWholeFalseDispatchIffSentence modeIndex w mode depth P n q)) := ZFReplay.replay (smallModeWholeFalseDispatchIff_kernel_certificate modeIndex w mode depth P n q)

def smallModeWholeTrueDispatchIffSentence {m} (modeIndex : Fin 4) (w mode depth P n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral modeIndex.val mode).imp ((Formula.mem depth w).imp ((Formula.mem P w).imp ((SyntaxNodeSyntax.constructor 0 1 w Fin.elim0 n).imp (((OriginalTransformRowSyntax.run 3 w mode depth P n q).iff (OriginalFormulaLocalData.constant 1 w n q)))))))).close

theorem source_smallModeWholeTrueDispatchIff {m} (modeIndex : Fin 4) (w mode depth P n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (smallModeWholeTrueDispatchIffSentence modeIndex w mode depth P n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNodeSyntax.constructor 0 1 w Fin.elim0 n) (Context.add (Formula.mem P w) (Context.add (Formula.mem depth w) (Context.add (SyntaxNumeralSyntax.numeral modeIndex.val mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral modeIndex.val mode) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (Formula.mem depth w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (Formula.mem P w) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (SyntaxNodeSyntax.constructor 0 1 w Fin.elim0 n) := .hyp (Or.inl rfl)
  exact SmallModeAtomicDispatch.run_iff_true hZ modeIndex.val modeIndex.isLt w mode depth P n q h0 h1 h2 h3 h4

theorem smallModeWholeTrueDispatchIff_kernel_certificate {m} (modeIndex : Fin 4) (w mode depth P n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (smallModeWholeTrueDispatchIffSentence modeIndex w mode depth P n q)) := TheoryTransport.sentence (source_smallModeWholeTrueDispatchIff modeIndex w mode depth P n q)

theorem native_smallModeWholeTrueDispatchIff {m} (modeIndex : Fin 4) (w mode depth P n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (smallModeWholeTrueDispatchIffSentence modeIndex w mode depth P n q)) := ZFReplay.replay (smallModeWholeTrueDispatchIff_kernel_certificate modeIndex w mode depth P n q)

def smallModeWholeEqualityDispatchIffSentence {m} (modeIndex : Fin 4) (w mode depth P n q x y : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral modeIndex.val mode).imp ((Formula.mem depth w).imp ((Formula.mem P w).imp ((SyntaxAtomSyntax.equalCode w x y n).imp (((OriginalTransformRowSyntax.run 3 w mode depth P n q).iff (OriginalFormulaCaseSyntax.binaryCase 3 1 w mode depth P n q)))))))).close

theorem source_smallModeWholeEqualityDispatchIff {m} (modeIndex : Fin 4) (w mode depth P n q x y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (smallModeWholeEqualityDispatchIffSentence modeIndex w mode depth P n q x y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxAtomSyntax.equalCode w x y n) (Context.add (Formula.mem P w) (Context.add (Formula.mem depth w) (Context.add (SyntaxNumeralSyntax.numeral modeIndex.val mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral modeIndex.val mode) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (Formula.mem depth w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (Formula.mem P w) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (SyntaxAtomSyntax.equalCode w x y n) := .hyp (Or.inl rfl)
  exact SmallModeAtomicDispatch.run_iff_equality hZ modeIndex.val modeIndex.isLt w mode depth P n q x y h0 h1 h2 h3 h4

theorem smallModeWholeEqualityDispatchIff_kernel_certificate {m} (modeIndex : Fin 4) (w mode depth P n q x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (smallModeWholeEqualityDispatchIffSentence modeIndex w mode depth P n q x y)) := TheoryTransport.sentence (source_smallModeWholeEqualityDispatchIff modeIndex w mode depth P n q x y)

theorem native_smallModeWholeEqualityDispatchIff {m} (modeIndex : Fin 4) (w mode depth P n q x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (smallModeWholeEqualityDispatchIffSentence modeIndex w mode depth P n q x y)) := ZFReplay.replay (smallModeWholeEqualityDispatchIff_kernel_certificate modeIndex w mode depth P n q x y)

def smallModeWholeMemberDispatchIffSentence {m} (modeIndex : Fin 4) (w mode depth P s x y n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral modeIndex.val mode).imp ((Formula.mem depth w).imp ((Formula.mem P w).imp ((SyntaxAtomSyntax.memberCode w s x y n).imp (((OriginalTransformRowSyntax.run 3 w mode depth P n q).iff (OriginalFormulaCaseSyntax.applicationCase w mode depth P n q)))))))).close

theorem source_smallModeWholeMemberDispatchIff {m} (modeIndex : Fin 4) (w mode depth P s x y n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (smallModeWholeMemberDispatchIffSentence modeIndex w mode depth P s x y n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxAtomSyntax.memberCode w s x y n) (Context.add (Formula.mem P w) (Context.add (Formula.mem depth w) (Context.add (SyntaxNumeralSyntax.numeral modeIndex.val mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral modeIndex.val mode) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (Formula.mem depth w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (Formula.mem P w) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (SyntaxAtomSyntax.memberCode w s x y n) := .hyp (Or.inl rfl)
  exact SmallModeAtomicDispatch.run_iff_application hZ modeIndex.val modeIndex.isLt w mode depth P s x y n q h0 h1 h2 h3 h4

theorem smallModeWholeMemberDispatchIff_kernel_certificate {m} (modeIndex : Fin 4) (w mode depth P s x y n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (smallModeWholeMemberDispatchIffSentence modeIndex w mode depth P s x y n q)) := TheoryTransport.sentence (source_smallModeWholeMemberDispatchIff modeIndex w mode depth P s x y n q)

theorem native_smallModeWholeMemberDispatchIff {m} (modeIndex : Fin 4) (w mode depth P s x y n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (smallModeWholeMemberDispatchIffSentence modeIndex w mode depth P s x y n q)) := ZFReplay.replay (smallModeWholeMemberDispatchIff_kernel_certificate modeIndex w mode depth P s x y n q)

def modeOneFrameAtomicTermAgreementSentence {m} (w mode depth P a b c e R S : Fin m) : Source.Sentence := ((omega w).imp ((AbstractOperationFrameSyntax.frame w mode depth P a b c e R S).imp ((AtomicTermAgreementSyntax.agreement w mode depth P R S a b c e)))).close

theorem source_modeOneFrameAtomicTermAgreement {m} (w mode depth P a b c e R S : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeOneFrameAtomicTermAgreementSentence w mode depth P a b c e R S) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (AbstractOperationFrameSyntax.frame w mode depth P a b c e R S) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (AbstractOperationFrameSyntax.frame w mode depth P a b c e R S) := .hyp (Or.inl rfl)
  exact AbstractFrameAtomicAgreement.terms hZ w mode depth P a b c e R S h0 h1

theorem modeOneFrameAtomicTermAgreement_kernel_certificate {m} (w mode depth P a b c e R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeOneFrameAtomicTermAgreementSentence w mode depth P a b c e R S)) := TheoryTransport.sentence (source_modeOneFrameAtomicTermAgreement w mode depth P a b c e R S)

theorem native_modeOneFrameAtomicTermAgreement {m} (w mode depth P a b c e R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeOneFrameAtomicTermAgreementSentence w mode depth P a b c e R S)) := ZFReplay.replay (modeOneFrameAtomicTermAgreement_kernel_certificate w mode depth P a b c e R S)

def modeOneFrameActualPairProgramIffSentence {m} (w mode depth P a b c e R S n q x y : Fin m) : Source.Sentence := ((omega w).imp ((AbstractOperationFrameSyntax.frame w mode depth P a b c e R S).imp ((SyntaxForestSyntax.forest 2 w (SyntaxAtomSyntax.two x y) n).imp ((ArgumentForestProgramSyntax.typedInputs 2 w a b (SyntaxAtomSyntax.two x y)).imp (((OriginalTransformRowSyntax.run 2 w mode depth P n q).iff (ArgumentPairProgramSyntax.returned w R S c e x y q))))))).close

theorem source_modeOneFrameActualPairProgramIff {m} (w mode depth P a b c e R S n q x y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeOneFrameActualPairProgramIffSentence w mode depth P a b c e R S n q x y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ArgumentForestProgramSyntax.typedInputs 2 w a b (SyntaxAtomSyntax.two x y)) (Context.add (SyntaxForestSyntax.forest 2 w (SyntaxAtomSyntax.two x y) n) (Context.add (AbstractOperationFrameSyntax.frame w mode depth P a b c e R S) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (AbstractOperationFrameSyntax.frame w mode depth P a b c e R S) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxForestSyntax.forest 2 w (SyntaxAtomSyntax.two x y) n) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (ArgumentForestProgramSyntax.typedInputs 2 w a b (SyntaxAtomSyntax.two x y)) := .hyp (Or.inl rfl)
  exact AbstractFrameAtomicAgreement.pair_iff hZ w mode depth P a b c e R S n q x y h0 h1 h2 h3

theorem modeOneFrameActualPairProgramIff_kernel_certificate {m} (w mode depth P a b c e R S n q x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeOneFrameActualPairProgramIffSentence w mode depth P a b c e R S n q x y)) := TheoryTransport.sentence (source_modeOneFrameActualPairProgramIff w mode depth P a b c e R S n q x y)

theorem native_modeOneFrameActualPairProgramIff {m} (w mode depth P a b c e R S n q x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeOneFrameActualPairProgramIffSentence w mode depth P a b c e R S n q x y)) := ZFReplay.replay (modeOneFrameActualPairProgramIff_kernel_certificate w mode depth P a b c e R S n q x y)

def modeOneFrameActualPairAgreementSentence {m} (w mode depth P a b c e R S x y : Fin m) : Source.Sentence := ((omega w).imp ((AbstractOperationFrameSyntax.frame w mode depth P a b c e R S).imp ((ArgumentForestProgramSyntax.typedInputs 2 w a b (SyntaxAtomSyntax.two x y)).imp ((MemberPairAgreementSyntax.agreement w mode depth P R S c e x y))))).close

theorem source_modeOneFrameActualPairAgreement {m} (w mode depth P a b c e R S x y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeOneFrameActualPairAgreementSentence w mode depth P a b c e R S x y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ArgumentForestProgramSyntax.typedInputs 2 w a b (SyntaxAtomSyntax.two x y)) (Context.add (AbstractOperationFrameSyntax.frame w mode depth P a b c e R S) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (AbstractOperationFrameSyntax.frame w mode depth P a b c e R S) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (ArgumentForestProgramSyntax.typedInputs 2 w a b (SyntaxAtomSyntax.two x y)) := .hyp (Or.inl rfl)
  exact AbstractFrameAtomicAgreement.pair_agreement hZ w mode depth P a b c e R S x y h0 h1 h2

theorem modeOneFrameActualPairAgreement_kernel_certificate {m} (w mode depth P a b c e R S x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeOneFrameActualPairAgreementSentence w mode depth P a b c e R S x y)) := TheoryTransport.sentence (source_modeOneFrameActualPairAgreement w mode depth P a b c e R S x y)

theorem native_modeOneFrameActualPairAgreement {m} (w mode depth P a b c e R S x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeOneFrameActualPairAgreementSentence w mode depth P a b c e R S x y)) := ZFReplay.replay (modeOneFrameActualPairAgreement_kernel_certificate w mode depth P a b c e R S x y)

def modeOneFrameWholeConstantIffSentence {m} (truth : Bool) (w mode depth P a b c e R S n q : Fin m) : Source.Sentence := ((omega w).imp ((AbstractOperationFrameSyntax.frame w mode depth P a b c e R S).imp ((SyntaxAtomSyntax.nullary truth w a b n).imp (((OriginalTransformRowSyntax.run 3 w mode depth P n q).iff (FormulaTransformAtomSyntax.nullary truth w a b c e n q)))))).close

theorem source_modeOneFrameWholeConstantIff {m} (truth : Bool) (w mode depth P a b c e R S n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeOneFrameWholeConstantIffSentence truth w mode depth P a b c e R S n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxAtomSyntax.nullary truth w a b n) (Context.add (AbstractOperationFrameSyntax.frame w mode depth P a b c e R S) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (AbstractOperationFrameSyntax.frame w mode depth P a b c e R S) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxAtomSyntax.nullary truth w a b n) := .hyp (Or.inl rfl)
  exact AbstractFrameAtomicExisting.constant_iff hZ truth w mode depth P a b c e R S n q h0 h1 h2

theorem modeOneFrameWholeConstantIff_kernel_certificate {m} (truth : Bool) (w mode depth P a b c e R S n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeOneFrameWholeConstantIffSentence truth w mode depth P a b c e R S n q)) := TheoryTransport.sentence (source_modeOneFrameWholeConstantIff truth w mode depth P a b c e R S n q)

theorem native_modeOneFrameWholeConstantIff {m} (truth : Bool) (w mode depth P a b c e R S n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeOneFrameWholeConstantIffSentence truth w mode depth P a b c e R S n q)) := ZFReplay.replay (modeOneFrameWholeConstantIff_kernel_certificate truth w mode depth P a b c e R S n q)

def modeOneFrameWholeMembershipIffSentence {m} (w mode depth P a b c e R S n q : Fin m) : Source.Sentence := ((omega w).imp ((AbstractOperationFrameSyntax.frame w mode depth P a b c e R S).imp ((SyntaxAtomSyntax.membership w a b n).imp (((OriginalTransformRowSyntax.run 3 w mode depth P n q).iff (FormulaTransformAtomSyntax.membership w R S a b c e n q)))))).close

theorem source_modeOneFrameWholeMembershipIff {m} (w mode depth P a b c e R S n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeOneFrameWholeMembershipIffSentence w mode depth P a b c e R S n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxAtomSyntax.membership w a b n) (Context.add (AbstractOperationFrameSyntax.frame w mode depth P a b c e R S) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (AbstractOperationFrameSyntax.frame w mode depth P a b c e R S) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxAtomSyntax.membership w a b n) := .hyp (Or.inl rfl)
  exact AbstractFrameTypedAtomic.membership_iff hZ w mode depth P a b c e R S n q h0 h1 h2

theorem modeOneFrameWholeMembershipIff_kernel_certificate {m} (w mode depth P a b c e R S n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeOneFrameWholeMembershipIffSentence w mode depth P a b c e R S n q)) := TheoryTransport.sentence (source_modeOneFrameWholeMembershipIff w mode depth P a b c e R S n q)

theorem native_modeOneFrameWholeMembershipIff {m} (w mode depth P a b c e R S n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeOneFrameWholeMembershipIffSentence w mode depth P a b c e R S n q)) := ZFReplay.replay (modeOneFrameWholeMembershipIff_kernel_certificate w mode depth P a b c e R S n q)

def modeOneFrameWholeEqualityIffSentence {m} (w mode depth P a b c e R S n q : Fin m) : Source.Sentence := ((omega w).imp ((AbstractOperationFrameSyntax.frame w mode depth P a b c e R S).imp ((SyntaxAtomSyntax.equality w a b n).imp (((OriginalTransformRowSyntax.run 3 w mode depth P n q).iff (FormulaTransformAtomSyntax.equality w R S a b c e n q)))))).close

theorem source_modeOneFrameWholeEqualityIff {m} (w mode depth P a b c e R S n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeOneFrameWholeEqualityIffSentence w mode depth P a b c e R S n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxAtomSyntax.equality w a b n) (Context.add (AbstractOperationFrameSyntax.frame w mode depth P a b c e R S) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (AbstractOperationFrameSyntax.frame w mode depth P a b c e R S) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxAtomSyntax.equality w a b n) := .hyp (Or.inl rfl)
  exact AbstractFrameTypedAtomic.equality_iff hZ w mode depth P a b c e R S n q h0 h1 h2

theorem modeOneFrameWholeEqualityIff_kernel_certificate {m} (w mode depth P a b c e R S n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeOneFrameWholeEqualityIffSentence w mode depth P a b c e R S n q)) := TheoryTransport.sentence (source_modeOneFrameWholeEqualityIff w mode depth P a b c e R S n q)

theorem native_modeOneFrameWholeEqualityIff {m} (w mode depth P a b c e R S n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeOneFrameWholeEqualityIffSentence w mode depth P a b c e R S n q)) := ZFReplay.replay (modeOneFrameWholeEqualityIff_kernel_certificate w mode depth P a b c e R S n q)

def modeOneFrameAllAtomicWholeRunIffSentence {m} (w mode depth P a b c e R S n q : Fin m) : Source.Sentence := ((omega w).imp ((AbstractOperationFrameSyntax.frame w mode depth P a b c e R S).imp ((SyntaxAtomSyntax.atomic w a b n).imp (((OriginalTransformRowSyntax.run 3 w mode depth P n q).iff (FormulaAtomicProgramSyntax.run w R S a b c e n q)))))).close

theorem source_modeOneFrameAllAtomicWholeRunIff {m} (w mode depth P a b c e R S n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeOneFrameAllAtomicWholeRunIffSentence w mode depth P a b c e R S n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxAtomSyntax.atomic w a b n) (Context.add (AbstractOperationFrameSyntax.frame w mode depth P a b c e R S) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (AbstractOperationFrameSyntax.frame w mode depth P a b c e R S) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxAtomSyntax.atomic w a b n) := .hyp (Or.inl rfl)
  exact AbstractFrameAtomic.run_iff hZ w mode depth P a b c e R S n q h0 h1 h2

theorem modeOneFrameAllAtomicWholeRunIff_kernel_certificate {m} (w mode depth P a b c e R S n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeOneFrameAllAtomicWholeRunIffSentence w mode depth P a b c e R S n q)) := TheoryTransport.sentence (source_modeOneFrameAllAtomicWholeRunIff w mode depth P a b c e R S n q)

theorem native_modeOneFrameAllAtomicWholeRunIff {m} (w mode depth P a b c e R S n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeOneFrameAllAtomicWholeRunIffSentence w mode depth P a b c e R S n q)) := ZFReplay.replay (modeOneFrameAllAtomicWholeRunIff_kernel_certificate w mode depth P a b c e R S n q)

def modeOneFrameAllAtomicProgramIffSentence {m} (w mode depth P a b c e R S h n q : Fin m) : Source.Sentence := ((omega w).imp ((AbstractOperationFrameSyntax.frame w mode depth P a b c e R S).imp ((SyntaxAtomSyntax.atomic w a b n).imp (((OriginalTransformRowSyntax.run 3 w mode depth P n q).iff (FormulaTransformProgramSyntax.run FormulaAtomicProgramSyntax.program w R S a b c e h n q)))))).close

theorem source_modeOneFrameAllAtomicProgramIff {m} (w mode depth P a b c e R S h n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeOneFrameAllAtomicProgramIffSentence w mode depth P a b c e R S h n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxAtomSyntax.atomic w a b n) (Context.add (AbstractOperationFrameSyntax.frame w mode depth P a b c e R S) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (AbstractOperationFrameSyntax.frame w mode depth P a b c e R S) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxAtomSyntax.atomic w a b n) := .hyp (Or.inl rfl)
  exact AbstractFrameAtomic.program_iff hZ w mode depth P a b c e R S h n q h0 h1 h2

theorem modeOneFrameAllAtomicProgramIff_kernel_certificate {m} (w mode depth P a b c e R S h n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeOneFrameAllAtomicProgramIffSentence w mode depth P a b c e R S h n q)) := TheoryTransport.sentence (source_modeOneFrameAllAtomicProgramIff w mode depth P a b c e R S h n q)

theorem native_modeOneFrameAllAtomicProgramIff {m} (w mode depth P a b c e R S h n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeOneFrameAllAtomicProgramIffSentence w mode depth P a b c e R S h n q)) := ZFReplay.replay (modeOneFrameAllAtomicProgramIff_kernel_certificate w mode depth P a b c e R S h n q)

end PPAC.Migration.Internal.ObjectAbstractAtomicFormula
