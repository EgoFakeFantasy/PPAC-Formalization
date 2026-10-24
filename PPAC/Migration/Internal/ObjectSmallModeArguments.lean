import PPAC.Migration.Internal.SmallModeArgumentsRun
import PPAC.Migration.Internal.AbstractTermValue

/-! 原k<4参数列完整方程及mode1全部纯项数值对应的原核闭句。 -/
namespace PPAC.Migration.Internal.ObjectSmallModeArguments
open Source SourceAlgebra SourceLogic OmegaSyntax

def smallModeOriginalNilGuardSentence {m} (k : Fin 4) (env : Fin 3 → Fin m) (w : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 3 w env).imp ((SyntaxNumeralSyntax.numeral k.val (env 0)).imp ((HornRuleSyntax.guards YesMetaZFC.Automation.ObjectSyntaxTransform.nilArguments.guards w env))))).close

theorem source_smallModeOriginalNilGuard {m} (k : Fin 4) (env : Fin 3 → Fin m) (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (smallModeOriginalNilGuardSentence k env w) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNumeralSyntax.numeral k.val (env 0)) (Context.add (HornExprSyntax.environmentNat 3 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 3 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral k.val (env 0)) := .hyp (Or.inl rfl)
  exact SmallModeArgumentsGuard.nil_guard hZ k.val k.isLt w env h0 h1 h2

theorem smallModeOriginalNilGuard_kernel_certificate {m} (k : Fin 4) (env : Fin 3 → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (smallModeOriginalNilGuardSentence k env w)) := TheoryTransport.sentence (source_smallModeOriginalNilGuard k env w)

theorem native_smallModeOriginalNilGuard {m} (k : Fin 4) (env : Fin 3 → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (smallModeOriginalNilGuardSentence k env w)) := ZFReplay.replay (smallModeOriginalNilGuard_kernel_certificate k env w)

def smallModeOriginalNilMatrixIffSentence {m} (k : Fin 4) (env : Fin 3 → Fin m) (w n q r : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 3 w env).imp ((SyntaxNumeralSyntax.numeral k.val (env 0)).imp ((StructuralListSyntax.nilCode w n).imp ((StructuralListSyntax.nilCode w q).imp (((HornUniversalTraceRules.tracedMatrix YesMetaZFC.Automation.ObjectSyntaxTransform.nilArguments w r env).iff (OriginalTransformRowSyntax.row 2 w (env 0) (env 1) (env 2) n q r)))))))).close

theorem source_smallModeOriginalNilMatrixIff {m} (k : Fin 4) (env : Fin 3 → Fin m) (w n q r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (smallModeOriginalNilMatrixIffSentence k env w n q r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralListSyntax.nilCode w q) (Context.add (StructuralListSyntax.nilCode w n) (Context.add (SyntaxNumeralSyntax.numeral k.val (env 0)) (Context.add (HornExprSyntax.environmentNat 3 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 3 w env) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral k.val (env 0)) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (StructuralListSyntax.nilCode w n) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (StructuralListSyntax.nilCode w q) := .hyp (Or.inl rfl)
  exact SmallModeArgumentsNil.nil_matrix_iff hZ k.val k.isLt w n q r env h0 h1 h2 h3 h4

theorem smallModeOriginalNilMatrixIff_kernel_certificate {m} (k : Fin 4) (env : Fin 3 → Fin m) (w n q r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (smallModeOriginalNilMatrixIffSentence k env w n q r)) := TheoryTransport.sentence (source_smallModeOriginalNilMatrixIff k env w n q r)

theorem native_smallModeOriginalNilMatrixIff {m} (k : Fin 4) (env : Fin 3 → Fin m) (w n q r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (smallModeOriginalNilMatrixIffSentence k env w n q r)) := ZFReplay.replay (smallModeOriginalNilMatrixIff_kernel_certificate k env w n q r)

def smallModeOriginalNilAtRowIffSentence {m} (k : Fin 4) (env : Fin 3 → Fin m) (w n q r : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 3 w env).imp ((SyntaxNumeralSyntax.numeral k.val (env 0)).imp ((OriginalTransformRowSyntax.row 2 w (env 0) (env 1) (env 2) n q r).imp (((HornUniversalTraceRules.tracedMatrix YesMetaZFC.Automation.ObjectSyntaxTransform.nilArguments w r env).iff ((StructuralListSyntax.nilCode w n).conj (StructuralListSyntax.nilCode w q)))))))).close

theorem source_smallModeOriginalNilAtRowIff {m} (k : Fin 4) (env : Fin 3 → Fin m) (w n q r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (smallModeOriginalNilAtRowIffSentence k env w n q r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (OriginalTransformRowSyntax.row 2 w (env 0) (env 1) (env 2) n q r) (Context.add (SyntaxNumeralSyntax.numeral k.val (env 0)) (Context.add (HornExprSyntax.environmentNat 3 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 3 w env) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral k.val (env 0)) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (OriginalTransformRowSyntax.row 2 w (env 0) (env 1) (env 2) n q r) := .hyp (Or.inl rfl)
  exact SmallModeArgumentsNil.nil_at_row hZ k.val k.isLt w n q r env h0 h1 h2 h3

theorem smallModeOriginalNilAtRowIff_kernel_certificate {m} (k : Fin 4) (env : Fin 3 → Fin m) (w n q r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (smallModeOriginalNilAtRowIffSentence k env w n q r)) := TheoryTransport.sentence (source_smallModeOriginalNilAtRowIff k env w n q r)

theorem native_smallModeOriginalNilAtRowIff {m} (k : Fin 4) (env : Fin 3 → Fin m) (w n q r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (smallModeOriginalNilAtRowIffSentence k env w n q r)) := ZFReplay.replay (smallModeOriginalNilAtRowIff_kernel_certificate k env w n q r)

def smallModeOriginalNilApplicationIffSentence {m} (k : Fin 4) (w mode depth parameter input output r V : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral k.val mode).imp ((OriginalTransformRowSyntax.row 2 w mode depth parameter input output r).imp ((HornUniversalTraceSyntax.value w V).imp (((HornApplicationSyntax.application YesMetaZFC.Automation.ObjectSyntaxTransform.nilArguments w r V).iff (OriginalArgumentCaseSyntax.nilData w input output))))))).close

theorem source_smallModeOriginalNilApplicationIff {m} (k : Fin 4) (w mode depth parameter input output r V : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (smallModeOriginalNilApplicationIffSentence k w mode depth parameter input output r V) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornUniversalTraceSyntax.value w V) (Context.add (OriginalTransformRowSyntax.row 2 w mode depth parameter input output r) (Context.add (SyntaxNumeralSyntax.numeral k.val mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral k.val mode) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (OriginalTransformRowSyntax.row 2 w mode depth parameter input output r) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (HornUniversalTraceSyntax.value w V) := .hyp (Or.inl rfl)
  exact SmallModeArgumentsNilApplication.application_iff hZ k.val k.isLt w mode depth parameter input output r V h0 h1 h2 h3

theorem smallModeOriginalNilApplicationIff_kernel_certificate {m} (k : Fin 4) (w mode depth parameter input output r V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (smallModeOriginalNilApplicationIffSentence k w mode depth parameter input output r V)) := TheoryTransport.sentence (source_smallModeOriginalNilApplicationIff k w mode depth parameter input output r V)

theorem native_smallModeOriginalNilApplicationIff {m} (k : Fin 4) (w mode depth parameter input output r V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (smallModeOriginalNilApplicationIffSentence k w mode depth parameter input output r V)) := ZFReplay.replay (smallModeOriginalNilApplicationIff_kernel_certificate k w mode depth parameter input output r V)

def smallModeArgumentTraceAtActualValueIffSentence {m} (k : Fin 4) (w mode depth parameter input output r V : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral k.val mode).imp ((OriginalTransformRowSyntax.row 2 w mode depth parameter input output r).imp ((HornUniversalTraceSyntax.value w V).imp (((HornLookupConditionSyntax.condition w r).iff (OriginalArgumentCaseSyntax.outcomes w mode depth parameter input output))))))).close

theorem source_smallModeArgumentTraceAtActualValueIff {m} (k : Fin 4) (w mode depth parameter input output r V : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (smallModeArgumentTraceAtActualValueIffSentence k w mode depth parameter input output r V) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornUniversalTraceSyntax.value w V) (Context.add (OriginalTransformRowSyntax.row 2 w mode depth parameter input output r) (Context.add (SyntaxNumeralSyntax.numeral k.val mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral k.val mode) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (OriginalTransformRowSyntax.row 2 w mode depth parameter input output r) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (HornUniversalTraceSyntax.value w V) := .hyp (Or.inl rfl)
  exact SmallModeArgumentsTrace.at_row_value hZ k.val k.isLt w mode depth parameter input output r V h0 h1 h2 h3

theorem smallModeArgumentTraceAtActualValueIff_kernel_certificate {m} (k : Fin 4) (w mode depth parameter input output r V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (smallModeArgumentTraceAtActualValueIffSentence k w mode depth parameter input output r V)) := TheoryTransport.sentence (source_smallModeArgumentTraceAtActualValueIff k w mode depth parameter input output r V)

theorem native_smallModeArgumentTraceAtActualValueIff {m} (k : Fin 4) (w mode depth parameter input output r V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (smallModeArgumentTraceAtActualValueIffSentence k w mode depth parameter input output r V)) := ZFReplay.replay (smallModeArgumentTraceAtActualValueIff_kernel_certificate k w mode depth parameter input output r V)

def smallModeArgumentTraceIffSentence {m} (k : Fin 4) (w mode depth parameter input output r : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral k.val mode).imp ((OriginalTransformRowSyntax.row 2 w mode depth parameter input output r).imp (((HornLookupConditionSyntax.condition w r).iff (OriginalArgumentCaseSyntax.outcomes w mode depth parameter input output)))))).close

theorem source_smallModeArgumentTraceIff {m} (k : Fin 4) (w mode depth parameter input output r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (smallModeArgumentTraceIffSentence k w mode depth parameter input output r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (OriginalTransformRowSyntax.row 2 w mode depth parameter input output r) (Context.add (SyntaxNumeralSyntax.numeral k.val mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral k.val mode) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (OriginalTransformRowSyntax.row 2 w mode depth parameter input output r) := .hyp (Or.inl rfl)
  exact SmallModeArgumentsTrace.at_row hZ k.val k.isLt w mode depth parameter input output r h0 h1 h2

theorem smallModeArgumentTraceIff_kernel_certificate {m} (k : Fin 4) (w mode depth parameter input output r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (smallModeArgumentTraceIffSentence k w mode depth parameter input output r)) := TheoryTransport.sentence (source_smallModeArgumentTraceIff k w mode depth parameter input output r)

theorem native_smallModeArgumentTraceIff {m} (k : Fin 4) (w mode depth parameter input output r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (smallModeArgumentTraceIffSentence k w mode depth parameter input output r)) := ZFReplay.replay (smallModeArgumentTraceIff_kernel_certificate k w mode depth parameter input output r)

def smallModeArgumentWholeRunIffSentence {m} (k : Fin 4) (w mode depth parameter input output : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral k.val mode).imp ((Formula.mem depth w).imp ((Formula.mem parameter w).imp (((OriginalTransformRowSyntax.run 2 w mode depth parameter input output).iff (OriginalArgumentCaseSyntax.outcomes w mode depth parameter input output))))))).close

theorem source_smallModeArgumentWholeRunIff {m} (k : Fin 4) (w mode depth parameter input output : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (smallModeArgumentWholeRunIffSentence k w mode depth parameter input output) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem parameter w) (Context.add (Formula.mem depth w) (Context.add (SyntaxNumeralSyntax.numeral k.val mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral k.val mode) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (Formula.mem depth w) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (Formula.mem parameter w) := .hyp (Or.inl rfl)
  exact SmallModeArgumentsRun.run_iff hZ k.val k.isLt w mode depth parameter input output h0 h1 h2 h3

theorem smallModeArgumentWholeRunIff_kernel_certificate {m} (k : Fin 4) (w mode depth parameter input output : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (smallModeArgumentWholeRunIffSentence k w mode depth parameter input output)) := TheoryTransport.sentence (source_smallModeArgumentWholeRunIff k w mode depth parameter input output)

theorem native_smallModeArgumentWholeRunIff {m} (k : Fin 4) (w mode depth parameter input output : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (smallModeArgumentWholeRunIffSentence k w mode depth parameter input output)) := ZFReplay.replay (smallModeArgumentWholeRunIff_kernel_certificate k w mode depth parameter input output)

def modeOnePureTermGuardedNumericIffSentence {m} (w mode depth P a b n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 1 mode).imp ((OriginalTermTraceSyntax.metadata w depth P).imp ((((SyntaxTermSyntax.term w a b n).conj (OriginalTransformRowSyntax.run 1 w mode depth P n q)).iff (AbstractTermValueSyntax.value w a b depth n q)))))).close

theorem source_modeOnePureTermGuardedNumericIff {m} (w mode depth P a b n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeOnePureTermGuardedNumericIffSentence w mode depth P a b n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (OriginalTermTraceSyntax.metadata w depth P) (Context.add (SyntaxNumeralSyntax.numeral 1 mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 1 mode) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (OriginalTermTraceSyntax.metadata w depth P) := .hyp (Or.inl rfl)
  exact AbstractTermValue.guarded_iff hZ w mode depth P a b n q h0 h1 h2

theorem modeOnePureTermGuardedNumericIff_kernel_certificate {m} (w mode depth P a b n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeOnePureTermGuardedNumericIffSentence w mode depth P a b n q)) := TheoryTransport.sentence (source_modeOnePureTermGuardedNumericIff w mode depth P a b n q)

theorem native_modeOnePureTermGuardedNumericIff {m} (w mode depth P a b n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeOnePureTermGuardedNumericIffSentence w mode depth P a b n q)) := ZFReplay.replay (modeOnePureTermGuardedNumericIff_kernel_certificate w mode depth P a b n q)

def modeOnePureTermTypedNumericIffSentence {m} (w mode depth P a b n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 1 mode).imp ((OriginalTermTraceSyntax.metadata w depth P).imp ((SyntaxTermSyntax.term w a b n).imp (((OriginalTransformRowSyntax.run 1 w mode depth P n q).iff (AbstractTermValueSyntax.value w a b depth n q))))))).close

theorem source_modeOnePureTermTypedNumericIff {m} (w mode depth P a b n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeOnePureTermTypedNumericIffSentence w mode depth P a b n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTermSyntax.term w a b n) (Context.add (OriginalTermTraceSyntax.metadata w depth P) (Context.add (SyntaxNumeralSyntax.numeral 1 mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 1 mode) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (OriginalTermTraceSyntax.metadata w depth P) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxTermSyntax.term w a b n) := .hyp (Or.inl rfl)
  exact AbstractTermValue.typed_iff hZ w mode depth P a b n q h0 h1 h2 h3

theorem modeOnePureTermTypedNumericIff_kernel_certificate {m} (w mode depth P a b n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeOnePureTermTypedNumericIffSentence w mode depth P a b n q)) := TheoryTransport.sentence (source_modeOnePureTermTypedNumericIff w mode depth P a b n q)

theorem native_modeOnePureTermTypedNumericIff {m} (w mode depth P a b n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeOnePureTermTypedNumericIffSentence w mode depth P a b n q)) := ZFReplay.replay (modeOnePureTermTypedNumericIff_kernel_certificate w mode depth P a b n q)

def modeOneTermScopeBranchNumericSentence {m} (bound : Bool) (w mode depth P limit n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 1 mode).imp ((OriginalTermTraceSyntax.metadata w depth P).imp ((SyntaxTermSyntax.branch bound w limit n).imp ((OriginalTransformRowSyntax.run 1 w mode depth P n q).imp ((AbstractTermValueSyntax.branch bound w limit depth n q))))))).close

theorem source_modeOneTermScopeBranchNumeric {m} (bound : Bool) (w mode depth P limit n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeOneTermScopeBranchNumericSentence bound w mode depth P limit n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (OriginalTransformRowSyntax.run 1 w mode depth P n q) (Context.add (SyntaxTermSyntax.branch bound w limit n) (Context.add (OriginalTermTraceSyntax.metadata w depth P) (Context.add (SyntaxNumeralSyntax.numeral 1 mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 1 mode) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (OriginalTermTraceSyntax.metadata w depth P) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (SyntaxTermSyntax.branch bound w limit n) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (OriginalTransformRowSyntax.run 1 w mode depth P n q) := .hyp (Or.inl rfl)
  exact AbstractTermValue.from_scope_branch hZ bound w mode depth P limit n q h0 h1 h2 h3 h4

theorem modeOneTermScopeBranchNumeric_kernel_certificate {m} (bound : Bool) (w mode depth P limit n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeOneTermScopeBranchNumericSentence bound w mode depth P limit n q)) := TheoryTransport.sentence (source_modeOneTermScopeBranchNumeric bound w mode depth P limit n q)

theorem native_modeOneTermScopeBranchNumeric {m} (bound : Bool) (w mode depth P limit n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeOneTermScopeBranchNumericSentence bound w mode depth P limit n q)) := ZFReplay.replay (modeOneTermScopeBranchNumeric_kernel_certificate bound w mode depth P limit n q)

def modeOneTermNumericBranchRunSentence {m} (bound : Bool) (w mode depth P limit n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 1 mode).imp ((OriginalTermTraceSyntax.metadata w depth P).imp ((AbstractTermValueSyntax.branch bound w limit depth n q).imp ((OriginalTransformRowSyntax.run 1 w mode depth P n q)))))).close

theorem source_modeOneTermNumericBranchRun {m} (bound : Bool) (w mode depth P limit n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeOneTermNumericBranchRunSentence bound w mode depth P limit n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (AbstractTermValueSyntax.branch bound w limit depth n q) (Context.add (OriginalTermTraceSyntax.metadata w depth P) (Context.add (SyntaxNumeralSyntax.numeral 1 mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 1 mode) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (OriginalTermTraceSyntax.metadata w depth P) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (AbstractTermValueSyntax.branch bound w limit depth n q) := .hyp (Or.inl rfl)
  exact AbstractTermValue.branch_to_run hZ bound w mode depth P limit n q h0 h1 h2 h3

theorem modeOneTermNumericBranchRun_kernel_certificate {m} (bound : Bool) (w mode depth P limit n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeOneTermNumericBranchRunSentence bound w mode depth P limit n q)) := TheoryTransport.sentence (source_modeOneTermNumericBranchRun bound w mode depth P limit n q)

theorem native_modeOneTermNumericBranchRun {m} (bound : Bool) (w mode depth P limit n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeOneTermNumericBranchRunSentence bound w mode depth P limit n q)) := ZFReplay.replay (modeOneTermNumericBranchRun_kernel_certificate bound w mode depth P limit n q)

end PPAC.Migration.Internal.ObjectSmallModeArguments
