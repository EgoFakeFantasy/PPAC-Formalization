import PPAC.Migration.Internal.PureProofSubstitutionTransform

/-! 原替换节点确切语法/变换查询的对象合同，接受关系独立于比较规格。 -/
namespace PPAC.Migration.Internal.ObjectPureProofSubstitutionQueries
open Source SourceAlgebra SourceLogic OmegaSyntax
open YesMetaZFC.Automation.ObjectHorn (Rule)

def termExprQueryIffSentence {m} (env : Fin 3 → Fin m) (w : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 3 w env).imp (((PureSyntaxExprQuery.query (YesMetaZFC.Automation.ObjectHorn.Expr.node (.literal 0) (List.ofFn (fun i : Fin 3 => YesMetaZFC.Automation.ObjectHorn.Expr.var i))) w env).iff (SyntaxTermSyntax.term w (env 0) (env 1) (env 2)))))).close

theorem source_termExprQueryIff {m} (env : Fin 3 → Fin m) (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (termExprQueryIffSentence env w) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.environmentNat 3 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 3 w env) := .hyp (Or.inl rfl)
  exact PureSyntaxQueryTyping.term_iff hZ (fun i : Fin 3 => YesMetaZFC.Automation.ObjectHorn.Expr.var i) w (env 0) (env 1) (env 2) env h0 h1 (fun i => Fin.cases (Derives.conjI (HornExprSyntax.environmentNat_at w env h1 0) (.eqRefl _)) (fun j0 => Fin.cases (Derives.conjI (HornExprSyntax.environmentNat_at w env h1 1) (.eqRefl _)) (fun j1 => Fin.cases (Derives.conjI (HornExprSyntax.environmentNat_at w env h1 2) (.eqRefl _)) (fun v => Fin.elim0 v) j1) j0) i)

theorem termExprQueryIff_kernel_certificate {m} (env : Fin 3 → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (termExprQueryIffSentence env w)) := TheoryTransport.sentence (source_termExprQueryIff env w)

theorem native_termExprQueryIff {m} (env : Fin 3 → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (termExprQueryIffSentence env w)) := ZFReplay.replay (termExprQueryIff_kernel_certificate env w)

def argumentsExprQueryIffSentence {m} (env : Fin 4 → Fin m) (w : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 4 w env).imp (((PureSyntaxExprQuery.query (YesMetaZFC.Automation.ObjectHorn.Expr.node (.literal 1) (List.ofFn (fun i : Fin 4 => YesMetaZFC.Automation.ObjectHorn.Expr.var i))) w env).iff (SyntaxMixedImageCodeSyntax.termList w (env 2) (env 0) (env 1) (env 3)))))).close

theorem source_argumentsExprQueryIff {m} (env : Fin 4 → Fin m) (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (argumentsExprQueryIffSentence env w) := by
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
  exact PureSyntaxQueryTyping.arguments_iff hZ (fun i : Fin 4 => YesMetaZFC.Automation.ObjectHorn.Expr.var i) w (env 0) (env 1) (env 2) (env 3) env h0 h1 (fun i => Fin.cases (Derives.conjI (HornExprSyntax.environmentNat_at w env h1 0) (.eqRefl _)) (fun j0 => Fin.cases (Derives.conjI (HornExprSyntax.environmentNat_at w env h1 1) (.eqRefl _)) (fun j1 => Fin.cases (Derives.conjI (HornExprSyntax.environmentNat_at w env h1 2) (.eqRefl _)) (fun j2 => Fin.cases (Derives.conjI (HornExprSyntax.environmentNat_at w env h1 3) (.eqRefl _)) (fun v => Fin.elim0 v) j2) j1) j0) i)

theorem argumentsExprQueryIff_kernel_certificate {m} (env : Fin 4 → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (argumentsExprQueryIffSentence env w)) := TheoryTransport.sentence (source_argumentsExprQueryIff env w)

theorem native_argumentsExprQueryIff {m} (env : Fin 4 → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (argumentsExprQueryIffSentence env w)) := ZFReplay.replay (argumentsExprQueryIff_kernel_certificate env w)

def formulaExprQueryIffSentence {m} (env : Fin 3 → Fin m) (w : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 3 w env).imp (((PureSyntaxExprQuery.query (YesMetaZFC.Automation.ObjectHorn.Expr.node (.literal 4) (List.ofFn (fun i : Fin 3 => YesMetaZFC.Automation.ObjectHorn.Expr.var i))) w env).iff (FormulaCodeSyntax.formulaCode w (env 2) (env 0) (env 1)))))).close

theorem source_formulaExprQueryIff {m} (env : Fin 3 → Fin m) (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (formulaExprQueryIffSentence env w) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.environmentNat 3 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 3 w env) := .hyp (Or.inl rfl)
  exact PureSyntaxQueryTyping.formula_iff hZ (fun i : Fin 3 => YesMetaZFC.Automation.ObjectHorn.Expr.var i) w (env 0) (env 1) (env 2) env h0 h1 (fun i => Fin.cases (Derives.conjI (HornExprSyntax.environmentNat_at w env h1 0) (.eqRefl _)) (fun j0 => Fin.cases (Derives.conjI (HornExprSyntax.environmentNat_at w env h1 1) (.eqRefl _)) (fun j1 => Fin.cases (Derives.conjI (HornExprSyntax.environmentNat_at w env h1 2) (.eqRefl _)) (fun v => Fin.elim0 v) j1) j0) i)

theorem formulaExprQueryIff_kernel_certificate {m} (env : Fin 3 → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (formulaExprQueryIffSentence env w)) := TheoryTransport.sentence (source_formulaExprQueryIff env w)

theorem native_formulaExprQueryIff {m} (env : Fin 3 → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (formulaExprQueryIffSentence env w)) := ZFReplay.replay (formulaExprQueryIff_kernel_certificate env w)

def substitutionFormulaQueryIffSentence {m} (env : Fin 6 → Fin m) (w z : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 6 w env).imp ((empty z).imp (((PureSyntaxExprQuery.query PureProofSubstitutionQueries.substitutionFormula w env).iff (FormulaCodeSyntax.formulaCode w (env 5) z (env 2))))))).close

theorem source_substitutionFormulaQueryIff {m} (env : Fin 6 → Fin m) (w z : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (substitutionFormulaQueryIffSentence env w z) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (empty z) (Context.add (HornExprSyntax.environmentNat 6 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 6 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (empty z) := .hyp (Or.inl rfl)
  exact PureProofSubstitutionQueries.substitution_formula_iff hZ w z env h0 h1 h2

theorem substitutionFormulaQueryIff_kernel_certificate {m} (env : Fin 6 → Fin m) (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (substitutionFormulaQueryIffSentence env w z)) := TheoryTransport.sentence (source_substitutionFormulaQueryIff env w z)

theorem native_substitutionFormulaQueryIff {m} (env : Fin 6 → Fin m) (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (substitutionFormulaQueryIffSentence env w z)) := ZFReplay.replay (substitutionFormulaQueryIff_kernel_certificate env w z)

def substitutionArgumentsQueryIffSentence {m} (env : Fin 6 → Fin m) (w z : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 6 w env).imp ((empty z).imp (((PureSyntaxExprQuery.query PureProofSubstitutionQueries.substitutionArguments w env).iff (SyntaxMixedImageCodeSyntax.termList w (env 2) z (env 0) (env 3))))))).close

theorem source_substitutionArgumentsQueryIff {m} (env : Fin 6 → Fin m) (w z : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (substitutionArgumentsQueryIffSentence env w z) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (empty z) (Context.add (HornExprSyntax.environmentNat 6 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 6 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (empty z) := .hyp (Or.inl rfl)
  exact PureProofSubstitutionQueries.substitution_arguments_iff hZ w z env h0 h1 h2

theorem substitutionArgumentsQueryIff_kernel_certificate {m} (env : Fin 6 → Fin m) (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (substitutionArgumentsQueryIffSentence env w z)) := TheoryTransport.sentence (source_substitutionArgumentsQueryIff env w z)

theorem native_substitutionArgumentsQueryIff {m} (env : Fin 6 → Fin m) (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (substitutionArgumentsQueryIffSentence env w z)) := ZFReplay.replay (substitutionArgumentsQueryIff_kernel_certificate env w z)

def substitutionTransformAtModeIffSentence {m} (env : Fin 6 → Fin m) (w z mode : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 6 w env).imp ((empty z).imp ((SyntaxNumeralSyntax.numeral 3 mode).imp (((OriginalTransformExprQuery.query PureProofSubstitutionQueries.substitutionTransform w env).iff (OriginalTransformRowSyntax.run 3 w mode z (env 3) (env 5) (env 1)))))))).close

theorem source_substitutionTransformAtModeIff {m} (env : Fin 6 → Fin m) (w z mode : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (substitutionTransformAtModeIffSentence env w z mode) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNumeralSyntax.numeral 3 mode) (Context.add (empty z) (Context.add (HornExprSyntax.environmentNat 6 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 6 w env) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (empty z) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxNumeralSyntax.numeral 3 mode) := .hyp (Or.inl rfl)
  exact PureProofSubstitutionTransform.transform_query_at_mode hZ w z mode env h0 h1 h2 h3

theorem substitutionTransformAtModeIff_kernel_certificate {m} (env : Fin 6 → Fin m) (w z mode : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (substitutionTransformAtModeIffSentence env w z mode)) := TheoryTransport.sentence (source_substitutionTransformAtModeIff env w z mode)

theorem native_substitutionTransformAtModeIff {m} (env : Fin 6 → Fin m) (w z mode : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (substitutionTransformAtModeIffSentence env w z mode)) := ZFReplay.replay (substitutionTransformAtModeIff_kernel_certificate env w z mode)

def substitutionGuardedTransformIffSentence {m} (env : Fin 6 → Fin m) (w z : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 6 w env).imp ((empty z).imp ((PureSyntaxExprQuery.query PureProofSubstitutionQueries.substitutionFormula w env).imp ((PureSyntaxExprQuery.query PureProofSubstitutionQueries.substitutionArguments w env).imp (((OriginalTransformExprQuery.query PureProofSubstitutionQueries.substitutionTransform w env).iff (FreeSubstProgramSyntax.executed w z (env 2) (env 0) (env 3) (env 5) (env 1))))))))).close

theorem source_substitutionGuardedTransformIff {m} (env : Fin 6 → Fin m) (w z : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (substitutionGuardedTransformIffSentence env w z) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PureSyntaxExprQuery.query PureProofSubstitutionQueries.substitutionArguments w env) (Context.add (PureSyntaxExprQuery.query PureProofSubstitutionQueries.substitutionFormula w env) (Context.add (empty z) (Context.add (HornExprSyntax.environmentNat 6 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 6 w env) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (empty z) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (PureSyntaxExprQuery.query PureProofSubstitutionQueries.substitutionFormula w env) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (PureSyntaxExprQuery.query PureProofSubstitutionQueries.substitutionArguments w env) := .hyp (Or.inl rfl)
  exact PureProofSubstitutionTransform.guarded_query_iff hZ w z env h0 h1 h2 h3 h4

theorem substitutionGuardedTransformIff_kernel_certificate {m} (env : Fin 6 → Fin m) (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (substitutionGuardedTransformIffSentence env w z)) := TheoryTransport.sentence (source_substitutionGuardedTransformIff env w z)

theorem native_substitutionGuardedTransformIff {m} (env : Fin 6 → Fin m) (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (substitutionGuardedTransformIffSentence env w z)) := ZFReplay.replay (substitutionGuardedTransformIff_kernel_certificate env w z)

def substitutionBundleIffSentence {m} (env : Fin 6 → Fin m) (w z : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 6 w env).imp ((empty z).imp (((PureProofSubstitutionTransform.bundle w env).iff (PureProofSubstitutionTransform.specification w z env)))))).close

theorem source_substitutionBundleIff {m} (env : Fin 6 → Fin m) (w z : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (substitutionBundleIffSentence env w z) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (empty z) (Context.add (HornExprSyntax.environmentNat 6 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 6 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (empty z) := .hyp (Or.inl rfl)
  exact PureProofSubstitutionTransform.bundle_iff hZ w z env h0 h1 h2

theorem substitutionBundleIff_kernel_certificate {m} (env : Fin 6 → Fin m) (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (substitutionBundleIffSentence env w z)) := TheoryTransport.sentence (source_substitutionBundleIff env w z)

theorem native_substitutionBundleIff {m} (env : Fin 6 → Fin m) (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (substitutionBundleIffSentence env w z)) := ZFReplay.replay (substitutionBundleIff_kernel_certificate env w z)

end PPAC.Migration.Internal.ObjectPureProofSubstitutionQueries
