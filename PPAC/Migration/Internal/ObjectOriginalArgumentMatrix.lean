import PPAC.Migration.Internal.OriginalArgumentsRowCases

/-! 原参数列表实际数值矩阵及全部内部候选行精确刻画的原核证书。 -/
namespace PPAC.Migration.Internal.ObjectOriginalArgumentMatrix
open Source SourceAlgebra SourceLogic OmegaSyntax
open YesMetaZFC.Automation.ObjectHorn (Rule)

def nilModeZeroThreeGuardSentence {m} (three : Bool) (env : Fin 3 → Fin m) (w : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 3 w env).imp ((SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) (env 0)).imp ((HornRuleSyntax.guards (YesMetaZFC.Automation.ObjectSyntaxTransform.nilArguments).guards w env))))).close

theorem source_nilModeZeroThreeGuard {m} (three : Bool) (env : Fin 3 → Fin m) (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (nilModeZeroThreeGuardSentence three env w) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) (env 0)) (Context.add (HornExprSyntax.environmentNat 3 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 3 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) (env 0)) := .hyp (Or.inl rfl)
  exact OriginalArgumentsModeGuard.nil_guard hZ three w env h0 h1 h2

theorem nilModeZeroThreeGuard_kernel_certificate {m} (three : Bool) (env : Fin 3 → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (nilModeZeroThreeGuardSentence three env w)) := TheoryTransport.sentence (source_nilModeZeroThreeGuard three env w)

theorem native_nilModeZeroThreeGuard {m} (three : Bool) (env : Fin 3 → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (nilModeZeroThreeGuardSentence three env w)) := ZFReplay.replay (nilModeZeroThreeGuard_kernel_certificate three env w)

def allCandidateEmptyExprNilIffSentence {m} (arity : Nat) (env : Fin arity → Fin m) (w y : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat arity w env).imp (((HornExprSyntax.graph (YesMetaZFC.Automation.ObjectHorn.Expr.list []) w env y).iff (StructuralListSyntax.nilCode w y))))).close

theorem source_allCandidateEmptyExprNilIff {m} (arity : Nat) (env : Fin arity → Fin m) (w y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (allCandidateEmptyExprNilIffSentence arity env w y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.environmentNat arity w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (HornExprSyntax.environmentNat arity w env) := .hyp (Or.inl rfl)
  exact OriginalArgumentsNilValue.nil_iff hZ w y env h0 h1

theorem allCandidateEmptyExprNilIff_kernel_certificate {m} (arity : Nat) (env : Fin arity → Fin m) (w y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (allCandidateEmptyExprNilIffSentence arity env w y)) := TheoryTransport.sentence (source_allCandidateEmptyExprNilIff arity env w y)

theorem native_allCandidateEmptyExprNilIff {m} (arity : Nat) (env : Fin arity → Fin m) (w y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (allCandidateEmptyExprNilIffSentence arity env w y)) := ZFReplay.replay (allCandidateEmptyExprNilIff_kernel_certificate arity env w y)

def nilActualHeadNumericIffSentence {m} (env : Fin 3 → Fin m) (w n q r : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 3 w env).imp ((StructuralListSyntax.nilCode w n).imp ((StructuralListSyntax.nilCode w q).imp (((HornExprSyntax.graph (YesMetaZFC.Automation.ObjectSyntaxTransform.nilArguments).head w env r).iff (OriginalTransformRowSyntax.row 2 w (env 0) (env 1) (env 2) n q r))))))).close

theorem source_nilActualHeadNumericIff {m} (env : Fin 3 → Fin m) (w n q r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (nilActualHeadNumericIffSentence env w n q r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralListSyntax.nilCode w q) (Context.add (StructuralListSyntax.nilCode w n) (Context.add (HornExprSyntax.environmentNat 3 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 3 w env) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (StructuralListSyntax.nilCode w n) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (StructuralListSyntax.nilCode w q) := .hyp (Or.inl rfl)
  exact OriginalArgumentsExpr.nil_head_iff hZ w n q r env h0 h1 h2 h3

theorem nilActualHeadNumericIff_kernel_certificate {m} (env : Fin 3 → Fin m) (w n q r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (nilActualHeadNumericIffSentence env w n q r)) := TheoryTransport.sentence (source_nilActualHeadNumericIff env w n q r)

theorem native_nilActualHeadNumericIff {m} (env : Fin 3 → Fin m) (w n q r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (nilActualHeadNumericIffSentence env w n q r)) := ZFReplay.replay (nilActualHeadNumericIff_kernel_certificate env w n q r)

def consActualHeadNumericIffSentence {m} (env : Fin 7 → Fin m) (w n q r : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 7 w env).imp ((StructuralListSyntax.consCode w (env 3) (env 4) n).imp ((StructuralListSyntax.consCode w (env 5) (env 6) q).imp (((HornExprSyntax.graph (YesMetaZFC.Automation.ObjectSyntaxTransform.consArguments).head w env r).iff (OriginalTransformRowSyntax.row 2 w (env 0) (env 1) (env 2) n q r))))))).close

theorem source_consActualHeadNumericIff {m} (env : Fin 7 → Fin m) (w n q r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (consActualHeadNumericIffSentence env w n q r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralListSyntax.consCode w (env 5) (env 6) q) (Context.add (StructuralListSyntax.consCode w (env 3) (env 4) n) (Context.add (HornExprSyntax.environmentNat 7 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 7 w env) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (StructuralListSyntax.consCode w (env 3) (env 4) n) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (StructuralListSyntax.consCode w (env 5) (env 6) q) := .hyp (Or.inl rfl)
  exact OriginalArgumentsExpr.cons_head_iff hZ w n q r env h0 h1 h2 h3

theorem consActualHeadNumericIff_kernel_certificate {m} (env : Fin 7 → Fin m) (w n q r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (consActualHeadNumericIffSentence env w n q r)) := TheoryTransport.sentence (source_consActualHeadNumericIff env w n q r)

theorem native_consActualHeadNumericIff {m} (env : Fin 7 → Fin m) (w n q r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (consActualHeadNumericIffSentence env w n q r)) := ZFReplay.replay (consActualHeadNumericIff_kernel_certificate env w n q r)

def headActualChildTraceNumericIffSentence {m} (env : Fin 7 → Fin m) (w : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 7 w env).imp (((HornUniversalTraceRules.tracedPremise OriginalArgumentsTraceRules.headPremise w env).iff (OriginalTransformRowSyntax.run 1 w (env 0) (env 1) (env 2) (env 3) (env 5)))))).close

theorem source_headActualChildTraceNumericIff {m} (env : Fin 7 → Fin m) (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (headActualChildTraceNumericIffSentence env w) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.environmentNat 7 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 7 w env) := .hyp (Or.inl rfl)
  exact OriginalArgumentsRuleMatrix.head_child_iff hZ w env h0 h1

theorem headActualChildTraceNumericIff_kernel_certificate {m} (env : Fin 7 → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (headActualChildTraceNumericIffSentence env w)) := TheoryTransport.sentence (source_headActualChildTraceNumericIff env w)

theorem native_headActualChildTraceNumericIff {m} (env : Fin 7 → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (headActualChildTraceNumericIffSentence env w)) := ZFReplay.replay (headActualChildTraceNumericIff_kernel_certificate env w)

def tailActualChildTraceNumericIffSentence {m} (env : Fin 7 → Fin m) (w : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 7 w env).imp (((HornUniversalTraceRules.tracedPremise OriginalArgumentsTraceRules.tailPremise w env).iff (OriginalTransformRowSyntax.run 2 w (env 0) (env 1) (env 2) (env 4) (env 6)))))).close

theorem source_tailActualChildTraceNumericIff {m} (env : Fin 7 → Fin m) (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (tailActualChildTraceNumericIffSentence env w) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.environmentNat 7 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 7 w env) := .hyp (Or.inl rfl)
  exact OriginalArgumentsRuleMatrix.tail_child_iff hZ w env h0 h1

theorem tailActualChildTraceNumericIff_kernel_certificate {m} (env : Fin 7 → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (tailActualChildTraceNumericIffSentence env w)) := TheoryTransport.sentence (source_tailActualChildTraceNumericIff env w)

theorem native_tailActualChildTraceNumericIff {m} (env : Fin 7 → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (tailActualChildTraceNumericIffSentence env w)) := ZFReplay.replay (tailActualChildTraceNumericIff_kernel_certificate env w)

def nilFullTracedMatrixNumericIffSentence {m} (three : Bool) (env : Fin 3 → Fin m) (w n q r : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 3 w env).imp ((SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) (env 0)).imp ((StructuralListSyntax.nilCode w n).imp ((StructuralListSyntax.nilCode w q).imp (((HornUniversalTraceRules.tracedMatrix (YesMetaZFC.Automation.ObjectSyntaxTransform.nilArguments) w r env).iff (OriginalTransformRowSyntax.row 2 w (env 0) (env 1) (env 2) n q r)))))))).close

theorem source_nilFullTracedMatrixNumericIff {m} (three : Bool) (env : Fin 3 → Fin m) (w n q r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (nilFullTracedMatrixNumericIffSentence three env w n q r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralListSyntax.nilCode w q) (Context.add (StructuralListSyntax.nilCode w n) (Context.add (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) (env 0)) (Context.add (HornExprSyntax.environmentNat 3 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 3 w env) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) (env 0)) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (StructuralListSyntax.nilCode w n) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (StructuralListSyntax.nilCode w q) := .hyp (Or.inl rfl)
  exact OriginalArgumentsRuleMatrix.nil_matrix_iff hZ three w n q r env h0 h1 h2 h3 h4

theorem nilFullTracedMatrixNumericIff_kernel_certificate {m} (three : Bool) (env : Fin 3 → Fin m) (w n q r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (nilFullTracedMatrixNumericIffSentence three env w n q r)) := TheoryTransport.sentence (source_nilFullTracedMatrixNumericIff three env w n q r)

theorem native_nilFullTracedMatrixNumericIff {m} (three : Bool) (env : Fin 3 → Fin m) (w n q r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (nilFullTracedMatrixNumericIffSentence three env w n q r)) := ZFReplay.replay (nilFullTracedMatrixNumericIff_kernel_certificate three env w n q r)

def consFullTracedMatrixNumericIffSentence {m} (env : Fin 7 → Fin m) (w n q r : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 7 w env).imp ((StructuralListSyntax.consCode w (env 3) (env 4) n).imp ((StructuralListSyntax.consCode w (env 5) (env 6) q).imp (((HornUniversalTraceRules.tracedMatrix (YesMetaZFC.Automation.ObjectSyntaxTransform.consArguments) w r env).iff ((OriginalTransformRowSyntax.row 2 w (env 0) (env 1) (env 2) n q r).conj ((OriginalTransformRowSyntax.run 1 w (env 0) (env 1) (env 2) (env 3) (env 5)).conj (OriginalTransformRowSyntax.run 2 w (env 0) (env 1) (env 2) (env 4) (env 6)))))))))).close

theorem source_consFullTracedMatrixNumericIff {m} (env : Fin 7 → Fin m) (w n q r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (consFullTracedMatrixNumericIffSentence env w n q r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralListSyntax.consCode w (env 5) (env 6) q) (Context.add (StructuralListSyntax.consCode w (env 3) (env 4) n) (Context.add (HornExprSyntax.environmentNat 7 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 7 w env) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (StructuralListSyntax.consCode w (env 3) (env 4) n) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (StructuralListSyntax.consCode w (env 5) (env 6) q) := .hyp (Or.inl rfl)
  exact OriginalArgumentsRuleMatrix.cons_matrix_iff hZ w n q r env h0 h1 h2 h3

theorem consFullTracedMatrixNumericIff_kernel_certificate {m} (env : Fin 7 → Fin m) (w n q r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (consFullTracedMatrixNumericIffSentence env w n q r)) := TheoryTransport.sentence (source_consFullTracedMatrixNumericIff env w n q r)

theorem native_consFullTracedMatrixNumericIff {m} (env : Fin 7 → Fin m) (w n q r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (consFullTracedMatrixNumericIffSentence env w n q r)) := ZFReplay.replay (consFullTracedMatrixNumericIff_kernel_certificate env w n q r)

def consOriginalMatrixNumericIffSentence {m} (env : Fin 7 → Fin m) (w V n q r : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 7 w env).imp ((HornUniversalTraceSyntax.value w V).imp ((StructuralListSyntax.consCode w (env 3) (env 4) n).imp ((StructuralListSyntax.consCode w (env 5) (env 6) q).imp (((HornRuleSyntax.matrix (YesMetaZFC.Automation.ObjectSyntaxTransform.consArguments) w r V env).iff ((OriginalTransformRowSyntax.row 2 w (env 0) (env 1) (env 2) n q r).conj ((OriginalTransformRowSyntax.run 1 w (env 0) (env 1) (env 2) (env 3) (env 5)).conj (OriginalTransformRowSyntax.run 2 w (env 0) (env 1) (env 2) (env 4) (env 6))))))))))).close

theorem source_consOriginalMatrixNumericIff {m} (env : Fin 7 → Fin m) (w V n q r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (consOriginalMatrixNumericIffSentence env w V n q r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralListSyntax.consCode w (env 5) (env 6) q) (Context.add (StructuralListSyntax.consCode w (env 3) (env 4) n) (Context.add (HornUniversalTraceSyntax.value w V) (Context.add (HornExprSyntax.environmentNat 7 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 7 w env) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (HornUniversalTraceSyntax.value w V) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (StructuralListSyntax.consCode w (env 3) (env 4) n) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (StructuralListSyntax.consCode w (env 5) (env 6) q) := .hyp (Or.inl rfl)
  exact OriginalArgumentsRuleMatrix.original_cons_matrix_iff hZ w V n q r env h0 h1 h2 h3 h4

theorem consOriginalMatrixNumericIff_kernel_certificate {m} (env : Fin 7 → Fin m) (w V n q r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (consOriginalMatrixNumericIffSentence env w V n q r)) := TheoryTransport.sentence (source_consOriginalMatrixNumericIff env w V n q r)

theorem native_consOriginalMatrixNumericIff {m} (env : Fin 7 → Fin m) (w V n q r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (consOriginalMatrixNumericIffSentence env w V n q r)) := ZFReplay.replay (consOriginalMatrixNumericIff_kernel_certificate env w V n q r)

def nilAllCandidateRowMatrixIffSentence {m} (three : Bool) (env : Fin 3 → Fin m) (w n q r : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 3 w env).imp ((SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) (env 0)).imp ((OriginalTransformRowSyntax.row 2 w (env 0) (env 1) (env 2) n q r).imp (((HornUniversalTraceRules.tracedMatrix (YesMetaZFC.Automation.ObjectSyntaxTransform.nilArguments) w r env).iff ((StructuralListSyntax.nilCode w n).conj (StructuralListSyntax.nilCode w q)))))))).close

theorem source_nilAllCandidateRowMatrixIff {m} (three : Bool) (env : Fin 3 → Fin m) (w n q r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (nilAllCandidateRowMatrixIffSentence three env w n q r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (OriginalTransformRowSyntax.row 2 w (env 0) (env 1) (env 2) n q r) (Context.add (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) (env 0)) (Context.add (HornExprSyntax.environmentNat 3 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 3 w env) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) (env 0)) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (OriginalTransformRowSyntax.row 2 w (env 0) (env 1) (env 2) n q r) := .hyp (Or.inl rfl)
  exact OriginalArgumentsRowCases.nil_at_row hZ three w n q r env h0 h1 h2 h3

theorem nilAllCandidateRowMatrixIff_kernel_certificate {m} (three : Bool) (env : Fin 3 → Fin m) (w n q r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (nilAllCandidateRowMatrixIffSentence three env w n q r)) := TheoryTransport.sentence (source_nilAllCandidateRowMatrixIff three env w n q r)

theorem native_nilAllCandidateRowMatrixIff {m} (three : Bool) (env : Fin 3 → Fin m) (w n q r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (nilAllCandidateRowMatrixIffSentence three env w n q r)) := ZFReplay.replay (nilAllCandidateRowMatrixIff_kernel_certificate three env w n q r)

def consAllCandidateRowMatrixIffSentence {m} (env : Fin 7 → Fin m) (w n q r : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 7 w env).imp ((OriginalTransformRowSyntax.row 2 w (env 0) (env 1) (env 2) n q r).imp (((HornUniversalTraceRules.tracedMatrix (YesMetaZFC.Automation.ObjectSyntaxTransform.consArguments) w r env).iff (((StructuralListSyntax.consCode w (env 3) (env 4) n).conj (StructuralListSyntax.consCode w (env 5) (env 6) q)).conj ((OriginalTransformRowSyntax.run 1 w (env 0) (env 1) (env 2) (env 3) (env 5)).conj (OriginalTransformRowSyntax.run 2 w (env 0) (env 1) (env 2) (env 4) (env 6))))))))).close

theorem source_consAllCandidateRowMatrixIff {m} (env : Fin 7 → Fin m) (w n q r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (consAllCandidateRowMatrixIffSentence env w n q r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (OriginalTransformRowSyntax.row 2 w (env 0) (env 1) (env 2) n q r) (Context.add (HornExprSyntax.environmentNat 7 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 7 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (OriginalTransformRowSyntax.row 2 w (env 0) (env 1) (env 2) n q r) := .hyp (Or.inl rfl)
  exact OriginalArgumentsRowCases.cons_at_row hZ w n q r env h0 h1 h2

theorem consAllCandidateRowMatrixIff_kernel_certificate {m} (env : Fin 7 → Fin m) (w n q r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (consAllCandidateRowMatrixIffSentence env w n q r)) := TheoryTransport.sentence (source_consAllCandidateRowMatrixIff env w n q r)

theorem native_consAllCandidateRowMatrixIff {m} (env : Fin 7 → Fin m) (w n q r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (consAllCandidateRowMatrixIffSentence env w n q r)) := ZFReplay.replay (consAllCandidateRowMatrixIff_kernel_certificate env w n q r)

end PPAC.Migration.Internal.ObjectOriginalArgumentMatrix
