import PPAC.Migration.Internal.ProofForallNode

/-! 实际mode1首槽公式及原全称化完整节点的原核闭句。 -/
namespace PPAC.Migration.Internal.ObjectForallNode
open Source SourceAlgebra SourceLogic OmegaSyntax

def modeOneActualTopFormulaAtCodesIffSentence {m} (w mode z P a b A B R S n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 1 mode).imp ((OriginalTermTraceSyntax.metadata w z P).imp ((empty z).imp ((SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S).imp ((FormulaCodeSyntax.formulaCode w n a B).imp (((OriginalTransformRowSyntax.run 3 w mode z P n q).iff (SyntaxTopFormulaSyntax.abstracted w a b A B n q))))))))).close

theorem source_modeOneActualTopFormulaAtCodesIff {m} (w mode z P a b A B R S n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeOneActualTopFormulaAtCodesIffSentence w mode z P a b A B R S n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (FormulaCodeSyntax.formulaCode w n a B) (Context.add (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S) (Context.add (empty z) (Context.add (OriginalTermTraceSyntax.metadata w z P) (Context.add (SyntaxNumeralSyntax.numeral 1 mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 1 mode) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (OriginalTermTraceSyntax.metadata w z P) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (empty z) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (FormulaCodeSyntax.formulaCode w n a B) := .hyp (Or.inl rfl)
  exact AbstractTopFormulaOperation.at_codes_iff hZ w mode z P a b A B R S n q h0 h1 h2 h3 h4 h5

theorem modeOneActualTopFormulaAtCodesIff_kernel_certificate {m} (w mode z P a b A B R S n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeOneActualTopFormulaAtCodesIffSentence w mode z P a b A B R S n q)) := TheoryTransport.sentence (source_modeOneActualTopFormulaAtCodesIff w mode z P a b A B R S n q)

theorem native_modeOneActualTopFormulaAtCodesIff {m} (w mode z P a b A B R S n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeOneActualTopFormulaAtCodesIffSentence w mode z P a b A B R S n q)) := ZFReplay.replay (modeOneActualTopFormulaAtCodesIff_kernel_certificate w mode z P a b A B R S n q)

def modeOneActualTopFormulaIffSentence {m} (w mode z P a b A B n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 1 mode).imp ((OriginalTermTraceSyntax.metadata w z P).imp ((empty z).imp ((SyntaxTopEnvironmentSyntax.abstractInput w a b A B).imp ((FormulaCodeSyntax.formulaCode w n a B).imp (((OriginalTransformRowSyntax.run 3 w mode z P n q).iff (SyntaxTopFormulaSyntax.abstracted w a b A B n q))))))))).close

theorem source_modeOneActualTopFormulaIff {m} (w mode z P a b A B n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeOneActualTopFormulaIffSentence w mode z P a b A B n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (FormulaCodeSyntax.formulaCode w n a B) (Context.add (SyntaxTopEnvironmentSyntax.abstractInput w a b A B) (Context.add (empty z) (Context.add (OriginalTermTraceSyntax.metadata w z P) (Context.add (SyntaxNumeralSyntax.numeral 1 mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 1 mode) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (OriginalTermTraceSyntax.metadata w z P) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (empty z) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (SyntaxTopEnvironmentSyntax.abstractInput w a b A B) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (FormulaCodeSyntax.formulaCode w n a B) := .hyp (Or.inl rfl)
  exact AbstractTopFormulaOperation.run_iff hZ w mode z P a b A B n q h0 h1 h2 h3 h4 h5

theorem modeOneActualTopFormulaIff_kernel_certificate {m} (w mode z P a b A B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeOneActualTopFormulaIffSentence w mode z P a b A B n q)) := TheoryTransport.sentence (source_modeOneActualTopFormulaIff w mode z P a b A B n q)

theorem native_modeOneActualTopFormulaIff {m} (w mode z P a b A B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeOneActualTopFormulaIffSentence w mode z P a b A B n q)) := ZFReplay.replay (modeOneActualTopFormulaIff_kernel_certificate w mode z P a b A B n q)

def modeOneActualTopGuardedFormulaIffSentence {m} (w mode z P a b A B n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 1 mode).imp ((OriginalTermTraceSyntax.metadata w z P).imp ((empty z).imp ((SyntaxTopEnvironmentSyntax.abstractInput w a b A B).imp ((((FormulaCodeSyntax.formulaCode w n a B).conj (OriginalTransformRowSyntax.run 3 w mode z P n q)).iff (SyntaxTopFormulaSyntax.abstracted w a b A B n q)))))))).close

theorem source_modeOneActualTopGuardedFormulaIff {m} (w mode z P a b A B n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeOneActualTopGuardedFormulaIffSentence w mode z P a b A B n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTopEnvironmentSyntax.abstractInput w a b A B) (Context.add (empty z) (Context.add (OriginalTermTraceSyntax.metadata w z P) (Context.add (SyntaxNumeralSyntax.numeral 1 mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 1 mode) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (OriginalTermTraceSyntax.metadata w z P) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (empty z) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (SyntaxTopEnvironmentSyntax.abstractInput w a b A B) := .hyp (Or.inl rfl)
  exact AbstractTopFormulaOperation.guarded_iff hZ w mode z P a b A B n q h0 h1 h2 h3 h4

theorem modeOneActualTopGuardedFormulaIff_kernel_certificate {m} (w mode z P a b A B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeOneActualTopGuardedFormulaIffSentence w mode z P a b A B n q)) := TheoryTransport.sentence (source_modeOneActualTopGuardedFormulaIff w mode z P a b A B n q)

theorem native_modeOneActualTopGuardedFormulaIff {m} (w mode z P a b A B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeOneActualTopGuardedFormulaIffSentence w mode z P a b A B n q)) := ZFReplay.replay (modeOneActualTopGuardedFormulaIff_kernel_certificate w mode z P a b A B n q)

def modeOneActualTopFormulaSourceSentence {m} (w a b A B n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxTopFormulaSyntax.abstracted w a b A B n q).imp ((FormulaCodeSyntax.formulaCode w n a B)))).close

theorem source_modeOneActualTopFormulaSource {m} (w a b A B n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeOneActualTopFormulaSourceSentence w a b A B n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTopFormulaSyntax.abstracted w a b A B n q) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxTopFormulaSyntax.abstracted w a b A B n q) := .hyp (Or.inl rfl)
  exact AbstractTopFormulaOperation.source_type hZ w a b A B n q h0 h1

theorem modeOneActualTopFormulaSource_kernel_certificate {m} (w a b A B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeOneActualTopFormulaSourceSentence w a b A B n q)) := TheoryTransport.sentence (source_modeOneActualTopFormulaSource w a b A B n q)

theorem native_modeOneActualTopFormulaSource {m} (w a b A B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeOneActualTopFormulaSourceSentence w a b A B n q)) := ZFReplay.replay (modeOneActualTopFormulaSource_kernel_certificate w a b A B n q)

def forallFormulaQueryIffSentence {m} (env : Fin 4 → Fin m) (w z B : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 4 w env).imp ((empty z).imp ((successor B (env 0)).imp (((PureSyntaxExprQuery.query ProofForallSyntax.formulaQuery w env).iff (FormulaCodeSyntax.formulaCode w (env 3) z B))))))).close

theorem source_forallFormulaQueryIff {m} (env : Fin 4 → Fin m) (w z B : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (forallFormulaQueryIffSentence env w z B) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor B (env 0)) (Context.add (empty z) (Context.add (HornExprSyntax.environmentNat 4 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 4 w env) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (empty z) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (successor B (env 0)) := .hyp (Or.inl rfl)
  exact ProofForallQueries.formula_iff hZ w z B env h0 h1 h2 h3

theorem forallFormulaQueryIff_kernel_certificate {m} (env : Fin 4 → Fin m) (w z B : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (forallFormulaQueryIffSentence env w z B)) := TheoryTransport.sentence (source_forallFormulaQueryIff env w z B)

theorem native_forallFormulaQueryIff {m} (env : Fin 4 → Fin m) (w z B : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (forallFormulaQueryIffSentence env w z B)) := ZFReplay.replay (forallFormulaQueryIff_kernel_certificate env w z B)

def forallFreeProjectionQueryIffSentence {m} (env : Fin 4 → Fin m) (w z B : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 4 w env).imp ((empty z).imp ((successor B (env 0)).imp (((ProjectionExprQuery.query ProofForallSyntax.freeQuery w env).iff (RawCodeFieldSyntax.field w (env 2) z B))))))).close

theorem source_forallFreeProjectionQueryIff {m} (env : Fin 4 → Fin m) (w z B : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (forallFreeProjectionQueryIffSentence env w z B) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor B (env 0)) (Context.add (empty z) (Context.add (HornExprSyntax.environmentNat 4 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 4 w env) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (empty z) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (successor B (env 0)) := .hyp (Or.inl rfl)
  exact ProofForallQueries.free_iff_at_successor hZ w z B env h0 h1 h2 h3

theorem forallFreeProjectionQueryIff_kernel_certificate {m} (env : Fin 4 → Fin m) (w z B : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (forallFreeProjectionQueryIffSentence env w z B)) := TheoryTransport.sentence (source_forallFreeProjectionQueryIff env w z B)

theorem native_forallFreeProjectionQueryIff {m} (env : Fin 4 → Fin m) (w z B : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (forallFreeProjectionQueryIffSentence env w z B)) := ZFReplay.replay (forallFreeProjectionQueryIff_kernel_certificate env w z B)

def forallPredecessorFormulaQueryIffSentence {m} (env : Fin 4 → Fin m) (w : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 4 w env).imp (((ProjectionExprQuery.query ProofForallSyntax.predecessorFormulaQuery w env).iff (ProofSubstitutionProjectionSyntax.atOne w (env 2) (env 3)))))).close

theorem source_forallPredecessorFormulaQueryIff {m} (env : Fin 4 → Fin m) (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (forallPredecessorFormulaQueryIffSentence env w) := by
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
  exact ProofForallQueries.predecessorFormula_iff hZ w env h0 h1

theorem forallPredecessorFormulaQueryIff_kernel_certificate {m} (env : Fin 4 → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (forallPredecessorFormulaQueryIffSentence env w)) := TheoryTransport.sentence (source_forallPredecessorFormulaQueryIff env w)

theorem native_forallPredecessorFormulaQueryIff {m} (env : Fin 4 → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (forallPredecessorFormulaQueryIffSentence env w)) := ZFReplay.replay (forallPredecessorFormulaQueryIff_kernel_certificate env w)

def forallModeOneTransformNumericIffSentence {m} (env : Fin 4 → Fin m) (w z A : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 4 w env).imp ((empty z).imp ((SyntaxNumeralSyntax.numeral 1 A).imp (((OriginalTransformExprQuery.query ProofForallSyntax.transformQuery w env).iff (OriginalTransformRowSyntax.run 3 w A z z (env 3) (env 1)))))))).close

theorem source_forallModeOneTransformNumericIff {m} (env : Fin 4 → Fin m) (w z A : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (forallModeOneTransformNumericIffSentence env w z A) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNumeralSyntax.numeral 1 A) (Context.add (empty z) (Context.add (HornExprSyntax.environmentNat 4 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 4 w env) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (empty z) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxNumeralSyntax.numeral 1 A) := .hyp (Or.inl rfl)
  exact ProofForallQueries.transform_at_zero hZ w z A env h0 h1 h2 h3

theorem forallModeOneTransformNumericIff_kernel_certificate {m} (env : Fin 4 → Fin m) (w z A : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (forallModeOneTransformNumericIffSentence env w z A)) := TheoryTransport.sentence (source_forallModeOneTransformNumericIff env w z A)

theorem native_forallModeOneTransformNumericIff {m} (env : Fin 4 → Fin m) (w z A : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (forallModeOneTransformNumericIffSentence env w z A)) := ZFReplay.replay (forallModeOneTransformNumericIff_kernel_certificate env w z A)

def forallActualTopTransformIffSentence {m} (env : Fin 4 → Fin m) (w z A B : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 4 w env).imp ((empty z).imp ((successor A z).imp ((successor B (env 0)).imp ((PureSyntaxExprQuery.query ProofForallSyntax.formulaQuery w env).imp (((OriginalTransformExprQuery.query ProofForallSyntax.transformQuery w env).iff (SyntaxTopFormulaSyntax.abstracted w z (env 0) A B (env 3) (env 1)))))))))).close

theorem source_forallActualTopTransformIff {m} (env : Fin 4 → Fin m) (w z A B : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (forallActualTopTransformIffSentence env w z A B) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PureSyntaxExprQuery.query ProofForallSyntax.formulaQuery w env) (Context.add (successor B (env 0)) (Context.add (successor A z) (Context.add (empty z) (Context.add (HornExprSyntax.environmentNat 4 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 4 w env) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (empty z) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (successor A z) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (successor B (env 0)) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (PureSyntaxExprQuery.query ProofForallSyntax.formulaQuery w env) := .hyp (Or.inl rfl)
  exact ProofForallQueries.guarded_transform_iff hZ w z A B env h0 h1 h2 h3 h4 h5

theorem forallActualTopTransformIff_kernel_certificate {m} (env : Fin 4 → Fin m) (w z A B : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (forallActualTopTransformIffSentence env w z A B)) := TheoryTransport.sentence (source_forallActualTopTransformIff env w z A B)

theorem native_forallActualTopTransformIff {m} (env : Fin 4 → Fin m) (w z A B : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (forallActualTopTransformIffSentence env w z A B)) := ZFReplay.replay (forallActualTopTransformIff_kernel_certificate env w z A B)

def forallAllFourQueriesIffSentence {m} (env : Fin 4 → Fin m) (w z : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 4 w env).imp ((empty z).imp (((ProofForallSyntax.bundle w env).iff (ProofForallSyntax.specification w z env)))))).close

theorem source_forallAllFourQueriesIff {m} (env : Fin 4 → Fin m) (w z : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (forallAllFourQueriesIffSentence env w z) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (empty z) (Context.add (HornExprSyntax.environmentNat 4 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 4 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (empty z) := .hyp (Or.inl rfl)
  exact ProofForallAllQueries.bundle_iff hZ w z env h0 h1 h2

theorem forallAllFourQueriesIff_kernel_certificate {m} (env : Fin 4 → Fin m) (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (forallAllFourQueriesIffSentence env w z)) := TheoryTransport.sentence (source_forallAllFourQueriesIff env w z)

theorem native_forallAllFourQueriesIff {m} (env : Fin 4 → Fin m) (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (forallAllFourQueriesIffSentence env w z)) := ZFReplay.replay (forallAllFourQueriesIff_kernel_certificate env w z)

def forallAllFourAssignmentBoundsSentence {m} (env : Fin 4 → Fin m) (w row : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 4 w env).imp ((HornExprSyntax.graph YesMetaZFC.Automation.ObjectProofNode.forallShape.head w env row).imp ((ProjectionExprQuery.query ProofForallSyntax.predecessorFormulaQuery w env).imp ((HornExprBounds.environmentBound 4 row env)))))).close

theorem source_forallAllFourAssignmentBounds {m} (env : Fin 4 → Fin m) (w row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (forallAllFourAssignmentBoundsSentence env w row) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ProjectionExprQuery.query ProofForallSyntax.predecessorFormulaQuery w env) (Context.add (HornExprSyntax.graph YesMetaZFC.Automation.ObjectProofNode.forallShape.head w env row) (Context.add (HornExprSyntax.environmentNat 4 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 4 w env) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (HornExprSyntax.graph YesMetaZFC.Automation.ObjectProofNode.forallShape.head w env row) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (ProjectionExprQuery.query ProofForallSyntax.predecessorFormulaQuery w env) := .hyp (Or.inl rfl)
  exact ProofForallBounds.environment_bound hZ w row env h0 h1 h2 h3

theorem forallAllFourAssignmentBounds_kernel_certificate {m} (env : Fin 4 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (forallAllFourAssignmentBoundsSentence env w row)) := TheoryTransport.sentence (source_forallAllFourAssignmentBounds env w row)

theorem native_forallAllFourAssignmentBounds {m} (env : Fin 4 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (forallAllFourAssignmentBoundsSentence env w row)) := ZFReplay.replay (forallAllFourAssignmentBounds_kernel_certificate env w row)

def forallActualNestedHeadIffSentence {m} (env : Fin 4 → Fin m) (w row : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 4 w env).imp (((HornExprSyntax.graph YesMetaZFC.Automation.ObjectProofNode.forallShape.head w env row).iff (ProofForallHead.normalized w row env))))).close

theorem source_forallActualNestedHeadIff {m} (env : Fin 4 → Fin m) (w row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (forallActualNestedHeadIffSentence env w row) := by
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
  exact ProofForallHead.head_iff hZ w row env h0 h1

theorem forallActualNestedHeadIff_kernel_certificate {m} (env : Fin 4 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (forallActualNestedHeadIffSentence env w row)) := TheoryTransport.sentence (source_forallActualNestedHeadIff env w row)

theorem native_forallActualNestedHeadIff {m} (env : Fin 4 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (forallActualNestedHeadIffSentence env w row)) := ZFReplay.replay (forallActualNestedHeadIff_kernel_certificate env w row)

def forallFullPureRelationalNodeIffSentence {m} (w z row : Fin m) : Source.Sentence := ((omega w).imp ((empty z).imp (((ProofForallNodeSyntax.node w row).iff (ProofForallNodeSyntax.specification w z row))))).close

theorem source_forallFullPureRelationalNodeIff {m} (w z row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (forallFullPureRelationalNodeIffSentence w z row) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (empty z) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (empty z) := .hyp (Or.inl rfl)
  exact ProofForallNode.node_iff hZ w z row h0 h1

theorem forallFullPureRelationalNodeIff_kernel_certificate {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (forallFullPureRelationalNodeIffSentence w z row)) := TheoryTransport.sentence (source_forallFullPureRelationalNodeIff w z row)

theorem native_forallFullPureRelationalNodeIff {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (forallFullPureRelationalNodeIffSentence w z row)) := ZFReplay.replay (forallFullPureRelationalNodeIff_kernel_certificate w z row)

def forallFullNormalizedNodeIffSentence {m} (w z row : Fin m) : Source.Sentence := ((omega w).imp ((empty z).imp (((ProofForallNodeSyntax.node w row).iff (ProofForallNode.normalized w z row))))).close

theorem source_forallFullNormalizedNodeIff {m} (w z row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (forallFullNormalizedNodeIffSentence w z row) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (empty z) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (empty z) := .hyp (Or.inl rfl)
  exact ProofForallNode.normalized_node_iff hZ w z row h0 h1

theorem forallFullNormalizedNodeIff_kernel_certificate {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (forallFullNormalizedNodeIffSentence w z row)) := TheoryTransport.sentence (source_forallFullNormalizedNodeIff w z row)

theorem native_forallFullNormalizedNodeIff {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (forallFullNormalizedNodeIffSentence w z row)) := ZFReplay.replay (forallFullNormalizedNodeIff_kernel_certificate w z row)

end PPAC.Migration.Internal.ObjectForallNode
