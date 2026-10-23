import PPAC.Migration.Internal.FormulaTransformProgramCode

/-! 独立固定十一分支公式程序的全部内部运行时正确性、拒绝性质及实际纤维的原YesMetaZFC核证书。 -/
namespace PPAC.Migration.Internal.ObjectFormulaTransformProgram
open Source SourceAlgebra SourceLogic OmegaSyntax

def membershipInstructionIffSentence {m} (w R S a b c d n q : Fin m) : Source.Sentence := ((omega w).imp (((FormulaTransformAtomSyntax.membership w R S a b c d n q).iff (SyntaxMixedFormulaAtomSyntax.membership w R S a b c d n q)))).close

theorem source_membershipInstructionIff {m} (w R S a b c d n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (membershipInstructionIffSentence w R S a b c d n q) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact FormulaTransformAtomCorrectness.membership_iff hZ w R S a b c d n q h0

theorem membershipInstructionIff_kernel_certificate {m} (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (membershipInstructionIffSentence w R S a b c d n q)) := TheoryTransport.sentence (source_membershipInstructionIff w R S a b c d n q)

theorem native_membershipInstructionIff {m} (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (membershipInstructionIffSentence w R S a b c d n q)) := ZFReplay.replay (membershipInstructionIff_kernel_certificate w R S a b c d n q)

def equalityInstructionIffSentence {m} (w R S a b c d n q : Fin m) : Source.Sentence := ((omega w).imp (((FormulaTransformAtomSyntax.equality w R S a b c d n q).iff (SyntaxMixedFormulaAtomSyntax.equality w R S a b c d n q)))).close

theorem source_equalityInstructionIff {m} (w R S a b c d n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (equalityInstructionIffSentence w R S a b c d n q) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact FormulaTransformAtomCorrectness.equality_iff hZ w R S a b c d n q h0

theorem equalityInstructionIff_kernel_certificate {m} (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (equalityInstructionIffSentence w R S a b c d n q)) := TheoryTransport.sentence (source_equalityInstructionIff w R S a b c d n q)

theorem native_equalityInstructionIff {m} (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (equalityInstructionIffSentence w R S a b c d n q)) := ZFReplay.replay (equalityInstructionIff_kernel_certificate w R S a b c d n q)

def compiledStepIffSentence {m} (w R S a b c d h n q : Fin m) : Source.Sentence := ((omega w).imp (((FormulaTransformProgramSyntax.step w R S a b c d h n q).iff (SyntaxMixedFormulaLocalSyntax.content w R S a b c d h n q)))).close

theorem source_compiledStepIff {m} (w R S a b c d h n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (compiledStepIffSentence w R S a b c d h n q) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact FormulaTransformStepCorrectness.step_iff hZ w R S a b c d h n q h0

theorem compiledStepIff_kernel_certificate {m} (w R S a b c d h n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (compiledStepIffSentence w R S a b c d h n q)) := TheoryTransport.sentence (source_compiledStepIff w R S a b c d h n q)

theorem native_compiledStepIff {m} (w R S a b c d h n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (compiledStepIffSentence w R S a b c d h n q)) := ZFReplay.replay (compiledStepIff_kernel_certificate w R S a b c d h n q)

def operatorRowIffSentence {m} (w n h p : Fin m) : Source.Sentence := ((omega w).imp (((FormulaTransformOperatorSyntax.row w n h p).iff (SyntaxMixedFormulaOperatorSyntax.row w n h p)))).close

theorem source_operatorRowIff {m} (w n h p : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (operatorRowIffSentence w n h p) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact FormulaTransformOperatorCorrectness.row_iff hZ w n h p h0

theorem operatorRowIff_kernel_certificate {m} (w n h p : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (operatorRowIffSentence w n h p)) := TheoryTransport.sentence (source_operatorRowIff w n h p)

theorem native_operatorRowIff {m} (w n h p : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (operatorRowIffSentence w n h p)) := ZFReplay.replay (operatorRowIff_kernel_certificate w n h p)

def operatorValueIffSentence {m} (w n h v : Fin m) : Source.Sentence := ((omega w).imp (((FormulaTransformOperatorSyntax.value w n h v).iff (SyntaxMixedFormulaOperatorSyntax.value w n h v)))).close

theorem source_operatorValueIff {m} (w n h v : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (operatorValueIffSentence w n h v) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact FormulaTransformOperatorCorrectness.value_iff hZ w n h v h0

theorem operatorValueIff_kernel_certificate {m} (w n h v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (operatorValueIffSentence w n h v)) := TheoryTransport.sentence (source_operatorValueIff w n h v)

theorem native_operatorValueIff {m} (w n h v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (operatorValueIffSentence w n h v)) := ZFReplay.replay (operatorValueIff_kernel_certificate w n h v)

def graphIffSentence {m} (w f d : Fin m) : Source.Sentence := ((omega w).imp (((FormulaTransformRecursionSyntax.graph w f d).iff (SyntaxMixedFormulaRecursionSyntax.graph w f d)))).close

theorem source_graphIff {m} (w f d : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (graphIffSentence w f d) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact FormulaTransformRecursionCorrectness.graph_iff hZ w f d h0

theorem graphIff_kernel_certificate {m} (w f d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (graphIffSentence w f d)) := TheoryTransport.sentence (source_graphIff w f d)

theorem native_graphIff {m} (w f d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (graphIffSentence w f d)) := ZFReplay.replay (graphIff_kernel_certificate w f d)

def evaluationIffSentence {m} (w n v : Fin m) : Source.Sentence := ((omega w).imp (((FormulaTransformEvaluationSyntax.evaluation w n v).iff (SyntaxMixedFormulaEvaluationSyntax.evaluation w n v)))).close

theorem source_evaluationIff {m} (w n v : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (evaluationIffSentence w n v) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact FormulaTransformRecursionCorrectness.evaluation_iff hZ w n v h0

theorem evaluationIff_kernel_certificate {m} (w n v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (evaluationIffSentence w n v)) := TheoryTransport.sentence (source_evaluationIff w n v)

theorem native_evaluationIff {m} (w n v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (evaluationIffSentence w n v)) := ZFReplay.replay (evaluationIff_kernel_certificate w n v)

def executionIffSentence {m} (w R S a b c d n q : Fin m) : Source.Sentence := ((omega w).imp (((FormulaTransformExecutionSyntax.executed w R S a b c d n q).iff (SyntaxMixedFormulaJudgmentSyntax.substituted w R S a b c d n q)))).close

theorem source_executionIff {m} (w R S a b c d n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (executionIffSentence w R S a b c d n q) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact FormulaTransformRecursionCorrectness.execution_iff hZ w R S a b c d n q h0

theorem executionIff_kernel_certificate {m} (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (executionIffSentence w R S a b c d n q)) := TheoryTransport.sentence (source_executionIff w R S a b c d n q)

theorem native_executionIff {m} (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (executionIffSentence w R S a b c d n q)) := ZFReplay.replay (executionIff_kernel_certificate w R S a b c d n q)

def actualRecursorsSentence {m} (w : Fin m) : Source.Sentence := ((omega w).imp ((FormulaTransformRecursionSyntax.recursors w))).close

theorem source_actualRecursors {m} (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (actualRecursorsSentence w) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact FormulaTransformRecursionCorrectness.actual_recursors hZ w h0

theorem actualRecursors_kernel_certificate {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (actualRecursorsSentence w)) := TheoryTransport.sentence (source_actualRecursors w)

theorem native_actualRecursors {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (actualRecursorsSentence w)) := ZFReplay.replay (actualRecursors_kernel_certificate w)

def graphExistsSentence {m} (w d : Fin m) : Source.Sentence := ((omega w).imp ((OrdinalSyntax.ordinal d).imp ((FormulaTransformRecursionSyntax.graphExists w d)))).close

theorem source_graphExists {m} (w d : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (graphExistsSentence w d) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (OrdinalSyntax.ordinal d) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (OrdinalSyntax.ordinal d) := .hyp (Or.inl rfl)
  exact FormulaTransformRecursionCorrectness.graph_exists hZ w d h0 h1

theorem graphExists_kernel_certificate {m} (w d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (graphExistsSentence w d)) := TheoryTransport.sentence (source_graphExists w d)

theorem native_graphExists {m} (w d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (graphExistsSentence w d)) := ZFReplay.replay (graphExists_kernel_certificate w d)

def evaluationExistsSentence {m} (w n : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem n w).imp ((FormulaTransformEvaluationSyntax.existsValue w n)))).close

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
  exact FormulaTransformRecursionCorrectness.evaluation_exists hZ w n h0 h1

theorem evaluationExists_kernel_certificate {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (evaluationExistsSentence w n)) := TheoryTransport.sentence (source_evaluationExists w n)

theorem native_evaluationExists {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (evaluationExistsSentence w n)) := ZFReplay.replay (evaluationExists_kernel_certificate w n)

def inputOfExecutionSentence {m} (w R S a b c d n q : Fin m) : Source.Sentence := ((omega w).imp ((FormulaTransformExecutionSyntax.executed w R S a b c d n q).imp ((FormulaTransformValueSyntax.inputGuard w R S a b c d n)))).close

theorem source_inputOfExecution {m} (w R S a b c d n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (inputOfExecutionSentence w R S a b c d n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (FormulaTransformExecutionSyntax.executed w R S a b c d n q) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (FormulaTransformExecutionSyntax.executed w R S a b c d n q) := .hyp (Or.inl rfl)
  exact FormulaTransformValue.input_of_execution hZ w R S a b c d n q h0 h1

theorem inputOfExecution_kernel_certificate {m} (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (inputOfExecutionSentence w R S a b c d n q)) := TheoryTransport.sentence (source_inputOfExecution w R S a b c d n q)

theorem native_inputOfExecution {m} (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (inputOfExecutionSentence w R S a b c d n q)) := ZFReplay.replay (inputOfExecution_kernel_certificate w R S a b c d n q)

def sourceTypeSentence {m} (w R S a b c d n q : Fin m) : Source.Sentence := ((omega w).imp ((FormulaTransformExecutionSyntax.executed w R S a b c d n q).imp ((FormulaCodeSyntax.formulaCode w n a b)))).close

theorem source_sourceType {m} (w R S a b c d n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (sourceTypeSentence w R S a b c d n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (FormulaTransformExecutionSyntax.executed w R S a b c d n q) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (FormulaTransformExecutionSyntax.executed w R S a b c d n q) := .hyp (Or.inl rfl)
  exact FormulaTransformValue.source_type hZ w R S a b c d n q h0 h1

theorem sourceType_kernel_certificate {m} (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (sourceTypeSentence w R S a b c d n q)) := TheoryTransport.sentence (source_sourceType w R S a b c d n q)

theorem native_sourceType {m} (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (sourceTypeSentence w R S a b c d n q)) := ZFReplay.replay (sourceType_kernel_certificate w R S a b c d n q)

def targetTypeSentence {m} (w R S a b c d n q : Fin m) : Source.Sentence := ((omega w).imp ((FormulaTransformExecutionSyntax.executed w R S a b c d n q).imp ((FormulaCodeSyntax.formulaCode w q c d)))).close

theorem source_targetType {m} (w R S a b c d n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (targetTypeSentence w R S a b c d n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (FormulaTransformExecutionSyntax.executed w R S a b c d n q) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (FormulaTransformExecutionSyntax.executed w R S a b c d n q) := .hyp (Or.inl rfl)
  exact FormulaTransformValue.target_type hZ w R S a b c d n q h0 h1

theorem targetType_kernel_certificate {m} (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (targetTypeSentence w R S a b c d n q)) := TheoryTransport.sentence (source_targetType w R S a b c d n q)

theorem native_targetType {m} (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (targetTypeSentence w R S a b c d n q)) := ZFReplay.replay (targetType_kernel_certificate w R S a b c d n q)

def outputNaturalSentence {m} (w R S a b c d n q : Fin m) : Source.Sentence := ((omega w).imp ((FormulaTransformExecutionSyntax.executed w R S a b c d n q).imp ((Formula.mem q w)))).close

theorem source_outputNatural {m} (w R S a b c d n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (outputNaturalSentence w R S a b c d n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (FormulaTransformExecutionSyntax.executed w R S a b c d n q) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (FormulaTransformExecutionSyntax.executed w R S a b c d n q) := .hyp (Or.inl rfl)
  exact FormulaTransformValue.output_natural hZ w R S a b c d n q h0 h1

theorem outputNatural_kernel_certificate {m} (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (outputNaturalSentence w R S a b c d n q)) := TheoryTransport.sentence (source_outputNatural w R S a b c d n q)

theorem native_outputNatural {m} (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (outputNaturalSentence w R S a b c d n q)) := ZFReplay.replay (outputNatural_kernel_certificate w R S a b c d n q)

def uniqueOutputSentence {m} (w R S a b c d n q : Fin m) : Source.Sentence := ((omega w).imp ((FormulaTransformExecutionSyntax.executed w R S a b c d n q).imp ((FormulaTransformValueSyntax.uniqueOutput w R S a b c d n q)))).close

theorem source_uniqueOutput {m} (w R S a b c d n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (uniqueOutputSentence w R S a b c d n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (FormulaTransformExecutionSyntax.executed w R S a b c d n q) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (FormulaTransformExecutionSyntax.executed w R S a b c d n q) := .hyp (Or.inl rfl)
  exact FormulaTransformValue.unique_output hZ w R S a b c d n q h0 h1

theorem uniqueOutput_kernel_certificate {m} (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (uniqueOutputSentence w R S a b c d n q)) := TheoryTransport.sentence (source_uniqueOutput w R S a b c d n q)

theorem native_uniqueOutput {m} (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (uniqueOutputSentence w R S a b c d n q)) := ZFReplay.replay (uniqueOutput_kernel_certificate w R S a b c d n q)

def atCandidateSentence {m} (w R S a b c d n q : Fin m) : Source.Sentence := ((omega w).imp ((FormulaTransformExecutionSyntax.executed w R S a b c d n q).imp ((FormulaTransformValueSyntax.value w R S a b c d n q)))).close

theorem source_atCandidate {m} (w R S a b c d n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (atCandidateSentence w R S a b c d n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (FormulaTransformExecutionSyntax.executed w R S a b c d n q) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (FormulaTransformExecutionSyntax.executed w R S a b c d n q) := .hyp (Or.inl rfl)
  exact FormulaTransformValue.at_candidate hZ w R S a b c d n q h0 h1

theorem atCandidate_kernel_certificate {m} (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (atCandidateSentence w R S a b c d n q)) := TheoryTransport.sentence (source_atCandidate w R S a b c d n q)

theorem native_atCandidate {m} (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (atCandidateSentence w R S a b c d n q)) := ZFReplay.replay (atCandidate_kernel_certificate w R S a b c d n q)

def rejectEnvironmentSentence {m} (w R S a b c d n q : Fin m) : Source.Sentence := ((omega w).imp (((SyntaxMixedImageCodeSyntax.termLists w a b c d R S).neg).imp (((FormulaTransformExecutionSyntax.executed w R S a b c d n q).neg)))).close

theorem source_rejectEnvironment {m} (w R S a b c d n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (rejectEnvironmentSentence w R S a b c d n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add ((SyntaxMixedImageCodeSyntax.termLists w a b c d R S).neg) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ ((SyntaxMixedImageCodeSyntax.termLists w a b c d R S).neg) := .hyp (Or.inl rfl)
  exact FormulaTransformValue.reject_environment hZ w R S a b c d n q h0 h1

theorem rejectEnvironment_kernel_certificate {m} (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (rejectEnvironmentSentence w R S a b c d n q)) := TheoryTransport.sentence (source_rejectEnvironment w R S a b c d n q)

theorem native_rejectEnvironment {m} (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (rejectEnvironmentSentence w R S a b c d n q)) := ZFReplay.replay (rejectEnvironment_kernel_certificate w R S a b c d n q)

def rejectSourceSentence {m} (w R S a b c d n q : Fin m) : Source.Sentence := ((omega w).imp (((FormulaCodeSyntax.formulaCode w n a b).neg).imp (((FormulaTransformExecutionSyntax.executed w R S a b c d n q).neg)))).close

theorem source_rejectSource {m} (w R S a b c d n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (rejectSourceSentence w R S a b c d n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add ((FormulaCodeSyntax.formulaCode w n a b).neg) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ ((FormulaCodeSyntax.formulaCode w n a b).neg) := .hyp (Or.inl rfl)
  exact FormulaTransformValue.reject_source hZ w R S a b c d n q h0 h1

theorem rejectSource_kernel_certificate {m} (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (rejectSourceSentence w R S a b c d n q)) := TheoryTransport.sentence (source_rejectSource w R S a b c d n q)

theorem native_rejectSource {m} (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (rejectSourceSentence w R S a b c d n q)) := ZFReplay.replay (rejectSource_kernel_certificate w R S a b c d n q)

def rejectInputSentence {m} (w R S a b c d n q : Fin m) : Source.Sentence := ((omega w).imp (((FormulaTransformValueSyntax.inputGuard w R S a b c d n).neg).imp (((FormulaTransformExecutionSyntax.executed w R S a b c d n q).neg)))).close

theorem source_rejectInput {m} (w R S a b c d n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (rejectInputSentence w R S a b c d n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add ((FormulaTransformValueSyntax.inputGuard w R S a b c d n).neg) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ ((FormulaTransformValueSyntax.inputGuard w R S a b c d n).neg) := .hyp (Or.inl rfl)
  exact FormulaTransformValue.reject_input hZ w R S a b c d n q h0 h1

theorem rejectInput_kernel_certificate {m} (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (rejectInputSentence w R S a b c d n q)) := TheoryTransport.sentence (source_rejectInput w R S a b c d n q)

theorem native_rejectInput {m} (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (rejectInputSentence w R S a b c d n q)) := ZFReplay.replay (rejectInput_kernel_certificate w R S a b c d n q)

def rejectTargetSentence {m} (w R S a b c d n q : Fin m) : Source.Sentence := ((omega w).imp (((FormulaCodeSyntax.formulaCode w q c d).neg).imp (((FormulaTransformExecutionSyntax.executed w R S a b c d n q).neg)))).close

theorem source_rejectTarget {m} (w R S a b c d n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (rejectTargetSentence w R S a b c d n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add ((FormulaCodeSyntax.formulaCode w q c d).neg) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ ((FormulaCodeSyntax.formulaCode w q c d).neg) := .hyp (Or.inl rfl)
  exact FormulaTransformValue.reject_target hZ w R S a b c d n q h0 h1

theorem rejectTarget_kernel_certificate {m} (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (rejectTargetSentence w R S a b c d n q)) := TheoryTransport.sentence (source_rejectTarget w R S a b c d n q)

theorem native_rejectTarget {m} (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (rejectTargetSentence w R S a b c d n q)) := ZFReplay.replay (rejectTarget_kernel_certificate w R S a b c d n q)

def rejectOutputNaturalSentence {m} (w R S a b c d n q : Fin m) : Source.Sentence := ((omega w).imp (((Formula.mem q w).neg).imp (((FormulaTransformExecutionSyntax.executed w R S a b c d n q).neg)))).close

theorem source_rejectOutputNatural {m} (w R S a b c d n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (rejectOutputNaturalSentence w R S a b c d n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add ((Formula.mem q w).neg) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ ((Formula.mem q w).neg) := .hyp (Or.inl rfl)
  exact FormulaTransformValue.reject_output_natural hZ w R S a b c d n q h0 h1

theorem rejectOutputNatural_kernel_certificate {m} (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (rejectOutputNaturalSentence w R S a b c d n q)) := TheoryTransport.sentence (source_rejectOutputNatural w R S a b c d n q)

theorem native_rejectOutputNatural {m} (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (rejectOutputNaturalSentence w R S a b c d n q)) := ZFReplay.replay (rejectOutputNatural_kernel_certificate w R S a b c d n q)

def uniqueSentence {m} (w R S a b c d n q v : Fin m) : Source.Sentence := ((omega w).imp ((FormulaTransformExecutionSyntax.executed w R S a b c d n q).imp ((FormulaTransformExecutionSyntax.executed w R S a b c d n v).imp ((.equal q v))))).close

theorem source_unique {m} (w R S a b c d n q v : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (uniqueSentence w R S a b c d n q v) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (FormulaTransformExecutionSyntax.executed w R S a b c d n v) (Context.add (FormulaTransformExecutionSyntax.executed w R S a b c d n q) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (FormulaTransformExecutionSyntax.executed w R S a b c d n q) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (FormulaTransformExecutionSyntax.executed w R S a b c d n v) := .hyp (Or.inl rfl)
  exact FormulaTransformValue.unique hZ w R S a b c d n q v h0 h1 h2

theorem unique_kernel_certificate {m} (w R S a b c d n q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (uniqueSentence w R S a b c d n q v)) := TheoryTransport.sentence (source_unique w R S a b c d n q v)

theorem native_unique {m} (w R S a b c d n q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (uniqueSentence w R S a b c d n q v)) := ZFReplay.replay (unique_kernel_certificate w R S a b c d n q v)

def actualFiberSentence {m} (w R S a b c d n : Fin m) : Source.Sentence := ((omega w).imp ((FormulaTransformValueSyntax.inputGuard w R S a b c d n).imp ((FormulaTransformValueSyntax.fiber w R S a b c d n)))).close

theorem source_actualFiber {m} (w R S a b c d n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (actualFiberSentence w R S a b c d n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (FormulaTransformValueSyntax.inputGuard w R S a b c d n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (FormulaTransformValueSyntax.inputGuard w R S a b c d n) := .hyp (Or.inl rfl)
  exact FormulaTransformValue.actual_fiber hZ w R S a b c d n h0 h1

theorem actualFiber_kernel_certificate {m} (w R S a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (actualFiberSentence w R S a b c d n)) := TheoryTransport.sentence (source_actualFiber w R S a b c d n)

theorem native_actualFiber {m} (w R S a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (actualFiberSentence w R S a b c d n)) := ZFReplay.replay (actualFiber_kernel_certificate w R S a b c d n)

def fiberIffInputSentence {m} (w R S a b c d n : Fin m) : Source.Sentence := ((omega w).imp (((FormulaTransformValueSyntax.fiber w R S a b c d n).iff (FormulaTransformValueSyntax.inputGuard w R S a b c d n)))).close

theorem source_fiberIffInput {m} (w R S a b c d n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (fiberIffInputSentence w R S a b c d n) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact FormulaTransformValue.fiber_iff_input hZ w R S a b c d n h0

theorem fiberIffInput_kernel_certificate {m} (w R S a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (fiberIffInputSentence w R S a b c d n)) := TheoryTransport.sentence (source_fiberIffInput w R S a b c d n)

theorem native_fiberIffInput {m} (w R S a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (fiberIffInputSentence w R S a b c d n)) := ZFReplay.replay (fiberIffInput_kernel_certificate w R S a b c d n)

def encodedExecutionIffSentence {m} (w P R S a b c d n q : Fin m) : Source.Sentence := ((omega w).imp ((FormulaTransformProgramCodeSyntax.code w P).imp ((FormulaTransformProgramCodeSyntax.correctAt w P R S a b c d n q)))).close

theorem source_encodedExecutionIff {m} (w P R S a b c d n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (encodedExecutionIffSentence w P R S a b c d n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (FormulaTransformProgramCodeSyntax.code w P) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (FormulaTransformProgramCodeSyntax.code w P) := .hyp (Or.inl rfl)
  exact FormulaTransformProgramCode.encoded_execution_iff hZ w P R S a b c d n q h0 h1

theorem encodedExecutionIff_kernel_certificate {m} (w P R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (encodedExecutionIffSentence w P R S a b c d n q)) := TheoryTransport.sentence (source_encodedExecutionIff w P R S a b c d n q)

theorem native_encodedExecutionIff {m} (w P R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (encodedExecutionIffSentence w P R S a b c d n q)) := ZFReplay.replay (encodedExecutionIff_kernel_certificate w P R S a b c d n q)

def uniformCorrectnessSentence {m} (w P : Fin m) : Source.Sentence := ((omega w).imp ((FormulaTransformProgramCodeSyntax.code w P).imp ((FormulaTransformProgramCodeSyntax.uniform w P)))).close

theorem source_uniformCorrectness {m} (w P : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (uniformCorrectnessSentence w P) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (FormulaTransformProgramCodeSyntax.code w P) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (FormulaTransformProgramCodeSyntax.code w P) := .hyp (Or.inl rfl)
  exact FormulaTransformProgramCode.uniform_correctness hZ w P h0 h1

theorem uniformCorrectness_kernel_certificate {m} (w P : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (uniformCorrectnessSentence w P)) := TheoryTransport.sentence (source_uniformCorrectness w P)

theorem native_uniformCorrectness {m} (w P : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (uniformCorrectnessSentence w P)) := ZFReplay.replay (uniformCorrectness_kernel_certificate w P)

def uniqueCodeSentence {m} (w P : Fin m) : Source.Sentence := ((omega w).imp ((FormulaTransformProgramCodeSyntax.code w P).imp ((FormulaTransformProgramCodeSyntax.uniqueCode w P)))).close

theorem source_uniqueCode {m} (w P : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (uniqueCodeSentence w P) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (FormulaTransformProgramCodeSyntax.code w P) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (FormulaTransformProgramCodeSyntax.code w P) := .hyp (Or.inl rfl)
  exact FormulaTransformProgramCode.unique_code hZ w P h0 h1

theorem uniqueCode_kernel_certificate {m} (w P : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (uniqueCodeSentence w P)) := TheoryTransport.sentence (source_uniqueCode w P)

theorem native_uniqueCode {m} (w P : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (uniqueCodeSentence w P)) := ZFReplay.replay (uniqueCode_kernel_certificate w P)

def atCodeSentence {m} (w P : Fin m) : Source.Sentence := ((omega w).imp ((FormulaTransformProgramCodeSyntax.code w P).imp ((FormulaTransformProgramCodeSyntax.programValue w P)))).close

theorem source_atCode {m} (w P : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (atCodeSentence w P) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (FormulaTransformProgramCodeSyntax.code w P) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (FormulaTransformProgramCodeSyntax.code w P) := .hyp (Or.inl rfl)
  exact FormulaTransformProgramCode.at_code hZ w P h0 h1

theorem atCode_kernel_certificate {m} (w P : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (atCodeSentence w P)) := TheoryTransport.sentence (source_atCode w P)

theorem native_atCode {m} (w P : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (atCodeSentence w P)) := ZFReplay.replay (atCode_kernel_certificate w P)

def existsCorrectProgramSentence {m} (w : Fin m) : Source.Sentence := ((omega w).imp ((FormulaTransformProgramCodeSyntax.existsProgram w))).close

theorem source_existsCorrectProgram {m} (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (existsCorrectProgramSentence w) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact FormulaTransformProgramCode.exists_correct_program hZ w h0

theorem existsCorrectProgram_kernel_certificate {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (existsCorrectProgramSentence w)) := TheoryTransport.sentence (source_existsCorrectProgram w)

theorem native_existsCorrectProgram {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (existsCorrectProgramSentence w)) := ZFReplay.replay (existsCorrectProgram_kernel_certificate w)

end PPAC.Migration.Internal.ObjectFormulaTransformProgram
