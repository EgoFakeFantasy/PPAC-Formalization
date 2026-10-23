import PPAC.Migration.Internal.LookupTableOutcome

/-! 独立固定两分支查找程序的全部内部运行时正确性、拒绝性质及实际纤维的原YesMetaZFC核证书。 -/
namespace PPAC.Migration.Internal.ObjectLookupTableProgram
open Source SourceAlgebra SourceLogic OmegaSyntax

def operatorActualFiberSentence {m} (w n h : Fin m) : Source.Sentence := ((LookupTableOperatorSyntax.fiber w n h)).close

theorem source_operatorActualFiber {m} (w n h : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (operatorActualFiberSentence w n h) := by
  apply close_derives
  let Δ : Context m := Source.SetLanguage.ZF.at m
  have hZ : ZFContext.Evidence Δ := by
    exact ZFContext.source_ZF m
  exact LookupTableOperatorExistence.actual_fiber hZ w n h

theorem operatorActualFiber_kernel_certificate {m} (w n h : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (operatorActualFiberSentence w n h)) := TheoryTransport.sentence (source_operatorActualFiber w n h)

theorem native_operatorActualFiber {m} (w n h : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (operatorActualFiberSentence w n h)) := ZFReplay.replay (operatorActualFiber_kernel_certificate w n h)

def actualCarrierRecursorsSentence {m} (w : Fin m) : Source.Sentence := ((LookupTableRecursionSyntax.actualRecursors w)).close

theorem source_actualCarrierRecursors {m} (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (actualCarrierRecursorsSentence w) := by
  apply close_derives
  let Δ : Context m := Source.SetLanguage.ZF.at m
  have hZ : ZFContext.Evidence Δ := by
    exact ZFContext.source_ZF m
  exact LookupTableRecursors.actual_carrier_recursors hZ w

theorem actualCarrierRecursors_kernel_certificate {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (actualCarrierRecursorsSentence w)) := TheoryTransport.sentence (source_actualCarrierRecursors w)

theorem native_actualCarrierRecursors {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (actualCarrierRecursorsSentence w)) := ZFReplay.replay (actualCarrierRecursors_kernel_certificate w)

def allOrdinalRecursorsSentence {m} (w : Fin m) : Source.Sentence := ((LookupTableRecursionSyntax.recursors w)).close

theorem source_allOrdinalRecursors {m} (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (allOrdinalRecursorsSentence w) := by
  apply close_derives
  let Δ : Context m := Source.SetLanguage.ZF.at m
  have hZ : ZFContext.Evidence Δ := by
    exact ZFContext.source_ZF m
  exact LookupTableRecursors.all_unique hZ w

theorem allOrdinalRecursors_kernel_certificate {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (allOrdinalRecursorsSentence w)) := TheoryTransport.sentence (source_allOrdinalRecursors w)

theorem native_allOrdinalRecursors {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (allOrdinalRecursorsSentence w)) := ZFReplay.replay (allOrdinalRecursors_kernel_certificate w)

def actualGraphSentence {m} (w d : Fin m) : Source.Sentence := ((OrdinalSyntax.ordinal d).imp ((LookupTableRecursionSyntax.graphExists w d))).close

theorem source_actualGraph {m} (w d : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (actualGraphSentence w d) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (OrdinalSyntax.ordinal d) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (OrdinalSyntax.ordinal d) := .hyp (Or.inl rfl)
  exact LookupTableRecursors.exists_graph hZ w d h0

theorem actualGraph_kernel_certificate {m} (w d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (actualGraphSentence w d)) := TheoryTransport.sentence (source_actualGraph w d)

theorem native_actualGraph {m} (w d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (actualGraphSentence w d)) := ZFReplay.replay (actualGraph_kernel_certificate w d)

def evaluationAtNaturalSentence {m} (w n : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem n w).imp ((LookupTableEvaluationSyntax.existsValue w n)))).close

theorem source_evaluationAtNatural {m} (w n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (evaluationAtNaturalSentence w n) := by
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
  exact LookupTableEvaluationExistence.at_natural hZ w n h0 h1

theorem evaluationAtNatural_kernel_certificate {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (evaluationAtNaturalSentence w n)) := TheoryTransport.sentence (source_evaluationAtNatural w n)

theorem native_evaluationAtNatural {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (evaluationAtNaturalSentence w n)) := ZFReplay.replay (evaluationAtNatural_kernel_certificate w n)

def evaluationUniqueFiberSentence {m} (w n : Fin m) : Source.Sentence := ((OrdinalSyntax.ordinal n).imp ((LookupTableEvaluationSyntax.fiber w n))).close

theorem source_evaluationUniqueFiber {m} (w n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (evaluationUniqueFiberSentence w n) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (OrdinalSyntax.ordinal n) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (OrdinalSyntax.ordinal n) := .hyp (Or.inl rfl)
  exact LookupTableEvaluationUnique.exists_unique hZ w n h0

theorem evaluationUniqueFiber_kernel_certificate {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (evaluationUniqueFiberSentence w n)) := TheoryTransport.sentence (source_evaluationUniqueFiber w n)

theorem native_evaluationUniqueFiber {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (evaluationUniqueFiberSentence w n)) := ZFReplay.replay (evaluationUniqueFiber_kernel_certificate w n)

def stateMembershipIffSentence {m} (w n h v i y : Fin m) : Source.Sentence := ((omega w).imp ((LookupTableOperatorSyntax.value w n h v).imp (((LookupTableProgramSyntax.contains w v i y).iff ((LookupTableProgramSyntax.legal w i y).conj (LookupTableProgramSyntax.run w h n i y)))))).close

theorem source_stateMembershipIff {m} (w n h v i y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (stateMembershipIffSentence w n h v i y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (LookupTableOperatorSyntax.value w n h v) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (LookupTableOperatorSyntax.value w n h v) := .hyp (Or.inl rfl)
  exact LookupTableOperatorMembership.contains_iff hZ w n h v i y h0 h1

theorem stateMembershipIff_kernel_certificate {m} (w n h v i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (stateMembershipIffSentence w n h v i y)) := TheoryTransport.sentence (source_stateMembershipIff w n h v i y)

theorem native_stateMembershipIff {m} (w n h v i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (stateMembershipIffSentence w n h v i y)) := ZFReplay.replay (stateMembershipIff_kernel_certificate w n h v i y)

def recursiveCriterionSentence {m} (w n i y : Fin m) : Source.Sentence := ((omega w).imp (((LookupTableExecutionSyntax.executed w n i y).iff (LookupTableRecursiveSyntax.criterion w n i y)))).close

theorem source_recursiveCriterion {m} (w n i y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (recursiveCriterionSentence w n i y) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact LookupTableRecursive.recursive_iff hZ w n i y h0

theorem recursiveCriterion_kernel_certificate {m} (w n i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (recursiveCriterionSentence w n i y)) := TheoryTransport.sentence (source_recursiveCriterion w n i y)

theorem native_recursiveCriterion {m} (w n i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (recursiveCriterionSentence w n i y)) := ZFReplay.replay (recursiveCriterion_kernel_certificate w n i y)

def allInternalExecutionIffSentence {m} (w n i y : Fin m) : Source.Sentence := ((omega w).imp (((LookupTableExecutionSyntax.executed w n i y).iff (StrictLookupSyntax.checked w n i y)))).close

theorem source_allInternalExecutionIff {m} (w n i y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (allInternalExecutionIffSentence w n i y) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact LookupTableCorrectness.execution_iff_checked hZ w n i y h0

theorem allInternalExecutionIff_kernel_certificate {m} (w n i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (allInternalExecutionIffSentence w n i y)) := TheoryTransport.sentence (source_allInternalExecutionIff w n i y)

theorem native_allInternalExecutionIff {m} (w n i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (allInternalExecutionIffSentence w n i y)) := ZFReplay.replay (allInternalExecutionIff_kernel_certificate w n i y)

def naturalExecutionIffSentence {m} (w n i y : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem n w).imp ((Formula.mem i w).imp (((LookupTableExecutionSyntax.executed w n i y).iff (StrictLookupSyntax.returned w n i y)))))).close

theorem source_naturalExecutionIff {m} (w n i y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (naturalExecutionIffSentence w n i y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem i w) (Context.add (Formula.mem n w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (Formula.mem n w) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (Formula.mem i w) := .hyp (Or.inl rfl)
  exact LookupTableCorrectnessInduction.execution_iff_at_natural hZ w n i y h0 h1 h2

theorem naturalExecutionIff_kernel_certificate {m} (w n i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (naturalExecutionIffSentence w n i y)) := TheoryTransport.sentence (source_naturalExecutionIff w n i y)

theorem native_naturalExecutionIff {m} (w n i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (naturalExecutionIffSentence w n i y)) := ZFReplay.replay (naturalExecutionIff_kernel_certificate w n i y)

def encodedExecutionIffSentence {m} (w P n i y : Fin m) : Source.Sentence := ((omega w).imp ((LookupTableProgramCodeSyntax.code w P).imp ((LookupTableProgramCodeSyntax.correctAt w P n i y)))).close

theorem source_encodedExecutionIff {m} (w P n i y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (encodedExecutionIffSentence w P n i y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (LookupTableProgramCodeSyntax.code w P) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (LookupTableProgramCodeSyntax.code w P) := .hyp (Or.inl rfl)
  exact LookupTableProgramCode.encoded_execution_iff hZ w P n i y h0 h1

theorem encodedExecutionIff_kernel_certificate {m} (w P n i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (encodedExecutionIffSentence w P n i y)) := TheoryTransport.sentence (source_encodedExecutionIff w P n i y)

theorem native_encodedExecutionIff {m} (w P n i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (encodedExecutionIffSentence w P n i y)) := ZFReplay.replay (encodedExecutionIff_kernel_certificate w P n i y)

def uniformCorrectnessSentence {m} (w P : Fin m) : Source.Sentence := ((omega w).imp ((LookupTableProgramCodeSyntax.code w P).imp ((LookupTableProgramCodeSyntax.uniform w P)))).close

theorem source_uniformCorrectness {m} (w P : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (uniformCorrectnessSentence w P) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (LookupTableProgramCodeSyntax.code w P) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (LookupTableProgramCodeSyntax.code w P) := .hyp (Or.inl rfl)
  exact LookupTableProgramCode.uniform_correctness hZ w P h0 h1

theorem uniformCorrectness_kernel_certificate {m} (w P : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (uniformCorrectnessSentence w P)) := TheoryTransport.sentence (source_uniformCorrectness w P)

theorem native_uniformCorrectness {m} (w P : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (uniformCorrectnessSentence w P)) := ZFReplay.replay (uniformCorrectness_kernel_certificate w P)

def uniqueProgramCodeSentence {m} (w P : Fin m) : Source.Sentence := ((omega w).imp ((LookupTableProgramCodeSyntax.code w P).imp ((LookupTableProgramCodeSyntax.uniqueCode w P)))).close

theorem source_uniqueProgramCode {m} (w P : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (uniqueProgramCodeSentence w P) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (LookupTableProgramCodeSyntax.code w P) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (LookupTableProgramCodeSyntax.code w P) := .hyp (Or.inl rfl)
  exact LookupTableProgramCode.unique_code hZ w P h0 h1

theorem uniqueProgramCode_kernel_certificate {m} (w P : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (uniqueProgramCodeSentence w P)) := TheoryTransport.sentence (source_uniqueProgramCode w P)

theorem native_uniqueProgramCode {m} (w P : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (uniqueProgramCodeSentence w P)) := ZFReplay.replay (uniqueProgramCode_kernel_certificate w P)

def existsCorrectProgramSentence {m} (w : Fin m) : Source.Sentence := ((omega w).imp ((LookupTableProgramCodeSyntax.existsProgram w))).close

theorem source_existsCorrectProgram {m} (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (existsCorrectProgramSentence w) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact LookupTableProgramCode.exists_correct_program hZ w h0

theorem existsCorrectProgram_kernel_certificate {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (existsCorrectProgramSentence w)) := TheoryTransport.sentence (source_existsCorrectProgram w)

theorem native_existsCorrectProgram {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (existsCorrectProgramSentence w)) := ZFReplay.replay (existsCorrectProgram_kernel_certificate w)

def hasOutputIffSentence {m} (w n i : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem n w).imp ((Formula.mem i w).imp (((LookupTableOutcomeSyntax.hasOutput w n i).iff (StrictLookupSyntax.hasOutput w n i)))))).close

theorem source_hasOutputIff {m} (w n i : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (hasOutputIffSentence w n i) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem i w) (Context.add (Formula.mem n w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (Formula.mem n w) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (Formula.mem i w) := .hyp (Or.inl rfl)
  exact LookupTableOutcome.has_output_iff hZ w n i h0 h1 h2

theorem hasOutputIff_kernel_certificate {m} (w n i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (hasOutputIffSentence w n i)) := TheoryTransport.sentence (source_hasOutputIff w n i)

theorem native_hasOutputIff {m} (w n i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (hasOutputIffSentence w n i)) := ZFReplay.replay (hasOutputIff_kernel_certificate w n i)

def noOutputIffSentence {m} (w n i : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem n w).imp ((Formula.mem i w).imp (((LookupTableOutcomeSyntax.noOutput w n i).iff (StrictLookupSyntax.rejected w n i)))))).close

theorem source_noOutputIff {m} (w n i : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (noOutputIffSentence w n i) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem i w) (Context.add (Formula.mem n w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (Formula.mem n w) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (Formula.mem i w) := .hyp (Or.inl rfl)
  exact LookupTableOutcome.no_output_iff hZ w n i h0 h1 h2

theorem noOutputIff_kernel_certificate {m} (w n i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (noOutputIffSentence w n i)) := TheoryTransport.sentence (source_noOutputIff w n i)

theorem native_noOutputIff {m} (w n i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (noOutputIffSentence w n i)) := ZFReplay.replay (noOutputIff_kernel_certificate w n i)

def outcomeExhaustiveSentence {m} (w n i : Fin m) : Source.Sentence := (((LookupTableOutcomeSyntax.hasOutput w n i).disj (LookupTableOutcomeSyntax.noOutput w n i))).close

theorem source_outcomeExhaustive {m} (w n i : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (outcomeExhaustiveSentence w n i) := by
  apply close_derives
  let Δ : Context m := Source.SetLanguage.ZF.at m
  exact LookupTableOutcome.exhaustive w n i

theorem outcomeExhaustive_kernel_certificate {m} (w n i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (outcomeExhaustiveSentence w n i)) := TheoryTransport.sentence (source_outcomeExhaustive w n i)

theorem native_outcomeExhaustive {m} (w n i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (outcomeExhaustiveSentence w n i)) := ZFReplay.replay (outcomeExhaustive_kernel_certificate w n i)

def outcomeIncompatibleSentence {m} (w n i : Fin m) : Source.Sentence := ((((LookupTableOutcomeSyntax.hasOutput w n i).conj (LookupTableOutcomeSyntax.noOutput w n i)).neg)).close

theorem source_outcomeIncompatible {m} (w n i : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (outcomeIncompatibleSentence w n i) := by
  apply close_derives
  let Δ : Context m := Source.SetLanguage.ZF.at m
  exact LookupTableOutcome.incompatible w n i

theorem outcomeIncompatible_kernel_certificate {m} (w n i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (outcomeIncompatibleSentence w n i)) := TheoryTransport.sentence (source_outcomeIncompatible w n i)

theorem native_outcomeIncompatible {m} (w n i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (outcomeIncompatibleSentence w n i)) := ZFReplay.replay (outcomeIncompatible_kernel_certificate w n i)

def uniqueOutputSentence {m} (w n i y : Fin m) : Source.Sentence := ((omega w).imp ((LookupTableExecutionSyntax.executed w n i y).imp ((LookupTableOutcomeSyntax.uniqueOutput w n i y)))).close

theorem source_uniqueOutput {m} (w n i y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (uniqueOutputSentence w n i y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (LookupTableExecutionSyntax.executed w n i y) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (LookupTableExecutionSyntax.executed w n i y) := .hyp (Or.inl rfl)
  exact LookupTableOutcome.unique_output hZ w n i y h0 h1

theorem uniqueOutput_kernel_certificate {m} (w n i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (uniqueOutputSentence w n i y)) := TheoryTransport.sentence (source_uniqueOutput w n i y)

theorem native_uniqueOutput {m} (w n i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (uniqueOutputSentence w n i y)) := ZFReplay.replay (uniqueOutput_kernel_certificate w n i y)

end PPAC.Migration.Internal.ObjectLookupTableProgram
