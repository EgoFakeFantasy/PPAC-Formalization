import PPAC.Migration.Internal.FormulaTransformRootStep

/-! 实际十一分支程序的类型守卫、根执行方程及其原推导核闭句。 -/
namespace PPAC.Migration.Internal.ObjectFormulaTransformRootStep
open Source SourceAlgebra SourceLogic OmegaSyntax
open YesMetaZFC.Automation.ObjectHorn (Rule)

def recursiveCasesTargetTypeSentence {m} (w R S a b c d n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMixedFormulaOutputSyntax.input w R S a b c d n).imp ((SyntaxMixedFormulaRecursiveSyntax.cases w R S a b c d n q).imp ((FormulaCodeSyntax.formulaCode w q c d))))).close

theorem source_recursiveCasesTargetType {m} (w R S a b c d n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (recursiveCasesTargetTypeSentence w R S a b c d n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMixedFormulaRecursiveSyntax.cases w R S a b c d n q) (Context.add (SyntaxMixedFormulaOutputSyntax.input w R S a b c d n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxMixedFormulaOutputSyntax.input w R S a b c d n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxMixedFormulaRecursiveSyntax.cases w R S a b c d n q) := .hyp (Or.inl rfl)
  exact FormulaTransformRootStep.recursive_target_type hZ w R S a b c d n q h0 h1 h2

theorem recursiveCasesTargetType_kernel_certificate {m} (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (recursiveCasesTargetTypeSentence w R S a b c d n q)) := TheoryTransport.sentence (source_recursiveCasesTargetType w R S a b c d n q)

theorem native_recursiveCasesTargetType {m} (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (recursiveCasesTargetTypeSentence w R S a b c d n q)) := ZFReplay.replay (recursiveCasesTargetType_kernel_certificate w R S a b c d n q)

def actualProgramTargetTypeSentence {m} (w R S a b c d h n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMixedFormulaOutputSyntax.input w R S a b c d n).imp ((FormulaTransformRecursionSyntax.graph w h n).imp ((FormulaTransformProgramSyntax.run FormulaTransformProgramSyntax.formulaProgram w R S a b c d h n q).imp ((FormulaCodeSyntax.formulaCode w q c d)))))).close

theorem source_actualProgramTargetType {m} (w R S a b c d h n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (actualProgramTargetTypeSentence w R S a b c d h n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (FormulaTransformProgramSyntax.run FormulaTransformProgramSyntax.formulaProgram w R S a b c d h n q) (Context.add (FormulaTransformRecursionSyntax.graph w h n) (Context.add (SyntaxMixedFormulaOutputSyntax.input w R S a b c d n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxMixedFormulaOutputSyntax.input w R S a b c d n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (FormulaTransformRecursionSyntax.graph w h n) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (FormulaTransformProgramSyntax.run FormulaTransformProgramSyntax.formulaProgram w R S a b c d h n q) := .hyp (Or.inl rfl)
  exact FormulaTransformRootStep.program_target_type hZ w R S a b c d h n q h0 h1 h2 h3

theorem actualProgramTargetType_kernel_certificate {m} (w R S a b c d h n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (actualProgramTargetTypeSentence w R S a b c d h n q)) := TheoryTransport.sentence (source_actualProgramTargetType w R S a b c d h n q)

theorem native_actualProgramTargetType {m} (w R S a b c d h n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (actualProgramTargetTypeSentence w R S a b c d h n q)) := ZFReplay.replay (actualProgramTargetType_kernel_certificate w R S a b c d h n q)

def actualRootGuardedStepIffSentence {m} (w R S a b c d h n q : Fin m) : Source.Sentence := ((omega w).imp ((OrdinalSyntax.ordinal n).imp ((FormulaTransformRecursionSyntax.graph w h n).imp (((FormulaTransformExecutionSyntax.executed w R S a b c d n q).iff ((Formula.mem n w).conj ((SyntaxMixedFormulaStateSyntax.legal w R S a b c d q).conj (FormulaTransformProgramSyntax.step w R S a b c d h n q)))))))).close

theorem source_actualRootGuardedStepIff {m} (w R S a b c d h n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (actualRootGuardedStepIffSentence w R S a b c d h n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (FormulaTransformRecursionSyntax.graph w h n) (Context.add (OrdinalSyntax.ordinal n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (OrdinalSyntax.ordinal n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (FormulaTransformRecursionSyntax.graph w h n) := .hyp (Or.inl rfl)
  exact FormulaTransformRootStep.execution_iff_guarded_step hZ w R S a b c d h n q h0 h1 h2

theorem actualRootGuardedStepIff_kernel_certificate {m} (w R S a b c d h n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (actualRootGuardedStepIffSentence w R S a b c d h n q)) := TheoryTransport.sentence (source_actualRootGuardedStepIff w R S a b c d h n q)

theorem native_actualRootGuardedStepIff {m} (w R S a b c d h n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (actualRootGuardedStepIffSentence w R S a b c d h n q)) := ZFReplay.replay (actualRootGuardedStepIff_kernel_certificate w R S a b c d h n q)

def actualRootStepIffSentence {m} (w R S a b c d h n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMixedFormulaOutputSyntax.input w R S a b c d n).imp ((FormulaTransformRecursionSyntax.graph w h n).imp (((FormulaTransformExecutionSyntax.executed w R S a b c d n q).iff (FormulaTransformProgramSyntax.step w R S a b c d h n q)))))).close

theorem source_actualRootStepIff {m} (w R S a b c d h n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (actualRootStepIffSentence w R S a b c d h n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (FormulaTransformRecursionSyntax.graph w h n) (Context.add (SyntaxMixedFormulaOutputSyntax.input w R S a b c d n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxMixedFormulaOutputSyntax.input w R S a b c d n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (FormulaTransformRecursionSyntax.graph w h n) := .hyp (Or.inl rfl)
  exact FormulaTransformRootStep.execution_iff_step hZ w R S a b c d h n q h0 h1 h2

theorem actualRootStepIff_kernel_certificate {m} (w R S a b c d h n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (actualRootStepIffSentence w R S a b c d h n q)) := TheoryTransport.sentence (source_actualRootStepIff w R S a b c d h n q)

theorem native_actualRootStepIff {m} (w R S a b c d h n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (actualRootStepIffSentence w R S a b c d h n q)) := ZFReplay.replay (actualRootStepIff_kernel_certificate w R S a b c d h n q)

def actualRootWholeProgramIffSentence {m} (w R S a b c d h n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMixedFormulaOutputSyntax.input w R S a b c d n).imp ((FormulaTransformRecursionSyntax.graph w h n).imp (((FormulaTransformExecutionSyntax.executed w R S a b c d n q).iff (FormulaTransformProgramSyntax.run FormulaTransformProgramSyntax.formulaProgram w R S a b c d h n q)))))).close

theorem source_actualRootWholeProgramIff {m} (w R S a b c d h n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (actualRootWholeProgramIffSentence w R S a b c d h n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (FormulaTransformRecursionSyntax.graph w h n) (Context.add (SyntaxMixedFormulaOutputSyntax.input w R S a b c d n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxMixedFormulaOutputSyntax.input w R S a b c d n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (FormulaTransformRecursionSyntax.graph w h n) := .hyp (Or.inl rfl)
  exact FormulaTransformRootStep.execution_iff_program hZ w R S a b c d h n q h0 h1 h2

theorem actualRootWholeProgramIff_kernel_certificate {m} (w R S a b c d h n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (actualRootWholeProgramIffSentence w R S a b c d h n q)) := TheoryTransport.sentence (source_actualRootWholeProgramIff w R S a b c d h n q)

theorem native_actualRootWholeProgramIff {m} (w R S a b c d h n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (actualRootWholeProgramIffSentence w R S a b c d h n q)) := ZFReplay.replay (actualRootWholeProgramIff_kernel_certificate w R S a b c d h n q)

end PPAC.Migration.Internal.ObjectFormulaTransformRootStep
