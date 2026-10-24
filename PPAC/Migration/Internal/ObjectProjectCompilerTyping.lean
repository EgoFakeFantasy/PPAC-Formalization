import PPAC.Migration.Internal.ProjectCompilerTyping

/-! All internal actual Project compiler output types by original Foundation; source completeness and scalar uniqueness remain unproved in the original nativeZF kernel; complete schema tests and Con remain unproved. -/
namespace PPAC.Migration.Internal.ObjectProjectCompilerTyping
open Source SourceAlgebra SourceLogic OmegaSyntax

def compilerChildTypingFromMemberIHSentence {m} (w n z : Fin m) : Source.Sentence := ((empty z).imp ((ProjectCompilerTypingSyntax.allIH w n).imp ((ProjectCompilerTypingSyntax.goodQueries ProjectCompilerRecursiveSyntax.codeMatrix (ProjectCompilerRecursiveSyntax.parameters w) w n z)))).close

theorem source_compilerChildTypingFromMemberIH {m} (w n z : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (compilerChildTypingFromMemberIHSentence w n z) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ProjectCompilerTypingSyntax.allIH w n) (Context.add (empty z) (Source.SetLanguage.ZF.at m))
  have h0 : Derives Δ (empty z) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (ProjectCompilerTypingSyntax.allIH w n) := .hyp (Or.inl rfl)
  exact ProjectCompilerTypingQueries.from_induction w n z h0 h1

theorem compilerChildTypingFromMemberIH_kernel_certificate {m} (w n z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (compilerChildTypingFromMemberIHSentence w n z)) := TheoryTransport.sentence (source_compilerChildTypingFromMemberIH w n z)

theorem native_compilerChildTypingFromMemberIH {m} (w n z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (compilerChildTypingFromMemberIHSentence w n z)) := ZFReplay.replay (compilerChildTypingFromMemberIH_kernel_certificate w n z)

def compilerTwelveCasesTargetTypedSentence {m} (w b z n q : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem b w).imp ((empty z).imp ((ProjectCompilerTypingSyntax.goodQueries ProjectCompilerRecursiveSyntax.codeMatrix (ProjectCompilerRecursiveSyntax.parameters w) w n z).imp ((ProjectCompilerRecursiveSyntax.casesAt w b z n q).imp ((FormulaCodeSyntax.formulaCode w q b z))))))).close

theorem source_compilerTwelveCasesTargetTyped {m} (w b z n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (compilerTwelveCasesTargetTypedSentence w b z n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ProjectCompilerRecursiveSyntax.casesAt w b z n q) (Context.add (ProjectCompilerTypingSyntax.goodQueries ProjectCompilerRecursiveSyntax.codeMatrix (ProjectCompilerRecursiveSyntax.parameters w) w n z) (Context.add (empty z) (Context.add (Formula.mem b w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (Formula.mem b w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (empty z) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (ProjectCompilerTypingSyntax.goodQueries ProjectCompilerRecursiveSyntax.codeMatrix (ProjectCompilerRecursiveSyntax.parameters w) w n z) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (ProjectCompilerRecursiveSyntax.casesAt w b z n q) := .hyp (Or.inl rfl)
  exact ProjectCompilerAllTyping.all_cases hZ ProjectCompilerRecursiveSyntax.codeMatrix (ProjectCompilerRecursiveSyntax.parameters w) w b z n q h0 h1 h2 h3 h4

theorem compilerTwelveCasesTargetTyped_kernel_certificate {m} (w b z n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (compilerTwelveCasesTargetTypedSentence w b z n q)) := TheoryTransport.sentence (source_compilerTwelveCasesTargetTyped w b z n q)

theorem native_compilerTwelveCasesTargetTyped {m} (w b z n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (compilerTwelveCasesTargetTypedSentence w b z n q)) := ZFReplay.replay (compilerTwelveCasesTargetTyped_kernel_certificate w b z n q)

def compilerOutputTypedFromMemberIHSentence {m} (w n b q z : Fin m) : Source.Sentence := ((omega w).imp ((empty z).imp ((ProjectCompilerTypingSyntax.allIH w n).imp ((ProjectCompilerCodeSyntax.compiled w n b q).imp ((FormulaCodeSyntax.formulaCode w q b z)))))).close

theorem source_compilerOutputTypedFromMemberIH {m} (w n b q z : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (compilerOutputTypedFromMemberIHSentence w n b q z) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ProjectCompilerCodeSyntax.compiled w n b q) (Context.add (ProjectCompilerTypingSyntax.allIH w n) (Context.add (empty z) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (empty z) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (ProjectCompilerTypingSyntax.allIH w n) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (ProjectCompilerCodeSyntax.compiled w n b q) := .hyp (Or.inl rfl)
  exact ProjectCompilerTypingStep.output_from_induction hZ w n b q z h0 h1 h2 h3

theorem compilerOutputTypedFromMemberIH_kernel_certificate {m} (w n b q z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (compilerOutputTypedFromMemberIHSentence w n b q z)) := TheoryTransport.sentence (source_compilerOutputTypedFromMemberIH w n b q z)

theorem native_compilerOutputTypedFromMemberIH {m} (w n b q z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (compilerOutputTypedFromMemberIHSentence w n b q z)) := ZFReplay.replay (compilerOutputTypedFromMemberIH_kernel_certificate w n b q z)

def compilerTypingPropertyStepSentence {m} (w n : Fin m) : Source.Sentence := ((omega w).imp ((ProjectCompilerTypingSyntax.allIH w n).imp ((ProjectCompilerTypingSyntax.correct w n)))).close

theorem source_compilerTypingPropertyStep {m} (w n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (compilerTypingPropertyStepSentence w n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ProjectCompilerTypingSyntax.allIH w n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (ProjectCompilerTypingSyntax.allIH w n) := .hyp (Or.inl rfl)
  exact ProjectCompilerTypingStep.from_induction hZ w n h0 h1

theorem compilerTypingPropertyStep_kernel_certificate {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (compilerTypingPropertyStepSentence w n)) := TheoryTransport.sentence (source_compilerTypingPropertyStep w n)

theorem native_compilerTypingPropertyStep {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (compilerTypingPropertyStepSentence w n)) := ZFReplay.replay (compilerTypingPropertyStep_kernel_certificate w n)

def compilerTypingProgressiveSentence {m} (w : Fin m) : Source.Sentence := ((omega w).imp ((SetInductionSyntax.progressive ProjectCompilerTyping.inductionMatrix (fun _ : Fin 1 => w)))).close

theorem source_compilerTypingProgressive {m} (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (compilerTypingProgressiveSentence w) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact ProjectCompilerTyping.progressive hZ w h0

theorem compilerTypingProgressive_kernel_certificate {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (compilerTypingProgressiveSentence w)) := TheoryTransport.sentence (source_compilerTypingProgressive w)

theorem native_compilerTypingProgressive {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (compilerTypingProgressiveSentence w)) := ZFReplay.replay (compilerTypingProgressive_kernel_certificate w)

def compilerAllInternalOutputsTargetTypedSentence {m} (w : Fin m) : Source.Sentence := ((omega w).imp ((.all (ProjectCompilerTypingSyntax.correct w.castSucc (Fin.last m))))).close

theorem source_compilerAllInternalOutputsTargetTyped {m} (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (compilerAllInternalOutputsTargetTypedSentence w) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact ProjectCompilerTyping.all_correct hZ w h0

theorem compilerAllInternalOutputsTargetTyped_kernel_certificate {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (compilerAllInternalOutputsTargetTypedSentence w)) := TheoryTransport.sentence (source_compilerAllInternalOutputsTargetTyped w)

theorem native_compilerAllInternalOutputsTargetTyped {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (compilerAllInternalOutputsTargetTypedSentence w)) := ZFReplay.replay (compilerAllInternalOutputsTargetTyped_kernel_certificate w)

def compilerInputTypingPropertySentence {m} (w n : Fin m) : Source.Sentence := ((omega w).imp ((ProjectCompilerTypingSyntax.correct w n))).close

theorem source_compilerInputTypingProperty {m} (w n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (compilerInputTypingPropertySentence w n) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact ProjectCompilerTyping.at_input hZ w n h0

theorem compilerInputTypingProperty_kernel_certificate {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (compilerInputTypingPropertySentence w n)) := TheoryTransport.sentence (source_compilerInputTypingProperty w n)

theorem native_compilerInputTypingProperty {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (compilerInputTypingPropertySentence w n)) := ZFReplay.replay (compilerInputTypingProperty_kernel_certificate w n)

def compilerActualOutputTargetTypedSentence {m} (w n b q z : Fin m) : Source.Sentence := ((omega w).imp ((empty z).imp ((ProjectCompilerCodeSyntax.compiled w n b q).imp ((FormulaCodeSyntax.formulaCode w q b z))))).close

theorem source_compilerActualOutputTargetTyped {m} (w n b q z : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (compilerActualOutputTargetTypedSentence w n b q z) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ProjectCompilerCodeSyntax.compiled w n b q) (Context.add (empty z) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (empty z) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (ProjectCompilerCodeSyntax.compiled w n b q) := .hyp (Or.inl rfl)
  exact ProjectCompilerTyping.output_type hZ w n b q z h0 h1 h2

theorem compilerActualOutputTargetTyped_kernel_certificate {m} (w n b q z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (compilerActualOutputTargetTypedSentence w n b q z)) := TheoryTransport.sentence (source_compilerActualOutputTargetTyped w n b q z)

theorem native_compilerActualOutputTargetTyped {m} (w n b q z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (compilerActualOutputTargetTypedSentence w n b q z)) := ZFReplay.replay (compilerActualOutputTargetTyped_kernel_certificate w n b q z)

def compilerUntypedOutputRejectedSentence {m} (w n b q z : Fin m) : Source.Sentence := ((omega w).imp ((empty z).imp (((FormulaCodeSyntax.formulaCode w q b z).neg).imp (((ProjectCompilerCodeSyntax.compiled w n b q).neg))))).close

theorem source_compilerUntypedOutputRejected {m} (w n b q z : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (compilerUntypedOutputRejectedSentence w n b q z) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add ((FormulaCodeSyntax.formulaCode w q b z).neg) (Context.add (empty z) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (empty z) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ ((FormulaCodeSyntax.formulaCode w q b z).neg) := .hyp (Or.inl rfl)
  exact ProjectCompilerTyping.reject_untyped hZ w n b q z h0 h1 h2

theorem compilerUntypedOutputRejected_kernel_certificate {m} (w n b q z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (compilerUntypedOutputRejectedSentence w n b q z)) := TheoryTransport.sentence (source_compilerUntypedOutputRejected w n b q z)

theorem native_compilerUntypedOutputRejected {m} (w n b q z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (compilerUntypedOutputRejectedSentence w n b q z)) := ZFReplay.replay (compilerUntypedOutputRejected_kernel_certificate w n b q z)

end PPAC.Migration.Internal.ObjectProjectCompilerTyping
