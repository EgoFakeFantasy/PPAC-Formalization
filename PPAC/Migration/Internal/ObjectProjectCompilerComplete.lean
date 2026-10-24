import PPAC.Migration.Internal.ProjectCompilerComplete

/-! All internal legal Project source codes have actual typed compiler outputs; scalar uniqueness remains unproved in the original nativeZF kernel; complete schema tests and Con remain unproved. -/
namespace PPAC.Migration.Internal.ObjectProjectCompilerComplete
open Source SourceAlgebra SourceLogic OmegaSyntax

def compilerSourceAtomsActualOutputSentence {m} (w n b f z : Fin m) : Source.Sentence := ((omega w).imp ((empty z).imp ((ProjectSourceAtomSyntax.atomic w b f n).imp ((ProjectCompilerCompleteSyntax.existsOutput w n b))))).close

theorem source_compilerSourceAtomsActualOutput {m} (w n b f z : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (compilerSourceAtomsActualOutputSentence w n b f z) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ProjectSourceAtomSyntax.atomic w b f n) (Context.add (empty z) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (empty z) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (ProjectSourceAtomSyntax.atomic w b f n) := .hyp (Or.inl rfl)
  exact ProjectCompilerCompleteAtoms.all_atoms hZ w n b f z h0 h1 h2

theorem compilerSourceAtomsActualOutput_kernel_certificate {m} (w n b f z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (compilerSourceAtomsActualOutputSentence w n b f z)) := TheoryTransport.sentence (source_compilerSourceAtomsActualOutput w n b f z)

theorem native_compilerSourceAtomsActualOutput {m} (w n b f z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (compilerSourceAtomsActualOutputSentence w n b f z)) := ZFReplay.replay (compilerSourceAtomsActualOutput_kernel_certificate w n b f z)

def compilerSourceChildOutputFromMemberIHSentence {m} (w n x b f z : Fin m) : Source.Sentence := ((empty z).imp ((ProjectCompilerCompleteSyntax.allIH w n).imp ((Formula.mem x n).imp ((ProjectSourceCodeSyntax.sourceCode w x b f).imp ((ProjectCompilerCompleteSyntax.existsOutput w x b)))))).close

theorem source_compilerSourceChildOutputFromMemberIH {m} (w n x b f z : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (compilerSourceChildOutputFromMemberIHSentence w n x b f z) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ProjectSourceCodeSyntax.sourceCode w x b f) (Context.add (Formula.mem x n) (Context.add (ProjectCompilerCompleteSyntax.allIH w n) (Context.add (empty z) (Source.SetLanguage.ZF.at m))))
  have h0 : Derives Δ (empty z) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (ProjectCompilerCompleteSyntax.allIH w n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (Formula.mem x n) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (ProjectSourceCodeSyntax.sourceCode w x b f) := .hyp (Or.inl rfl)
  exact ProjectCompilerCompleteQueries.child_output w n x b f z h0 h1 h2 h3

theorem compilerSourceChildOutputFromMemberIH_kernel_certificate {m} (w n x b f z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (compilerSourceChildOutputFromMemberIHSentence w n x b f z)) := TheoryTransport.sentence (source_compilerSourceChildOutputFromMemberIH w n x b f z)

theorem native_compilerSourceChildOutputFromMemberIH {m} (w n x b f z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (compilerSourceChildOutputFromMemberIHSentence w n x b f z)) := ZFReplay.replay (compilerSourceChildOutputFromMemberIH_kernel_certificate w n x b f z)

def compilerSourceOutputFromMemberIHSentence {m} (w n b f z : Fin m) : Source.Sentence := ((omega w).imp ((empty z).imp ((ProjectCompilerCompleteSyntax.allIH w n).imp ((ProjectSourceCodeSyntax.sourceCode w n b f).imp ((ProjectCompilerCompleteSyntax.existsOutput w n b)))))).close

theorem source_compilerSourceOutputFromMemberIH {m} (w n b f z : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (compilerSourceOutputFromMemberIHSentence w n b f z) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ProjectSourceCodeSyntax.sourceCode w n b f) (Context.add (ProjectCompilerCompleteSyntax.allIH w n) (Context.add (empty z) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (empty z) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (ProjectCompilerCompleteSyntax.allIH w n) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (ProjectSourceCodeSyntax.sourceCode w n b f) := .hyp (Or.inl rfl)
  exact ProjectCompilerCompleteStep.output_from_induction hZ w n b f z h0 h1 h2 h3

theorem compilerSourceOutputFromMemberIH_kernel_certificate {m} (w n b f z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (compilerSourceOutputFromMemberIHSentence w n b f z)) := TheoryTransport.sentence (source_compilerSourceOutputFromMemberIH w n b f z)

theorem native_compilerSourceOutputFromMemberIH {m} (w n b f z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (compilerSourceOutputFromMemberIHSentence w n b f z)) := ZFReplay.replay (compilerSourceOutputFromMemberIH_kernel_certificate w n b f z)

def compilerCompletenessPropertyStepSentence {m} (w n : Fin m) : Source.Sentence := ((omega w).imp ((ProjectCompilerCompleteSyntax.allIH w n).imp ((ProjectCompilerCompleteSyntax.correct w n)))).close

theorem source_compilerCompletenessPropertyStep {m} (w n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (compilerCompletenessPropertyStepSentence w n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ProjectCompilerCompleteSyntax.allIH w n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (ProjectCompilerCompleteSyntax.allIH w n) := .hyp (Or.inl rfl)
  exact ProjectCompilerCompleteStep.from_induction hZ w n h0 h1

theorem compilerCompletenessPropertyStep_kernel_certificate {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (compilerCompletenessPropertyStepSentence w n)) := TheoryTransport.sentence (source_compilerCompletenessPropertyStep w n)

theorem native_compilerCompletenessPropertyStep {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (compilerCompletenessPropertyStepSentence w n)) := ZFReplay.replay (compilerCompletenessPropertyStep_kernel_certificate w n)

def compilerCompletenessProgressiveSentence {m} (w : Fin m) : Source.Sentence := ((omega w).imp ((SetInductionSyntax.progressive ProjectCompilerComplete.inductionMatrix (fun _ : Fin 1 => w)))).close

theorem source_compilerCompletenessProgressive {m} (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (compilerCompletenessProgressiveSentence w) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact ProjectCompilerComplete.progressive hZ w h0

theorem compilerCompletenessProgressive_kernel_certificate {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (compilerCompletenessProgressiveSentence w)) := TheoryTransport.sentence (source_compilerCompletenessProgressive w)

theorem native_compilerCompletenessProgressive {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (compilerCompletenessProgressiveSentence w)) := ZFReplay.replay (compilerCompletenessProgressive_kernel_certificate w)

def compilerAllInternalCompletenessPropertySentence {m} (w : Fin m) : Source.Sentence := ((omega w).imp ((.all (ProjectCompilerCompleteSyntax.correct w.castSucc (Fin.last m))))).close

theorem source_compilerAllInternalCompletenessProperty {m} (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (compilerAllInternalCompletenessPropertySentence w) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact ProjectCompilerComplete.all_correct hZ w h0

theorem compilerAllInternalCompletenessProperty_kernel_certificate {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (compilerAllInternalCompletenessPropertySentence w)) := TheoryTransport.sentence (source_compilerAllInternalCompletenessProperty w)

theorem native_compilerAllInternalCompletenessProperty {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (compilerAllInternalCompletenessPropertySentence w)) := ZFReplay.replay (compilerAllInternalCompletenessProperty_kernel_certificate w)

def compilerSourceInputActualOutputExistsSentence {m} (w n b f : Fin m) : Source.Sentence := ((omega w).imp ((ProjectSourceCodeSyntax.sourceCode w n b f).imp ((ProjectCompilerCompleteSyntax.existsOutput w n b)))).close

theorem source_compilerSourceInputActualOutputExists {m} (w n b f : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (compilerSourceInputActualOutputExistsSentence w n b f) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ProjectSourceCodeSyntax.sourceCode w n b f) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (ProjectSourceCodeSyntax.sourceCode w n b f) := .hyp (Or.inl rfl)
  exact ProjectCompilerComplete.output_exists_without_zero hZ w n b f h0 h1

theorem compilerSourceInputActualOutputExists_kernel_certificate {m} (w n b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (compilerSourceInputActualOutputExistsSentence w n b f)) := TheoryTransport.sentence (source_compilerSourceInputActualOutputExists w n b f)

theorem native_compilerSourceInputActualOutputExists {m} (w n b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (compilerSourceInputActualOutputExistsSentence w n b f)) := ZFReplay.replay (compilerSourceInputActualOutputExists_kernel_certificate w n b f)

def compilerAllInternalSourceOutputsExistSentence {m} (w : Fin m) : Source.Sentence := ((omega w).imp ((ProjectCompilerComplete.allSourceLaw w))).close

theorem source_compilerAllInternalSourceOutputsExist {m} (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (compilerAllInternalSourceOutputsExistSentence w) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact ProjectCompilerComplete.all_source_outputs hZ w h0

theorem compilerAllInternalSourceOutputsExist_kernel_certificate {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (compilerAllInternalSourceOutputsExistSentence w)) := TheoryTransport.sentence (source_compilerAllInternalSourceOutputsExist w)

theorem native_compilerAllInternalSourceOutputsExist {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (compilerAllInternalSourceOutputsExistSentence w)) := ZFReplay.replay (compilerAllInternalSourceOutputsExist_kernel_certificate w)

def compilerSourceInputActualTypedOutputExistsSentence {m} (w n b f z : Fin m) : Source.Sentence := ((omega w).imp ((empty z).imp ((ProjectSourceCodeSyntax.sourceCode w n b f).imp ((ProjectCompilerBase.existsTyped w n b z))))).close

theorem source_compilerSourceInputActualTypedOutputExists {m} (w n b f z : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (compilerSourceInputActualTypedOutputExistsSentence w n b f z) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ProjectSourceCodeSyntax.sourceCode w n b f) (Context.add (empty z) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (empty z) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (ProjectSourceCodeSyntax.sourceCode w n b f) := .hyp (Or.inl rfl)
  exact ProjectCompilerComplete.typed_output_exists hZ w n b f z h0 h1 h2

theorem compilerSourceInputActualTypedOutputExists_kernel_certificate {m} (w n b f z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (compilerSourceInputActualTypedOutputExistsSentence w n b f z)) := TheoryTransport.sentence (source_compilerSourceInputActualTypedOutputExists w n b f z)

theorem native_compilerSourceInputActualTypedOutputExists {m} (w n b f z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (compilerSourceInputActualTypedOutputExistsSentence w n b f z)) := ZFReplay.replay (compilerSourceInputActualTypedOutputExists_kernel_certificate w n b f z)

end PPAC.Migration.Internal.ObjectProjectCompilerComplete
