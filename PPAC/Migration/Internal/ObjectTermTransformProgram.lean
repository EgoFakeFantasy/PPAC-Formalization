import PPAC.Migration.Internal.TermTransformProgramCode

/-! 独立固定项程序的全部内部运行时正确性、拒绝性质及实际纤维的原YesMetaZFC核证书。 -/
namespace PPAC.Migration.Internal.ObjectTermTransformProgram
open Source SourceAlgebra SourceLogic OmegaSyntax

def variableRunSentence {m} (isBound : Bool) (w R S n q i : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxVariableSyntax.code isBound w i n).imp (((TermTransformProgramSyntax.run TermTransformProgramSyntax.termProgram w R S n q).iff (StructuralListFieldSyntax.field w (SyntaxIndexMapSyntax.selectMap isBound R S) i q))))).close

theorem source_variableRun {m} (isBound : Bool) (w R S n q i : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (variableRunSentence isBound w R S n q i) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxVariableSyntax.code isBound w i n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxVariableSyntax.code isBound w i n) := .hyp (Or.inl rfl)
  exact TermTransformProgramVariable.at_variable hZ isBound w R S n q i h0 h1

theorem variableRun_kernel_certificate {m} (isBound : Bool) (w R S n q i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (variableRunSentence isBound w R S n q i)) := TheoryTransport.sentence (source_variableRun isBound w R S n q i)

theorem native_variableRun {m} (isBound : Bool) (w R S n q i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (variableRunSentence isBound w R S n q i)) := ZFReplay.replay (variableRun_kernel_certificate isBound w R S n q i)

def defaultRunSentence {m} (w R S n q : Fin m) : Source.Sentence := (((SyntaxVariableDecodeSyntax.recognized true w n).neg).imp (((SyntaxVariableDecodeSyntax.recognized false w n).neg).imp (((TermTransformProgramSyntax.run TermTransformProgramSyntax.termProgram w R S n q).iff (.equal q n))))).close

theorem source_defaultRun {m} (w R S n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (defaultRunSentence w R S n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add ((SyntaxVariableDecodeSyntax.recognized false w n).neg) (Context.add ((SyntaxVariableDecodeSyntax.recognized true w n).neg) (Source.SetLanguage.ZF.at m))
  have h0 : Derives Δ ((SyntaxVariableDecodeSyntax.recognized true w n).neg) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ ((SyntaxVariableDecodeSyntax.recognized false w n).neg) := .hyp (Or.inl rfl)
  exact TermTransformProgramVariable.copy_default_iff w R S n q h0 h1

theorem defaultRun_kernel_certificate {m} (w R S n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (defaultRunSentence w R S n q)) := TheoryTransport.sentence (source_defaultRun w R S n q)

theorem native_defaultRun {m} (w R S n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (defaultRunSentence w R S n q)) := ZFReplay.replay (defaultRun_kernel_certificate w R S n q)

def checkedIffSentence {m} (w R S a b c d n q : Fin m) : Source.Sentence := ((omega w).imp (((TermTransformProgramSyntax.checked w R S a b c d n q).iff (SyntaxCodedMixedTermSyntax.substituted w R S a b c d n q)))).close

theorem source_checkedIff {m} (w R S a b c d n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (checkedIffSentence w R S a b c d n q) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact TermTransformProgramCorrectness.checked_iff hZ w R S a b c d n q h0

theorem checkedIff_kernel_certificate {m} (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (checkedIffSentence w R S a b c d n q)) := TheoryTransport.sentence (source_checkedIff w R S a b c d n q)

theorem native_checkedIff {m} (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (checkedIffSentence w R S a b c d n q)) := ZFReplay.replay (checkedIff_kernel_certificate w R S a b c d n q)

def rejectEnvironmentSentence {m} (w R S a b c d n q : Fin m) : Source.Sentence := (((SyntaxMixedImageCodeSyntax.termLists w a b c d R S).neg).imp (((TermTransformProgramSyntax.checked w R S a b c d n q).neg))).close

theorem source_rejectEnvironment {m} (w R S a b c d n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (rejectEnvironmentSentence w R S a b c d n q) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add ((SyntaxMixedImageCodeSyntax.termLists w a b c d R S).neg) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ ((SyntaxMixedImageCodeSyntax.termLists w a b c d R S).neg) := .hyp (Or.inl rfl)
  exact TermTransformProgramValue.reject_environment w R S a b c d n q h0

theorem rejectEnvironment_kernel_certificate {m} (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (rejectEnvironmentSentence w R S a b c d n q)) := TheoryTransport.sentence (source_rejectEnvironment w R S a b c d n q)

theorem native_rejectEnvironment {m} (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (rejectEnvironmentSentence w R S a b c d n q)) := ZFReplay.replay (rejectEnvironment_kernel_certificate w R S a b c d n q)

def rejectSourceSentence {m} (w R S a b c d n q : Fin m) : Source.Sentence := (((SyntaxTermSyntax.term w a b n).neg).imp (((TermTransformProgramSyntax.checked w R S a b c d n q).neg))).close

theorem source_rejectSource {m} (w R S a b c d n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (rejectSourceSentence w R S a b c d n q) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add ((SyntaxTermSyntax.term w a b n).neg) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ ((SyntaxTermSyntax.term w a b n).neg) := .hyp (Or.inl rfl)
  exact TermTransformProgramValue.reject_source w R S a b c d n q h0

theorem rejectSource_kernel_certificate {m} (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (rejectSourceSentence w R S a b c d n q)) := TheoryTransport.sentence (source_rejectSource w R S a b c d n q)

theorem native_rejectSource {m} (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (rejectSourceSentence w R S a b c d n q)) := ZFReplay.replay (rejectSource_kernel_certificate w R S a b c d n q)

def targetTypeSentence {m} (w R S a b c d n q : Fin m) : Source.Sentence := ((omega w).imp ((TermTransformProgramSyntax.checked w R S a b c d n q).imp ((SyntaxTermSyntax.term w c d q)))).close

theorem source_targetType {m} (w R S a b c d n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (targetTypeSentence w R S a b c d n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (TermTransformProgramSyntax.checked w R S a b c d n q) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (TermTransformProgramSyntax.checked w R S a b c d n q) := .hyp (Or.inl rfl)
  exact TermTransformProgramValue.target_type hZ w R S a b c d n q h0 h1

theorem targetType_kernel_certificate {m} (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (targetTypeSentence w R S a b c d n q)) := TheoryTransport.sentence (source_targetType w R S a b c d n q)

theorem native_targetType {m} (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (targetTypeSentence w R S a b c d n q)) := ZFReplay.replay (targetType_kernel_certificate w R S a b c d n q)

def outputNaturalSentence {m} (w R S a b c d n q : Fin m) : Source.Sentence := ((omega w).imp ((TermTransformProgramSyntax.checked w R S a b c d n q).imp ((Formula.mem q w)))).close

theorem source_outputNatural {m} (w R S a b c d n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (outputNaturalSentence w R S a b c d n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (TermTransformProgramSyntax.checked w R S a b c d n q) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (TermTransformProgramSyntax.checked w R S a b c d n q) := .hyp (Or.inl rfl)
  exact TermTransformProgramValue.output_natural hZ w R S a b c d n q h0 h1

theorem outputNatural_kernel_certificate {m} (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (outputNaturalSentence w R S a b c d n q)) := TheoryTransport.sentence (source_outputNatural w R S a b c d n q)

theorem native_outputNatural {m} (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (outputNaturalSentence w R S a b c d n q)) := ZFReplay.replay (outputNatural_kernel_certificate w R S a b c d n q)

def rejectTargetSentence {m} (w R S a b c d n q : Fin m) : Source.Sentence := ((omega w).imp (((SyntaxTermSyntax.term w c d q).neg).imp (((TermTransformProgramSyntax.checked w R S a b c d n q).neg)))).close

theorem source_rejectTarget {m} (w R S a b c d n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (rejectTargetSentence w R S a b c d n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add ((SyntaxTermSyntax.term w c d q).neg) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ ((SyntaxTermSyntax.term w c d q).neg) := .hyp (Or.inl rfl)
  exact TermTransformProgramValue.reject_target hZ w R S a b c d n q h0 h1

theorem rejectTarget_kernel_certificate {m} (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (rejectTargetSentence w R S a b c d n q)) := TheoryTransport.sentence (source_rejectTarget w R S a b c d n q)

theorem native_rejectTarget {m} (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (rejectTargetSentence w R S a b c d n q)) := ZFReplay.replay (rejectTarget_kernel_certificate w R S a b c d n q)

def rejectOutputNaturalSentence {m} (w R S a b c d n q : Fin m) : Source.Sentence := ((omega w).imp (((Formula.mem q w).neg).imp (((TermTransformProgramSyntax.checked w R S a b c d n q).neg)))).close

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
  exact TermTransformProgramValue.reject_output_natural hZ w R S a b c d n q h0 h1

theorem rejectOutputNatural_kernel_certificate {m} (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (rejectOutputNaturalSentence w R S a b c d n q)) := TheoryTransport.sentence (source_rejectOutputNatural w R S a b c d n q)

theorem native_rejectOutputNatural {m} (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (rejectOutputNaturalSentence w R S a b c d n q)) := ZFReplay.replay (rejectOutputNatural_kernel_certificate w R S a b c d n q)

def uniqueSentence {m} (w R S a b c d n q v : Fin m) : Source.Sentence := ((omega w).imp ((TermTransformProgramSyntax.checked w R S a b c d n q).imp ((TermTransformProgramSyntax.checked w R S a b c d n v).imp ((.equal q v))))).close

theorem source_unique {m} (w R S a b c d n q v : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (uniqueSentence w R S a b c d n q v) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (TermTransformProgramSyntax.checked w R S a b c d n v) (Context.add (TermTransformProgramSyntax.checked w R S a b c d n q) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (TermTransformProgramSyntax.checked w R S a b c d n q) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (TermTransformProgramSyntax.checked w R S a b c d n v) := .hyp (Or.inl rfl)
  exact TermTransformProgramValue.unique hZ w R S a b c d n q v h0 h1 h2

theorem unique_kernel_certificate {m} (w R S a b c d n q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (uniqueSentence w R S a b c d n q v)) := TheoryTransport.sentence (source_unique w R S a b c d n q v)

theorem native_unique {m} (w R S a b c d n q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (uniqueSentence w R S a b c d n q v)) := ZFReplay.replay (unique_kernel_certificate w R S a b c d n q v)

def uniqueOutputSentence {m} (w R S a b c d n q : Fin m) : Source.Sentence := ((omega w).imp ((TermTransformProgramSyntax.checked w R S a b c d n q).imp ((TermTransformProgramValueSyntax.uniqueOutput w R S a b c d n q)))).close

theorem source_uniqueOutput {m} (w R S a b c d n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (uniqueOutputSentence w R S a b c d n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (TermTransformProgramSyntax.checked w R S a b c d n q) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (TermTransformProgramSyntax.checked w R S a b c d n q) := .hyp (Or.inl rfl)
  exact TermTransformProgramValue.unique_output hZ w R S a b c d n q h0 h1

theorem uniqueOutput_kernel_certificate {m} (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (uniqueOutputSentence w R S a b c d n q)) := TheoryTransport.sentence (source_uniqueOutput w R S a b c d n q)

theorem native_uniqueOutput {m} (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (uniqueOutputSentence w R S a b c d n q)) := ZFReplay.replay (uniqueOutput_kernel_certificate w R S a b c d n q)

def atCandidateSentence {m} (w R S a b c d n q : Fin m) : Source.Sentence := ((omega w).imp ((TermTransformProgramSyntax.checked w R S a b c d n q).imp ((TermTransformProgramValueSyntax.value w R S a b c d n q)))).close

theorem source_atCandidate {m} (w R S a b c d n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (atCandidateSentence w R S a b c d n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (TermTransformProgramSyntax.checked w R S a b c d n q) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (TermTransformProgramSyntax.checked w R S a b c d n q) := .hyp (Or.inl rfl)
  exact TermTransformProgramValue.at_candidate hZ w R S a b c d n q h0 h1

theorem atCandidate_kernel_certificate {m} (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (atCandidateSentence w R S a b c d n q)) := TheoryTransport.sentence (source_atCandidate w R S a b c d n q)

theorem native_atCandidate {m} (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (atCandidateSentence w R S a b c d n q)) := ZFReplay.replay (atCandidate_kernel_certificate w R S a b c d n q)

def actualFiberSentence {m} (w R S a b c d n : Fin m) : Source.Sentence := ((omega w).imp ((TermTransformProgramSyntax.inputGuard w R S a b c d n).imp ((TermTransformProgramValueSyntax.fiber w R S a b c d n)))).close

theorem source_actualFiber {m} (w R S a b c d n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (actualFiberSentence w R S a b c d n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (TermTransformProgramSyntax.inputGuard w R S a b c d n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (TermTransformProgramSyntax.inputGuard w R S a b c d n) := .hyp (Or.inl rfl)
  exact TermTransformProgramValue.actual_fiber hZ w R S a b c d n h0 h1

theorem actualFiber_kernel_certificate {m} (w R S a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (actualFiberSentence w R S a b c d n)) := TheoryTransport.sentence (source_actualFiber w R S a b c d n)

theorem native_actualFiber {m} (w R S a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (actualFiberSentence w R S a b c d n)) := ZFReplay.replay (actualFiber_kernel_certificate w R S a b c d n)

def fiberIffInputSentence {m} (w R S a b c d n : Fin m) : Source.Sentence := ((omega w).imp (((TermTransformProgramValueSyntax.fiber w R S a b c d n).iff (TermTransformProgramSyntax.inputGuard w R S a b c d n)))).close

theorem source_fiberIffInput {m} (w R S a b c d n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (fiberIffInputSentence w R S a b c d n) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact TermTransformProgramValue.fiber_iff_input hZ w R S a b c d n h0

theorem fiberIffInput_kernel_certificate {m} (w R S a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (fiberIffInputSentence w R S a b c d n)) := TheoryTransport.sentence (source_fiberIffInput w R S a b c d n)

theorem native_fiberIffInput {m} (w R S a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (fiberIffInputSentence w R S a b c d n)) := ZFReplay.replay (fiberIffInput_kernel_certificate w R S a b c d n)

def encodedCheckedIffSentence {m} (w P R S a b c d n q : Fin m) : Source.Sentence := ((omega w).imp ((TermTransformProgramCodeSyntax.code w P).imp ((TermTransformProgramCodeSyntax.correctAt w P R S a b c d n q)))).close

theorem source_encodedCheckedIff {m} (w P R S a b c d n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (encodedCheckedIffSentence w P R S a b c d n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (TermTransformProgramCodeSyntax.code w P) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (TermTransformProgramCodeSyntax.code w P) := .hyp (Or.inl rfl)
  exact TermTransformProgramCode.encoded_checked_iff hZ w P R S a b c d n q h0 h1

theorem encodedCheckedIff_kernel_certificate {m} (w P R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (encodedCheckedIffSentence w P R S a b c d n q)) := TheoryTransport.sentence (source_encodedCheckedIff w P R S a b c d n q)

theorem native_encodedCheckedIff {m} (w P R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (encodedCheckedIffSentence w P R S a b c d n q)) := ZFReplay.replay (encodedCheckedIff_kernel_certificate w P R S a b c d n q)

def uniformCorrectnessSentence {m} (w P : Fin m) : Source.Sentence := ((omega w).imp ((TermTransformProgramCodeSyntax.code w P).imp ((TermTransformProgramCodeSyntax.uniform w P)))).close

theorem source_uniformCorrectness {m} (w P : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (uniformCorrectnessSentence w P) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (TermTransformProgramCodeSyntax.code w P) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (TermTransformProgramCodeSyntax.code w P) := .hyp (Or.inl rfl)
  exact TermTransformProgramCode.uniform_correctness hZ w P h0 h1

theorem uniformCorrectness_kernel_certificate {m} (w P : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (uniformCorrectnessSentence w P)) := TheoryTransport.sentence (source_uniformCorrectness w P)

theorem native_uniformCorrectness {m} (w P : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (uniformCorrectnessSentence w P)) := ZFReplay.replay (uniformCorrectness_kernel_certificate w P)

def uniqueCodeSentence {m} (w P : Fin m) : Source.Sentence := ((omega w).imp ((TermTransformProgramCodeSyntax.code w P).imp ((TermTransformProgramCodeSyntax.uniqueCode w P)))).close

theorem source_uniqueCode {m} (w P : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (uniqueCodeSentence w P) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (TermTransformProgramCodeSyntax.code w P) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (TermTransformProgramCodeSyntax.code w P) := .hyp (Or.inl rfl)
  exact TermTransformProgramCode.unique_code hZ w P h0 h1

theorem uniqueCode_kernel_certificate {m} (w P : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (uniqueCodeSentence w P)) := TheoryTransport.sentence (source_uniqueCode w P)

theorem native_uniqueCode {m} (w P : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (uniqueCodeSentence w P)) := ZFReplay.replay (uniqueCode_kernel_certificate w P)

def atCodeSentence {m} (w P : Fin m) : Source.Sentence := ((omega w).imp ((TermTransformProgramCodeSyntax.code w P).imp ((TermTransformProgramCodeSyntax.programValue w P)))).close

theorem source_atCode {m} (w P : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (atCodeSentence w P) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (TermTransformProgramCodeSyntax.code w P) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (TermTransformProgramCodeSyntax.code w P) := .hyp (Or.inl rfl)
  exact TermTransformProgramCode.at_code hZ w P h0 h1

theorem atCode_kernel_certificate {m} (w P : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (atCodeSentence w P)) := TheoryTransport.sentence (source_atCode w P)

theorem native_atCode {m} (w P : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (atCodeSentence w P)) := ZFReplay.replay (atCode_kernel_certificate w P)

def existsCorrectProgramSentence {m} (w : Fin m) : Source.Sentence := ((omega w).imp ((TermTransformProgramCodeSyntax.existsProgram w))).close

theorem source_existsCorrectProgram {m} (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (existsCorrectProgramSentence w) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact TermTransformProgramCode.exists_correct_program hZ w h0

theorem existsCorrectProgram_kernel_certificate {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (existsCorrectProgramSentence w)) := TheoryTransport.sentence (source_existsCorrectProgram w)

theorem native_existsCorrectProgram {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (existsCorrectProgramSentence w)) := ZFReplay.replay (existsCorrectProgram_kernel_certificate w)

end PPAC.Migration.Internal.ObjectTermTransformProgram
