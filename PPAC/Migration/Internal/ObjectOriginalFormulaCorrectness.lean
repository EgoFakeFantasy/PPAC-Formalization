import PPAC.Migration.Internal.OriginalFormulaCorrectnessInduction

/-! 原mode0／3完整十一情况、全参数对象归纳消去及实际历史对应的原核闭句。 -/
namespace PPAC.Migration.Internal.ObjectOriginalFormulaCorrectness
open Source SourceAlgebra SourceLogic OmegaSyntax
open YesMetaZFC.Automation.ObjectHorn (Rule)

def fullElevenProgramFromUniformIffSentence {m} (three : Bool) (w n mode depth P a b c I J R S h q : Fin m) : Source.Sentence := ((omega w).imp ((OriginalUniformInductionSyntax.allFramesIH three w n).imp ((OriginalOperationFrameSyntax.frame three w mode depth P a b c I J R S).imp ((FormulaCodeSyntax.formulaCode w n a b).imp ((FormulaTransformRecursionSyntax.graph w h n).imp (((OriginalTransformRowSyntax.run 3 w mode depth (OriginalOperationFrameSyntax.parameter three P S) n q).iff (FormulaTransformProgramSyntax.run FormulaTransformProgramSyntax.formulaProgram w R S a b a c h n q)))))))).close

theorem source_fullElevenProgramFromUniformIff {m} (three : Bool) (w n mode depth P a b c I J R S h q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (fullElevenProgramFromUniformIffSentence three w n mode depth P a b c I J R S h q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (FormulaTransformRecursionSyntax.graph w h n) (Context.add (FormulaCodeSyntax.formulaCode w n a b) (Context.add (OriginalOperationFrameSyntax.frame three w mode depth P a b c I J R S) (Context.add (OriginalUniformInductionSyntax.allFramesIH three w n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (OriginalUniformInductionSyntax.allFramesIH three w n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (OriginalOperationFrameSyntax.frame three w mode depth P a b c I J R S) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (FormulaCodeSyntax.formulaCode w n a b) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (FormulaTransformRecursionSyntax.graph w h n) := .hyp (Or.inl rfl)
  exact OriginalFullFormulaProgram.program_iff hZ three w n mode depth P a b c I J R S h q h0 h1 h2 h3 h4

theorem fullElevenProgramFromUniformIff_kernel_certificate {m} (three : Bool) (w n mode depth P a b c I J R S h q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (fullElevenProgramFromUniformIffSentence three w n mode depth P a b c I J R S h q)) := TheoryTransport.sentence (source_fullElevenProgramFromUniformIff three w n mode depth P a b c I J R S h q)

theorem native_fullElevenProgramFromUniformIff {m} (three : Bool) (w n mode depth P a b c I J R S h q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (fullElevenProgramFromUniformIffSentence three w n mode depth P a b c I J R S h q)) := ZFReplay.replay (fullElevenProgramFromUniformIff_kernel_certificate three w n mode depth P a b c I J R S h q)

def wholeRunExecutedFromUniformIffSentence {m} (three : Bool) (w n mode depth P a b c I J R S q : Fin m) : Source.Sentence := ((omega w).imp ((OriginalUniformInductionSyntax.allFramesIH three w n).imp ((OriginalOperationFrameSyntax.frame three w mode depth P a b c I J R S).imp ((FormulaCodeSyntax.formulaCode w n a b).imp (((OriginalTransformRowSyntax.run 3 w mode depth (OriginalOperationFrameSyntax.parameter three P S) n q).iff (FormulaTransformExecutionSyntax.executed w R S a b a c n q))))))).close

theorem source_wholeRunExecutedFromUniformIff {m} (three : Bool) (w n mode depth P a b c I J R S q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (wholeRunExecutedFromUniformIffSentence three w n mode depth P a b c I J R S q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (FormulaCodeSyntax.formulaCode w n a b) (Context.add (OriginalOperationFrameSyntax.frame three w mode depth P a b c I J R S) (Context.add (OriginalUniformInductionSyntax.allFramesIH three w n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (OriginalUniformInductionSyntax.allFramesIH three w n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (OriginalOperationFrameSyntax.frame three w mode depth P a b c I J R S) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (FormulaCodeSyntax.formulaCode w n a b) := .hyp (Or.inl rfl)
  exact OriginalFormulaCorrectnessPoint.execution_iff_from_induction hZ three w n mode depth P a b c I J R S q h0 h1 h2 h3

theorem wholeRunExecutedFromUniformIff_kernel_certificate {m} (three : Bool) (w n mode depth P a b c I J R S q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (wholeRunExecutedFromUniformIffSentence three w n mode depth P a b c I J R S q)) := TheoryTransport.sentence (source_wholeRunExecutedFromUniformIff three w n mode depth P a b c I J R S q)

theorem native_wholeRunExecutedFromUniformIff {m} (three : Bool) (w n mode depth P a b c I J R S q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (wholeRunExecutedFromUniformIffSentence three w n mode depth P a b c I J R S q)) := ZFReplay.replay (wholeRunExecutedFromUniformIff_kernel_certificate three w n mode depth P a b c I J R S q)

def allParametersCorrectFromUniformSentence {m} (three : Bool) (w n : Fin m) : Source.Sentence := ((omega w).imp ((OriginalUniformInductionSyntax.allFramesIH three w n).imp ((OriginalUniformInductionSyntax.correct three w n)))).close

theorem source_allParametersCorrectFromUniform {m} (three : Bool) (w n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (allParametersCorrectFromUniformSentence three w n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (OriginalUniformInductionSyntax.allFramesIH three w n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (OriginalUniformInductionSyntax.allFramesIH three w n) := .hyp (Or.inl rfl)
  exact OriginalFormulaCorrectnessPoint.correct_from_induction hZ three w n h0 h1

theorem allParametersCorrectFromUniform_kernel_certificate {m} (three : Bool) (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (allParametersCorrectFromUniformSentence three w n)) := TheoryTransport.sentence (source_allParametersCorrectFromUniform three w n)

theorem native_allParametersCorrectFromUniform {m} (three : Bool) (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (allParametersCorrectFromUniformSentence three w n)) := ZFReplay.replay (allParametersCorrectFromUniform_kernel_certificate three w n)

def allInternalRootsCorrectSentence {m} (three : Bool) (w : Fin m) : Source.Sentence := ((omega w).imp ((.all (OriginalUniformInductionSyntax.correct three w.castSucc (Fin.last m))))).close

theorem source_allInternalRootsCorrect {m} (three : Bool) (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (allInternalRootsCorrectSentence three w) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact OriginalFormulaCorrectnessInduction.all_correct hZ three w h0

theorem allInternalRootsCorrect_kernel_certificate {m} (three : Bool) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (allInternalRootsCorrectSentence three w)) := TheoryTransport.sentence (source_allInternalRootsCorrect three w)

theorem native_allInternalRootsCorrect {m} (three : Bool) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (allInternalRootsCorrectSentence three w)) := ZFReplay.replay (allInternalRootsCorrect_kernel_certificate three w)

def uniformInductionDischargedSentence {m} (three : Bool) (w n : Fin m) : Source.Sentence := ((omega w).imp ((OriginalUniformInductionSyntax.allFramesIH three w n))).close

theorem source_uniformInductionDischarged {m} (three : Bool) (w n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (uniformInductionDischargedSentence three w n) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact OriginalFormulaCorrectnessInduction.all_frames_ih hZ three w n h0

theorem uniformInductionDischarged_kernel_certificate {m} (three : Bool) (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (uniformInductionDischargedSentence three w n)) := TheoryTransport.sentence (source_uniformInductionDischarged three w n)

theorem native_uniformInductionDischarged {m} (three : Bool) (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (uniformInductionDischargedSentence three w n)) := ZFReplay.replay (uniformInductionDischarged_kernel_certificate three w n)

def allInternalWholeRunExecutedIffSentence {m} (three : Bool) (w n mode depth P a b c I J R S q : Fin m) : Source.Sentence := ((omega w).imp ((OriginalOperationFrameSyntax.frame three w mode depth P a b c I J R S).imp ((FormulaCodeSyntax.formulaCode w n a b).imp (((OriginalTransformRowSyntax.run 3 w mode depth (OriginalOperationFrameSyntax.parameter three P S) n q).iff (FormulaTransformExecutionSyntax.executed w R S a b a c n q)))))).close

theorem source_allInternalWholeRunExecutedIff {m} (three : Bool) (w n mode depth P a b c I J R S q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (allInternalWholeRunExecutedIffSentence three w n mode depth P a b c I J R S q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (FormulaCodeSyntax.formulaCode w n a b) (Context.add (OriginalOperationFrameSyntax.frame three w mode depth P a b c I J R S) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (OriginalOperationFrameSyntax.frame three w mode depth P a b c I J R S) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (FormulaCodeSyntax.formulaCode w n a b) := .hyp (Or.inl rfl)
  exact OriginalFormulaCorrectnessInduction.run_iff_execution hZ three w n mode depth P a b c I J R S q h0 h1 h2

theorem allInternalWholeRunExecutedIff_kernel_certificate {m} (three : Bool) (w n mode depth P a b c I J R S q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (allInternalWholeRunExecutedIffSentence three w n mode depth P a b c I J R S q)) := TheoryTransport.sentence (source_allInternalWholeRunExecutedIff three w n mode depth P a b c I J R S q)

theorem native_allInternalWholeRunExecutedIff {m} (three : Bool) (w n mode depth P a b c I J R S q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (allInternalWholeRunExecutedIffSentence three w n mode depth P a b c I J R S q)) := ZFReplay.replay (allInternalWholeRunExecutedIff_kernel_certificate three w n mode depth P a b c I J R S q)

def allInternalWholeProgramIffSentence {m} (three : Bool) (w n mode depth P a b c I J R S h q : Fin m) : Source.Sentence := ((omega w).imp ((OriginalOperationFrameSyntax.frame three w mode depth P a b c I J R S).imp ((FormulaCodeSyntax.formulaCode w n a b).imp ((FormulaTransformRecursionSyntax.graph w h n).imp (((OriginalTransformRowSyntax.run 3 w mode depth (OriginalOperationFrameSyntax.parameter three P S) n q).iff (FormulaTransformProgramSyntax.run FormulaTransformProgramSyntax.formulaProgram w R S a b a c h n q))))))).close

theorem source_allInternalWholeProgramIff {m} (three : Bool) (w n mode depth P a b c I J R S h q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (allInternalWholeProgramIffSentence three w n mode depth P a b c I J R S h q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (FormulaTransformRecursionSyntax.graph w h n) (Context.add (FormulaCodeSyntax.formulaCode w n a b) (Context.add (OriginalOperationFrameSyntax.frame three w mode depth P a b c I J R S) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (OriginalOperationFrameSyntax.frame three w mode depth P a b c I J R S) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (FormulaCodeSyntax.formulaCode w n a b) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (FormulaTransformRecursionSyntax.graph w h n) := .hyp (Or.inl rfl)
  exact OriginalFormulaCorrectnessInduction.run_iff_program hZ three w n mode depth P a b c I J R S h q h0 h1 h2 h3

theorem allInternalWholeProgramIff_kernel_certificate {m} (three : Bool) (w n mode depth P a b c I J R S h q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (allInternalWholeProgramIffSentence three w n mode depth P a b c I J R S h q)) := TheoryTransport.sentence (source_allInternalWholeProgramIff three w n mode depth P a b c I J R S h q)

theorem native_allInternalWholeProgramIff {m} (three : Bool) (w n mode depth P a b c I J R S h q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (allInternalWholeProgramIffSentence three w n mode depth P a b c I J R S h q)) := ZFReplay.replay (allInternalWholeProgramIff_kernel_certificate three w n mode depth P a b c I J R S h q)

def actualHistoryAgreementDischargedSentence {m} (three : Bool) (w n mode depth P a b c I J R S h : Fin m) : Source.Sentence := ((omega w).imp ((OrdinalSyntax.ordinal n).imp ((FormulaTransformRecursionSyntax.graph w h n).imp ((OriginalOperationFrameSyntax.frame three w mode depth P a b c I J R S).imp ((OriginalFormulaHistoryAgreementSyntax.agreement w mode depth (OriginalOperationFrameSyntax.parameter three P S) h R S a b a c n)))))).close

theorem source_actualHistoryAgreementDischarged {m} (three : Bool) (w n mode depth P a b c I J R S h : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (actualHistoryAgreementDischargedSentence three w n mode depth P a b c I J R S h) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (OriginalOperationFrameSyntax.frame three w mode depth P a b c I J R S) (Context.add (FormulaTransformRecursionSyntax.graph w h n) (Context.add (OrdinalSyntax.ordinal n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (OrdinalSyntax.ordinal n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (FormulaTransformRecursionSyntax.graph w h n) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (OriginalOperationFrameSyntax.frame three w mode depth P a b c I J R S) := .hyp (Or.inl rfl)
  exact OriginalFormulaCorrectnessInduction.actual_history_agreement hZ three w n mode depth P a b c I J R S h h0 h1 h2 h3

theorem actualHistoryAgreementDischarged_kernel_certificate {m} (three : Bool) (w n mode depth P a b c I J R S h : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (actualHistoryAgreementDischargedSentence three w n mode depth P a b c I J R S h)) := TheoryTransport.sentence (source_actualHistoryAgreementDischarged three w n mode depth P a b c I J R S h)

theorem native_actualHistoryAgreementDischarged {m} (three : Bool) (w n mode depth P a b c I J R S h : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (actualHistoryAgreementDischargedSentence three w n mode depth P a b c I J R S h)) := ZFReplay.replay (actualHistoryAgreementDischarged_kernel_certificate three w n mode depth P a b c I J R S h)

def agreedActualHistoryExistsDischargedSentence {m} (three : Bool) (w n mode depth P a b c I J R S : Fin m) : Source.Sentence := ((omega w).imp ((FormulaCodeSyntax.formulaCode w n a b).imp ((OriginalOperationFrameSyntax.frame three w mode depth P a b c I J R S).imp ((OriginalFormulaInductionSyntax.agreedHistory w mode depth (OriginalOperationFrameSyntax.parameter three P S) R S a b a c n))))).close

theorem source_agreedActualHistoryExistsDischarged {m} (three : Bool) (w n mode depth P a b c I J R S : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (agreedActualHistoryExistsDischargedSentence three w n mode depth P a b c I J R S) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (OriginalOperationFrameSyntax.frame three w mode depth P a b c I J R S) (Context.add (FormulaCodeSyntax.formulaCode w n a b) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (FormulaCodeSyntax.formulaCode w n a b) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (OriginalOperationFrameSyntax.frame three w mode depth P a b c I J R S) := .hyp (Or.inl rfl)
  exact OriginalFormulaCorrectnessInduction.agreed_history_exists hZ three w n mode depth P a b c I J R S h0 h1 h2

theorem agreedActualHistoryExistsDischarged_kernel_certificate {m} (three : Bool) (w n mode depth P a b c I J R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (agreedActualHistoryExistsDischargedSentence three w n mode depth P a b c I J R S)) := TheoryTransport.sentence (source_agreedActualHistoryExistsDischarged three w n mode depth P a b c I J R S)

theorem native_agreedActualHistoryExistsDischarged {m} (three : Bool) (w n mode depth P a b c I J R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (agreedActualHistoryExistsDischargedSentence three w n mode depth P a b c I J R S)) := ZFReplay.replay (agreedActualHistoryExistsDischarged_kernel_certificate three w n mode depth P a b c I J R S)

end PPAC.Migration.Internal.ObjectOriginalFormulaCorrectness
