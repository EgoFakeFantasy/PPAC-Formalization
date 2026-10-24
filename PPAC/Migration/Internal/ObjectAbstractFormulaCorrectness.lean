import PPAC.Migration.Internal.AbstractTopFormula

/-! 实际 mode1 全公式集合归纳与原运行对应的 nativeZF 闭句证书。 -/
namespace PPAC.Migration.Internal.ObjectAbstractFormulaCorrectness
open Source SourceAlgebra SourceLogic OmegaSyntax

def modeOneAllFormulaCorrectSentence {m} (w : Fin m) : Source.Sentence := ((omega w).imp ((.all (AbstractUniformInductionSyntax.correct w.castSucc (Fin.last m))))).close

theorem source_modeOneAllFormulaCorrect {m} (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeOneAllFormulaCorrectSentence w) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact AbstractFormulaCorrectnessInduction.all_correct hZ w h0

theorem modeOneAllFormulaCorrect_kernel_certificate {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeOneAllFormulaCorrectSentence w)) := TheoryTransport.sentence (source_modeOneAllFormulaCorrect w)

theorem native_modeOneAllFormulaCorrect {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeOneAllFormulaCorrectSentence w)) := ZFReplay.replay (modeOneAllFormulaCorrect_kernel_certificate w)

def modeOneFormulaCorrectAtSentence {m} (w n : Fin m) : Source.Sentence := ((omega w).imp ((AbstractUniformInductionSyntax.correct w n))).close

theorem source_modeOneFormulaCorrectAt {m} (w n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeOneFormulaCorrectAtSentence w n) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact AbstractFormulaCorrectnessInduction.at_root hZ w n h0

theorem modeOneFormulaCorrectAt_kernel_certificate {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeOneFormulaCorrectAtSentence w n)) := TheoryTransport.sentence (source_modeOneFormulaCorrectAt w n)

theorem native_modeOneFormulaCorrectAt {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeOneFormulaCorrectAtSentence w n)) := ZFReplay.replay (modeOneFormulaCorrectAt_kernel_certificate w n)

def modeOneAllFramesIHSentence {m} (w n : Fin m) : Source.Sentence := ((omega w).imp ((AbstractUniformInductionSyntax.allFramesIH w n))).close

theorem source_modeOneAllFramesIH {m} (w n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeOneAllFramesIHSentence w n) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact AbstractFormulaCorrectnessInduction.all_frames_ih hZ w n h0

theorem modeOneAllFramesIH_kernel_certificate {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeOneAllFramesIHSentence w n)) := TheoryTransport.sentence (source_modeOneAllFramesIH w n)

theorem native_modeOneAllFramesIH {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeOneAllFramesIHSentence w n)) := ZFReplay.replay (modeOneAllFramesIH_kernel_certificate w n)

def modeOneFullFormulaRunExecutionIffSentence {m} (w n mode depth P a b c e R S q : Fin m) : Source.Sentence := ((omega w).imp ((AbstractOperationFrameSyntax.frame w mode depth P a b c e R S).imp ((FormulaCodeSyntax.formulaCode w n a b).imp (((OriginalTransformRowSyntax.run 3 w mode depth P n q).iff (FormulaTransformExecutionSyntax.executed w R S a b c e n q)))))).close

theorem source_modeOneFullFormulaRunExecutionIff {m} (w n mode depth P a b c e R S q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeOneFullFormulaRunExecutionIffSentence w n mode depth P a b c e R S q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (FormulaCodeSyntax.formulaCode w n a b) (Context.add (AbstractOperationFrameSyntax.frame w mode depth P a b c e R S) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (AbstractOperationFrameSyntax.frame w mode depth P a b c e R S) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (FormulaCodeSyntax.formulaCode w n a b) := .hyp (Or.inl rfl)
  exact AbstractFormulaCorrectnessInduction.run_iff_execution hZ w n mode depth P a b c e R S q h0 h1 h2

theorem modeOneFullFormulaRunExecutionIff_kernel_certificate {m} (w n mode depth P a b c e R S q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeOneFullFormulaRunExecutionIffSentence w n mode depth P a b c e R S q)) := TheoryTransport.sentence (source_modeOneFullFormulaRunExecutionIff w n mode depth P a b c e R S q)

theorem native_modeOneFullFormulaRunExecutionIff {m} (w n mode depth P a b c e R S q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeOneFullFormulaRunExecutionIffSentence w n mode depth P a b c e R S q)) := ZFReplay.replay (modeOneFullFormulaRunExecutionIff_kernel_certificate w n mode depth P a b c e R S q)

def modeOneActualHistoryAgreementSentence {m} (w n mode depth P a b c e R S h : Fin m) : Source.Sentence := ((omega w).imp ((OrdinalSyntax.ordinal n).imp ((FormulaTransformRecursionSyntax.graph w h n).imp ((AbstractOperationFrameSyntax.frame w mode depth P a b c e R S).imp ((OriginalFormulaHistoryAgreementSyntax.agreement w mode depth P h R S a b c e n)))))).close

theorem source_modeOneActualHistoryAgreement {m} (w n mode depth P a b c e R S h : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeOneActualHistoryAgreementSentence w n mode depth P a b c e R S h) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (AbstractOperationFrameSyntax.frame w mode depth P a b c e R S) (Context.add (FormulaTransformRecursionSyntax.graph w h n) (Context.add (OrdinalSyntax.ordinal n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (OrdinalSyntax.ordinal n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (FormulaTransformRecursionSyntax.graph w h n) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (AbstractOperationFrameSyntax.frame w mode depth P a b c e R S) := .hyp (Or.inl rfl)
  exact AbstractFormulaCorrectnessInduction.actual_history_agreement hZ w n mode depth P a b c e R S h h0 h1 h2 h3

theorem modeOneActualHistoryAgreement_kernel_certificate {m} (w n mode depth P a b c e R S h : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeOneActualHistoryAgreementSentence w n mode depth P a b c e R S h)) := TheoryTransport.sentence (source_modeOneActualHistoryAgreement w n mode depth P a b c e R S h)

theorem native_modeOneActualHistoryAgreement {m} (w n mode depth P a b c e R S h : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeOneActualHistoryAgreementSentence w n mode depth P a b c e R S h)) := ZFReplay.replay (modeOneActualHistoryAgreement_kernel_certificate w n mode depth P a b c e R S h)

def modeOneFullFormulaRunProgramIffSentence {m} (w n mode depth P a b c e R S h q : Fin m) : Source.Sentence := ((omega w).imp ((AbstractOperationFrameSyntax.frame w mode depth P a b c e R S).imp ((FormulaCodeSyntax.formulaCode w n a b).imp ((FormulaTransformRecursionSyntax.graph w h n).imp (((OriginalTransformRowSyntax.run 3 w mode depth P n q).iff (FormulaTransformProgramSyntax.run FormulaTransformProgramSyntax.formulaProgram w R S a b c e h n q))))))).close

theorem source_modeOneFullFormulaRunProgramIff {m} (w n mode depth P a b c e R S h q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeOneFullFormulaRunProgramIffSentence w n mode depth P a b c e R S h q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (FormulaTransformRecursionSyntax.graph w h n) (Context.add (FormulaCodeSyntax.formulaCode w n a b) (Context.add (AbstractOperationFrameSyntax.frame w mode depth P a b c e R S) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (AbstractOperationFrameSyntax.frame w mode depth P a b c e R S) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (FormulaCodeSyntax.formulaCode w n a b) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (FormulaTransformRecursionSyntax.graph w h n) := .hyp (Or.inl rfl)
  exact AbstractFormulaCorrectnessInduction.run_iff_program hZ w n mode depth P a b c e R S h q h0 h1 h2 h3

theorem modeOneFullFormulaRunProgramIff_kernel_certificate {m} (w n mode depth P a b c e R S h q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeOneFullFormulaRunProgramIffSentence w n mode depth P a b c e R S h q)) := TheoryTransport.sentence (source_modeOneFullFormulaRunProgramIff w n mode depth P a b c e R S h q)

theorem native_modeOneFullFormulaRunProgramIff {m} (w n mode depth P a b c e R S h q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeOneFullFormulaRunProgramIffSentence w n mode depth P a b c e R S h q)) := ZFReplay.replay (modeOneFullFormulaRunProgramIff_kernel_certificate w n mode depth P a b c e R S h q)

def modeOneAgreedHistoryExistsSentence {m} (w n mode depth P a b c e R S : Fin m) : Source.Sentence := ((omega w).imp ((FormulaCodeSyntax.formulaCode w n a b).imp ((AbstractOperationFrameSyntax.frame w mode depth P a b c e R S).imp ((OriginalFormulaInductionSyntax.agreedHistory w mode depth P R S a b c e n))))).close

theorem source_modeOneAgreedHistoryExists {m} (w n mode depth P a b c e R S : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeOneAgreedHistoryExistsSentence w n mode depth P a b c e R S) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (AbstractOperationFrameSyntax.frame w mode depth P a b c e R S) (Context.add (FormulaCodeSyntax.formulaCode w n a b) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (FormulaCodeSyntax.formulaCode w n a b) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (AbstractOperationFrameSyntax.frame w mode depth P a b c e R S) := .hyp (Or.inl rfl)
  exact AbstractFormulaCorrectnessInduction.agreed_history_exists hZ w n mode depth P a b c e R S h0 h1 h2

theorem modeOneAgreedHistoryExists_kernel_certificate {m} (w n mode depth P a b c e R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeOneAgreedHistoryExistsSentence w n mode depth P a b c e R S)) := TheoryTransport.sentence (source_modeOneAgreedHistoryExists w n mode depth P a b c e R S)

theorem native_modeOneAgreedHistoryExists {m} (w n mode depth P a b c e R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeOneAgreedHistoryExistsSentence w n mode depth P a b c e R S)) := ZFReplay.replay (modeOneAgreedHistoryExists_kernel_certificate w n mode depth P a b c e R S)

def modeOneActualTopFullFormulaExecutionIffSentence {m} (w n mode z P a b A B R S q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 1 mode).imp ((OriginalTermTraceSyntax.metadata w z P).imp ((empty z).imp ((SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S).imp ((FormulaCodeSyntax.formulaCode w n a B).imp (((OriginalTransformRowSyntax.run 3 w mode z P n q).iff (FormulaTransformExecutionSyntax.executed w R S a B A b n q))))))))).close

theorem source_modeOneActualTopFullFormulaExecutionIff {m} (w n mode z P a b A B R S q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeOneActualTopFullFormulaExecutionIffSentence w n mode z P a b A B R S q) := by
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
  exact AbstractTopFormula.run_iff_execution hZ w n mode z P a b A B R S q h0 h1 h2 h3 h4 h5

theorem modeOneActualTopFullFormulaExecutionIff_kernel_certificate {m} (w n mode z P a b A B R S q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeOneActualTopFullFormulaExecutionIffSentence w n mode z P a b A B R S q)) := TheoryTransport.sentence (source_modeOneActualTopFullFormulaExecutionIff w n mode z P a b A B R S q)

theorem native_modeOneActualTopFullFormulaExecutionIff {m} (w n mode z P a b A B R S q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeOneActualTopFullFormulaExecutionIffSentence w n mode z P a b A B R S q)) := ZFReplay.replay (modeOneActualTopFullFormulaExecutionIff_kernel_certificate w n mode z P a b A B R S q)

def modeOneActualTopFullFormulaProgramIffSentence {m} (w n mode z P a b A B R S h q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 1 mode).imp ((OriginalTermTraceSyntax.metadata w z P).imp ((empty z).imp ((SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S).imp ((FormulaCodeSyntax.formulaCode w n a B).imp ((FormulaTransformRecursionSyntax.graph w h n).imp (((OriginalTransformRowSyntax.run 3 w mode z P n q).iff (FormulaTransformProgramSyntax.run FormulaTransformProgramSyntax.formulaProgram w R S a B A b h n q)))))))))).close

theorem source_modeOneActualTopFullFormulaProgramIff {m} (w n mode z P a b A B R S h q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeOneActualTopFullFormulaProgramIffSentence w n mode z P a b A B R S h q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (FormulaTransformRecursionSyntax.graph w h n) (Context.add (FormulaCodeSyntax.formulaCode w n a B) (Context.add (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S) (Context.add (empty z) (Context.add (OriginalTermTraceSyntax.metadata w z P) (Context.add (SyntaxNumeralSyntax.numeral 1 mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 1 mode) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h2 : Derives Δ (OriginalTermTraceSyntax.metadata w z P) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h3 : Derives Δ (empty z) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : Derives Δ (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h5 : Derives Δ (FormulaCodeSyntax.formulaCode w n a B) := .hyp (Or.inr (Or.inl rfl))
  have h6 : Derives Δ (FormulaTransformRecursionSyntax.graph w h n) := .hyp (Or.inl rfl)
  exact AbstractTopFormula.run_iff_program hZ w n mode z P a b A B R S h q h0 h1 h2 h3 h4 h5 h6

theorem modeOneActualTopFullFormulaProgramIff_kernel_certificate {m} (w n mode z P a b A B R S h q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeOneActualTopFullFormulaProgramIffSentence w n mode z P a b A B R S h q)) := TheoryTransport.sentence (source_modeOneActualTopFullFormulaProgramIff w n mode z P a b A B R S h q)

theorem native_modeOneActualTopFullFormulaProgramIff {m} (w n mode z P a b A B R S h q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeOneActualTopFullFormulaProgramIffSentence w n mode z P a b A B R S h q)) := ZFReplay.replay (modeOneActualTopFullFormulaProgramIff_kernel_certificate w n mode z P a b A B R S h q)

end PPAC.Migration.Internal.ObjectAbstractFormulaCorrectness
