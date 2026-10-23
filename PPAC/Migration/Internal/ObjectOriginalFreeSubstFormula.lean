import PPAC.Migration.Internal.OriginalFreeSubstFormulaRun

/-! 空绑定界纯项列表、原mode3全公式自由替换对应及其原核闭句。 -/
namespace PPAC.Migration.Internal.ObjectOriginalFreeSubstFormula
open Source SourceAlgebra SourceLogic OmegaSyntax
open YesMetaZFC.Automation.ObjectHorn (Rule)

def emptyBoundTermFreeSentence {m} (w z c t : Fin m) : Source.Sentence := ((empty z).imp ((SyntaxTermSyntax.term w z c t).imp ((SyntaxTermSyntax.branch false w c t)))).close

theorem source_emptyBoundTermFree {m} (w z c t : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (emptyBoundTermFreeSentence w z c t) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTermSyntax.term w z c t) (Context.add (empty z) (Source.SetLanguage.ZF.at m))
  have h0 : Derives Δ (empty z) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxTermSyntax.term w z c t) := .hyp (Or.inl rfl)
  exact EmptyBoundFreeInputs.term_free w z c t h0 h1

theorem emptyBoundTermFree_kernel_certificate {m} (w z c t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (emptyBoundTermFreeSentence w z c t)) := TheoryTransport.sentence (source_emptyBoundTermFree w z c t)

theorem native_emptyBoundTermFree {m} (w z c t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (emptyBoundTermFreeSentence w z c t)) := ZFReplay.replay (emptyBoundTermFree_kernel_certificate w z c t)

def emptyBoundListsIffSentence {m} (w a z c L : Fin m) : Source.Sentence := ((omega w).imp ((empty z).imp (((SyntaxMixedImageCodeSyntax.termList w a z c L).iff (SyntaxFreeSubstSyntax.termList w a c L))))).close

theorem source_emptyBoundListsIff {m} (w a z c L : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (emptyBoundListsIffSentence w a z c L) := by
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
  exact EmptyBoundFreeInputs.list_iff hZ w a z c L h0 h1

theorem emptyBoundListsIff_kernel_certificate {m} (w a z c L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (emptyBoundListsIffSentence w a z c L)) := TheoryTransport.sentence (source_emptyBoundListsIff w a z c L)

theorem native_emptyBoundListsIff {m} (w a z c L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (emptyBoundListsIffSentence w a z c L)) := ZFReplay.replay (emptyBoundListsIff_kernel_certificate w a z c L)

def emptyBoundConversionExistsSentence {m} (w a z c L : Fin m) : Source.Sentence := ((omega w).imp ((empty z).imp ((SyntaxMixedImageCodeSyntax.termList w a z c L).imp ((SyntaxFreeSubstFiber.mapExists w a c L))))).close

theorem source_emptyBoundConversionExists {m} (w a z c L : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (emptyBoundConversionExistsSentence w a z c L) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMixedImageCodeSyntax.termList w a z c L) (Context.add (empty z) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (empty z) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxMixedImageCodeSyntax.termList w a z c L) := .hyp (Or.inl rfl)
  exact EmptyBoundFreeInputs.conversion_exists hZ w a z c L h0 h1 h2

theorem emptyBoundConversionExists_kernel_certificate {m} (w a z c L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (emptyBoundConversionExistsSentence w a z c L)) := TheoryTransport.sentence (source_emptyBoundConversionExists w a z c L)

theorem native_emptyBoundConversionExists {m} (w a z c L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (emptyBoundConversionExistsSentence w a z c L)) := ZFReplay.replay (emptyBoundConversionExists_kernel_certificate w a z c L)

def modeThreeWholeSubstitutionIffSentence {m} (w mode depth b a c L n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 3 mode).imp ((OriginalTermTraceSyntax.metadata w depth L).imp ((FormulaCodeSyntax.formulaCode w n b a).imp ((SyntaxFreeSubstSyntax.termList w a c L).imp (((OriginalTransformRowSyntax.run 3 w mode depth L n q).iff (SyntaxFormulaFreeSubstSyntax.substituted w b a c L n q)))))))).close

theorem source_modeThreeWholeSubstitutionIff {m} (w mode depth b a c L n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeThreeWholeSubstitutionIffSentence w mode depth b a c L n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxFreeSubstSyntax.termList w a c L) (Context.add (FormulaCodeSyntax.formulaCode w n b a) (Context.add (OriginalTermTraceSyntax.metadata w depth L) (Context.add (SyntaxNumeralSyntax.numeral 3 mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 3 mode) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (OriginalTermTraceSyntax.metadata w depth L) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (FormulaCodeSyntax.formulaCode w n b a) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (SyntaxFreeSubstSyntax.termList w a c L) := .hyp (Or.inl rfl)
  exact OriginalFreeSubstFormulaRun.from_list_iff hZ w mode depth b a c L n q h0 h1 h2 h3 h4

theorem modeThreeWholeSubstitutionIff_kernel_certificate {m} (w mode depth b a c L n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeThreeWholeSubstitutionIffSentence w mode depth b a c L n q)) := TheoryTransport.sentence (source_modeThreeWholeSubstitutionIff w mode depth b a c L n q)

theorem native_modeThreeWholeSubstitutionIff {m} (w mode depth b a c L n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeThreeWholeSubstitutionIffSentence w mode depth b a c L n q)) := ZFReplay.replay (modeThreeWholeSubstitutionIff_kernel_certificate w mode depth b a c L n q)

def modeThreeWholeProgramIffSentence {m} (w mode depth b a c L n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 3 mode).imp ((OriginalTermTraceSyntax.metadata w depth L).imp ((FormulaCodeSyntax.formulaCode w n b a).imp ((SyntaxFreeSubstSyntax.termList w a c L).imp (((OriginalTransformRowSyntax.run 3 w mode depth L n q).iff (FreeSubstProgramSyntax.executed w b a c L n q)))))))).close

theorem source_modeThreeWholeProgramIff {m} (w mode depth b a c L n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeThreeWholeProgramIffSentence w mode depth b a c L n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxFreeSubstSyntax.termList w a c L) (Context.add (FormulaCodeSyntax.formulaCode w n b a) (Context.add (OriginalTermTraceSyntax.metadata w depth L) (Context.add (SyntaxNumeralSyntax.numeral 3 mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 3 mode) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (OriginalTermTraceSyntax.metadata w depth L) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (FormulaCodeSyntax.formulaCode w n b a) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (SyntaxFreeSubstSyntax.termList w a c L) := .hyp (Or.inl rfl)
  exact OriginalFreeSubstFormulaRun.program_iff hZ w mode depth b a c L n q h0 h1 h2 h3 h4

theorem modeThreeWholeProgramIff_kernel_certificate {m} (w mode depth b a c L n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeThreeWholeProgramIffSentence w mode depth b a c L n q)) := TheoryTransport.sentence (source_modeThreeWholeProgramIff w mode depth b a c L n q)

theorem native_modeThreeWholeProgramIff {m} (w mode depth b a c L n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeThreeWholeProgramIffSentence w mode depth b a c L n q)) := ZFReplay.replay (modeThreeWholeProgramIff_kernel_certificate w mode depth b a c L n q)

def modeThreeEmptyBoundArgumentsIffSentence {m} (w mode depth b a z c L n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 3 mode).imp ((OriginalTermTraceSyntax.metadata w depth L).imp ((FormulaCodeSyntax.formulaCode w n b a).imp ((empty z).imp ((SyntaxMixedImageCodeSyntax.termList w a z c L).imp (((OriginalTransformRowSyntax.run 3 w mode depth L n q).iff (FreeSubstProgramSyntax.executed w b a c L n q))))))))).close

theorem source_modeThreeEmptyBoundArgumentsIff {m} (w mode depth b a z c L n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeThreeEmptyBoundArgumentsIffSentence w mode depth b a z c L n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMixedImageCodeSyntax.termList w a z c L) (Context.add (empty z) (Context.add (FormulaCodeSyntax.formulaCode w n b a) (Context.add (OriginalTermTraceSyntax.metadata w depth L) (Context.add (SyntaxNumeralSyntax.numeral 3 mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 3 mode) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (OriginalTermTraceSyntax.metadata w depth L) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (FormulaCodeSyntax.formulaCode w n b a) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (empty z) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (SyntaxMixedImageCodeSyntax.termList w a z c L) := .hyp (Or.inl rfl)
  exact OriginalFreeSubstFormulaRun.empty_bound_arguments_iff hZ w mode depth b a z c L n q h0 h1 h2 h3 h4 h5

theorem modeThreeEmptyBoundArgumentsIff_kernel_certificate {m} (w mode depth b a z c L n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeThreeEmptyBoundArgumentsIffSentence w mode depth b a z c L n q)) := TheoryTransport.sentence (source_modeThreeEmptyBoundArgumentsIff w mode depth b a z c L n q)

theorem native_modeThreeEmptyBoundArgumentsIff {m} (w mode depth b a z c L n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeThreeEmptyBoundArgumentsIffSentence w mode depth b a z c L n q)) := ZFReplay.replay (modeThreeEmptyBoundArgumentsIff_kernel_certificate w mode depth b a z c L n q)

def modeThreeOutputTypeSentence {m} (w mode depth b a c L n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 3 mode).imp ((OriginalTermTraceSyntax.metadata w depth L).imp ((FormulaCodeSyntax.formulaCode w n b a).imp ((SyntaxFreeSubstSyntax.termList w a c L).imp ((OriginalTransformRowSyntax.run 3 w mode depth L n q).imp ((FormulaCodeSyntax.formulaCode w q b c)))))))).close

theorem source_modeThreeOutputType {m} (w mode depth b a c L n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeThreeOutputTypeSentence w mode depth b a c L n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (OriginalTransformRowSyntax.run 3 w mode depth L n q) (Context.add (SyntaxFreeSubstSyntax.termList w a c L) (Context.add (FormulaCodeSyntax.formulaCode w n b a) (Context.add (OriginalTermTraceSyntax.metadata w depth L) (Context.add (SyntaxNumeralSyntax.numeral 3 mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 3 mode) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (OriginalTermTraceSyntax.metadata w depth L) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (FormulaCodeSyntax.formulaCode w n b a) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (SyntaxFreeSubstSyntax.termList w a c L) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (OriginalTransformRowSyntax.run 3 w mode depth L n q) := .hyp (Or.inl rfl)
  exact OriginalFreeSubstFormulaRun.output_type hZ w mode depth b a c L n q h0 h1 h2 h3 h4 h5

theorem modeThreeOutputType_kernel_certificate {m} (w mode depth b a c L n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeThreeOutputTypeSentence w mode depth b a c L n q)) := TheoryTransport.sentence (source_modeThreeOutputType w mode depth b a c L n q)

theorem native_modeThreeOutputType {m} (w mode depth b a c L n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeThreeOutputTypeSentence w mode depth b a c L n q)) := ZFReplay.replay (modeThreeOutputType_kernel_certificate w mode depth b a c L n q)

def modeThreeOutputUniqueSentence {m} (w mode depth b a c L n q v : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 3 mode).imp ((OriginalTermTraceSyntax.metadata w depth L).imp ((FormulaCodeSyntax.formulaCode w n b a).imp ((SyntaxFreeSubstSyntax.termList w a c L).imp ((OriginalTransformRowSyntax.run 3 w mode depth L n q).imp ((OriginalTransformRowSyntax.run 3 w mode depth L n v).imp ((Formula.equal q v))))))))).close

theorem source_modeThreeOutputUnique {m} (w mode depth b a c L n q v : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeThreeOutputUniqueSentence w mode depth b a c L n q v) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (OriginalTransformRowSyntax.run 3 w mode depth L n v) (Context.add (OriginalTransformRowSyntax.run 3 w mode depth L n q) (Context.add (SyntaxFreeSubstSyntax.termList w a c L) (Context.add (FormulaCodeSyntax.formulaCode w n b a) (Context.add (OriginalTermTraceSyntax.metadata w depth L) (Context.add (SyntaxNumeralSyntax.numeral 3 mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))
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
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 3 mode) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h2 : Derives Δ (OriginalTermTraceSyntax.metadata w depth L) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h3 : Derives Δ (FormulaCodeSyntax.formulaCode w n b a) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : Derives Δ (SyntaxFreeSubstSyntax.termList w a c L) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h5 : Derives Δ (OriginalTransformRowSyntax.run 3 w mode depth L n q) := .hyp (Or.inr (Or.inl rfl))
  have h6 : Derives Δ (OriginalTransformRowSyntax.run 3 w mode depth L n v) := .hyp (Or.inl rfl)
  exact OriginalFreeSubstFormulaRun.unique hZ w mode depth b a c L n q v h0 h1 h2 h3 h4 h5 h6

theorem modeThreeOutputUnique_kernel_certificate {m} (w mode depth b a c L n q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeThreeOutputUniqueSentence w mode depth b a c L n q v)) := TheoryTransport.sentence (source_modeThreeOutputUnique w mode depth b a c L n q v)

theorem native_modeThreeOutputUnique {m} (w mode depth b a c L n q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeThreeOutputUniqueSentence w mode depth b a c L n q v)) := ZFReplay.replay (modeThreeOutputUnique_kernel_certificate w mode depth b a c L n q v)

def modeThreeActualOutputSentence {m} (w mode depth b a c L n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 3 mode).imp ((OriginalTermTraceSyntax.metadata w depth L).imp ((FormulaCodeSyntax.formulaCode w n b a).imp ((SyntaxFreeSubstSyntax.termList w a c L).imp ((.ex (OriginalTransformRowSyntax.run 3 w.castSucc mode.castSucc depth.castSucc L.castSucc n.castSucc (Fin.last m))))))))).close

theorem source_modeThreeActualOutput {m} (w mode depth b a c L n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeThreeActualOutputSentence w mode depth b a c L n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxFreeSubstSyntax.termList w a c L) (Context.add (FormulaCodeSyntax.formulaCode w n b a) (Context.add (OriginalTermTraceSyntax.metadata w depth L) (Context.add (SyntaxNumeralSyntax.numeral 3 mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 3 mode) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (OriginalTermTraceSyntax.metadata w depth L) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (FormulaCodeSyntax.formulaCode w n b a) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (SyntaxFreeSubstSyntax.termList w a c L) := .hyp (Or.inl rfl)
  exact OriginalFreeSubstFormulaRun.actual_output hZ w mode depth b a c L n h0 h1 h2 h3 h4

theorem modeThreeActualOutput_kernel_certificate {m} (w mode depth b a c L n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeThreeActualOutputSentence w mode depth b a c L n)) := TheoryTransport.sentence (source_modeThreeActualOutput w mode depth b a c L n)

theorem native_modeThreeActualOutput {m} (w mode depth b a c L n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeThreeActualOutputSentence w mode depth b a c L n)) := ZFReplay.replay (modeThreeActualOutput_kernel_certificate w mode depth b a c L n)

end PPAC.Migration.Internal.ObjectOriginalFreeSubstFormula
