import PPAC.Migration.Internal.PureSyntaxFormulaInduction

/-! 纯十五规则全部内部公式查询双条件、原ZF集合归纳和无IH原核闭句。 -/
namespace PPAC.Migration.Internal.ObjectPureSyntaxFormulaChecker
open Source SourceAlgebra SourceLogic OmegaSyntax
open YesMetaZFC.Automation.ObjectHorn (Rule)

def formulaFromInductionIffSentence {m} (w b f n : Fin m) : Source.Sentence := ((omega w).imp ((PureSyntaxFormulaInductionSyntax.allIH w n).imp (((PureSyntaxTrace.formula w b f n).iff (FormulaCodeSyntax.formulaCode w n b f))))).close

theorem source_formulaFromInductionIff {m} (w b f n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (formulaFromInductionIffSentence w b f n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PureSyntaxFormulaInductionSyntax.allIH w n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PureSyntaxFormulaInductionSyntax.allIH w n) := .hyp (Or.inl rfl)
  exact PureSyntaxFormulaComplete.checked_iff_from_induction hZ w b f n h0 h1

theorem formulaFromInductionIff_kernel_certificate {m} (w b f n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (formulaFromInductionIffSentence w b f n)) := TheoryTransport.sentence (source_formulaFromInductionIff w b f n)

theorem native_formulaFromInductionIff {m} (w b f n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (formulaFromInductionIffSentence w b f n)) := ZFReplay.replay (formulaFromInductionIff_kernel_certificate w b f n)

def formulaAllInternalCorrectSentence {m} (w : Fin m) : Source.Sentence := ((omega w).imp ((.all (PureSyntaxFormulaInductionSyntax.correct w.castSucc (Fin.last m))))).close

theorem source_formulaAllInternalCorrect {m} (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (formulaAllInternalCorrectSentence w) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact PureSyntaxFormulaInduction.all_correct hZ w h0

theorem formulaAllInternalCorrect_kernel_certificate {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (formulaAllInternalCorrectSentence w)) := TheoryTransport.sentence (source_formulaAllInternalCorrect w)

theorem native_formulaAllInternalCorrect {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (formulaAllInternalCorrectSentence w)) := ZFReplay.replay (formulaAllInternalCorrect_kernel_certificate w)

def formulaCorrectAtRootSentence {m} (w n : Fin m) : Source.Sentence := ((omega w).imp ((PureSyntaxFormulaInductionSyntax.correct w n))).close

theorem source_formulaCorrectAtRoot {m} (w n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (formulaCorrectAtRootSentence w n) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact PureSyntaxFormulaInduction.at_root hZ w n h0

theorem formulaCorrectAtRoot_kernel_certificate {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (formulaCorrectAtRootSentence w n)) := TheoryTransport.sentence (source_formulaCorrectAtRoot w n)

theorem native_formulaCorrectAtRoot {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (formulaCorrectAtRootSentence w n)) := ZFReplay.replay (formulaCorrectAtRoot_kernel_certificate w n)

def formulaInductionDischargedSentence {m} (w n : Fin m) : Source.Sentence := ((omega w).imp ((PureSyntaxFormulaInductionSyntax.allIH w n))).close

theorem source_formulaInductionDischarged {m} (w n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (formulaInductionDischargedSentence w n) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact PureSyntaxFormulaInduction.all_ih hZ w n h0

theorem formulaInductionDischarged_kernel_certificate {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (formulaInductionDischargedSentence w n)) := TheoryTransport.sentence (source_formulaInductionDischarged w n)

theorem native_formulaInductionDischarged {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (formulaInductionDischargedSentence w n)) := ZFReplay.replay (formulaInductionDischarged_kernel_certificate w n)

def formulaQueryIffSentence {m} (w b f n : Fin m) : Source.Sentence := ((omega w).imp (((PureSyntaxTrace.formula w b f n).iff (FormulaCodeSyntax.formulaCode w n b f)))).close

theorem source_formulaQueryIff {m} (w b f n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (formulaQueryIffSentence w b f n) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact PureSyntaxFormulaInduction.checked_iff hZ w b f n h0

theorem formulaQueryIff_kernel_certificate {m} (w b f n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (formulaQueryIffSentence w b f n)) := TheoryTransport.sentence (source_formulaQueryIff w b f n)

theorem native_formulaQueryIff {m} (w b f n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (formulaQueryIffSentence w b f n)) := ZFReplay.replay (formulaQueryIff_kernel_certificate w b f n)

def formulaQuerySoundSentence {m} (w b f n : Fin m) : Source.Sentence := ((omega w).imp ((PureSyntaxTrace.formula w b f n).imp ((FormulaCodeSyntax.formulaCode w n b f)))).close

theorem source_formulaQuerySound {m} (w b f n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (formulaQuerySoundSentence w b f n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PureSyntaxTrace.formula w b f n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PureSyntaxTrace.formula w b f n) := .hyp (Or.inl rfl)
  exact PureSyntaxFormulaInduction.checked_sound hZ w b f n h0 h1

theorem formulaQuerySound_kernel_certificate {m} (w b f n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (formulaQuerySoundSentence w b f n)) := TheoryTransport.sentence (source_formulaQuerySound w b f n)

theorem native_formulaQuerySound {m} (w b f n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (formulaQuerySoundSentence w b f n)) := ZFReplay.replay (formulaQuerySound_kernel_certificate w b f n)

def formulaQueryCompleteSentence {m} (w b f n : Fin m) : Source.Sentence := ((omega w).imp ((FormulaCodeSyntax.formulaCode w n b f).imp ((PureSyntaxTrace.formula w b f n)))).close

theorem source_formulaQueryComplete {m} (w b f n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (formulaQueryCompleteSentence w b f n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (FormulaCodeSyntax.formulaCode w n b f) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (FormulaCodeSyntax.formulaCode w n b f) := .hyp (Or.inl rfl)
  exact PureSyntaxFormulaInduction.checked_complete hZ w b f n h0 h1

theorem formulaQueryComplete_kernel_certificate {m} (w b f n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (formulaQueryCompleteSentence w b f n)) := TheoryTransport.sentence (source_formulaQueryComplete w b f n)

theorem native_formulaQueryComplete {m} (w b f n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (formulaQueryCompleteSentence w b f n)) := ZFReplay.replay (formulaQueryComplete_kernel_certificate w b f n)

def fullSyntaxTypingIffSentence {m} (w b f k n : Fin m) : Source.Sentence := ((omega w).imp ((((PureSyntaxTrace.term w b f n).iff (SyntaxTermSyntax.term w b f n)).conj (((PureSyntaxTrace.arguments w b f k n).iff (SyntaxMixedImageCodeSyntax.termList w k b f n)).conj ((PureSyntaxTrace.formula w b f n).iff (FormulaCodeSyntax.formulaCode w n b f)))))).close

theorem source_fullSyntaxTypingIff {m} (w b f k n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (fullSyntaxTypingIffSentence w b f k n) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact PureSyntaxFormulaInduction.full_typing hZ w b f k n h0

theorem fullSyntaxTypingIff_kernel_certificate {m} (w b f k n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (fullSyntaxTypingIffSentence w b f k n)) := TheoryTransport.sentence (source_fullSyntaxTypingIff w b f k n)

theorem native_fullSyntaxTypingIff {m} (w b f k n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (fullSyntaxTypingIffSentence w b f k n)) := ZFReplay.replay (fullSyntaxTypingIff_kernel_certificate w b f k n)

end PPAC.Migration.Internal.ObjectPureSyntaxFormulaChecker
