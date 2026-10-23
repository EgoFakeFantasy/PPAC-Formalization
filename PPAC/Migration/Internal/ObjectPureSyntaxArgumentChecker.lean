import PPAC.Migration.Internal.PureArgumentsModeThree

/-! 全内部参数列对象归纳、查询双条件及原核证书；最终Proof／Con未完成。 -/
namespace PPAC.Migration.Internal.ObjectPureSyntaxArgumentChecker
open Source SourceAlgebra SourceLogic OmegaSyntax
open YesMetaZFC.Automation.ObjectHorn (Rule)

def pureConsQueryCompleteSentence {m} (w b f ell k h t n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxTermSyntax.term w b f h).imp ((SyntaxMixedImageCodeSyntax.termList w ell b f t).imp ((PureSyntaxTrace.arguments w b f ell t).imp ((StructuralListSyntax.consCode w h t n).imp ((successor k ell).imp ((PureSyntaxTrace.arguments w b f k n)))))))).close

theorem source_pureConsQueryComplete {m} (w b f ell k h t n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (pureConsQueryCompleteSentence w b f ell k h t n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor k ell) (Context.add (StructuralListSyntax.consCode w h t n) (Context.add (PureSyntaxTrace.arguments w b f ell t) (Context.add (SyntaxMixedImageCodeSyntax.termList w ell b f t) (Context.add (SyntaxTermSyntax.term w b f h) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (SyntaxTermSyntax.term w b f h) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (SyntaxMixedImageCodeSyntax.termList w ell b f t) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (PureSyntaxTrace.arguments w b f ell t) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (StructuralListSyntax.consCode w h t n) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (successor k ell) := .hyp (Or.inl rfl)
  exact PureSyntaxConsComplete.checked_cons hZ w b f ell k h t n h0 h1 h2 h3 h4 h5

theorem pureConsQueryComplete_kernel_certificate {m} (w b f ell k h t n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (pureConsQueryCompleteSentence w b f ell k h t n)) := TheoryTransport.sentence (source_pureConsQueryComplete w b f ell k h t n)

theorem native_pureConsQueryComplete {m} (w b f ell k h t n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (pureConsQueryCompleteSentence w b f ell k h t n)) := ZFReplay.replay (pureConsQueryComplete_kernel_certificate w b f ell k h t n)

def pureConsApplicationFromInductionSoundSentence {m} (w b f k n r R : Fin m) : Source.Sentence := ((omega w).imp ((PureSyntaxListInductionSyntax.allIH w n).imp ((RestrictionSyntax.subset R w).imp ((PureSyntaxTrace.closed w R).imp ((PureSyntaxTrace.argumentRow w b f k n r).imp ((HornApplicationSyntax.application YesMetaZFC.Automation.ObjectTermSyntax.consRule w r R).imp ((SyntaxMixedImageCodeSyntax.termList w k b f n)))))))).close

theorem source_pureConsApplicationFromInductionSound {m} (w b f k n r R : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (pureConsApplicationFromInductionSoundSentence w b f k n r R) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornApplicationSyntax.application YesMetaZFC.Automation.ObjectTermSyntax.consRule w r R) (Context.add (PureSyntaxTrace.argumentRow w b f k n r) (Context.add (PureSyntaxTrace.closed w R) (Context.add (RestrictionSyntax.subset R w) (Context.add (PureSyntaxListInductionSyntax.allIH w n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (PureSyntaxListInductionSyntax.allIH w n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (RestrictionSyntax.subset R w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (PureSyntaxTrace.closed w R) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (PureSyntaxTrace.argumentRow w b f k n r) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (HornApplicationSyntax.application YesMetaZFC.Automation.ObjectTermSyntax.consRule w r R) := .hyp (Or.inl rfl)
  exact PureSyntaxConsSound.application_sound hZ w b f k n r R h0 h1 h2 h3 h4 h5

theorem pureConsApplicationFromInductionSound_kernel_certificate {m} (w b f k n r R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (pureConsApplicationFromInductionSoundSentence w b f k n r R)) := TheoryTransport.sentence (source_pureConsApplicationFromInductionSound w b f k n r R)

theorem native_pureConsApplicationFromInductionSound {m} (w b f k n r R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (pureConsApplicationFromInductionSoundSentence w b f k n r R)) := ZFReplay.replay (pureConsApplicationFromInductionSound_kernel_certificate w b f k n r R)

def pureArgumentsFromInductionIffSentence {m} (w b f k n : Fin m) : Source.Sentence := ((omega w).imp ((PureSyntaxListInductionSyntax.allIH w n).imp (((PureSyntaxTrace.arguments w b f k n).iff (SyntaxMixedImageCodeSyntax.termList w k b f n))))).close

theorem source_pureArgumentsFromInductionIff {m} (w b f k n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (pureArgumentsFromInductionIffSentence w b f k n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PureSyntaxListInductionSyntax.allIH w n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PureSyntaxListInductionSyntax.allIH w n) := .hyp (Or.inl rfl)
  exact PureSyntaxArgumentComplete.checked_iff_from_induction hZ w b f k n h0 h1

theorem pureArgumentsFromInductionIff_kernel_certificate {m} (w b f k n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (pureArgumentsFromInductionIffSentence w b f k n)) := TheoryTransport.sentence (source_pureArgumentsFromInductionIff w b f k n)

theorem native_pureArgumentsFromInductionIff {m} (w b f k n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (pureArgumentsFromInductionIffSentence w b f k n)) := ZFReplay.replay (pureArgumentsFromInductionIff_kernel_certificate w b f k n)

def pureAllArgumentsCorrectSentence {m} (w : Fin m) : Source.Sentence := ((omega w).imp ((Source.Formula.all (PureSyntaxListInductionSyntax.correct w.castSucc (Fin.last m))))).close

theorem source_pureAllArgumentsCorrect {m} (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (pureAllArgumentsCorrectSentence w) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact PureSyntaxArgumentInduction.all_correct hZ w h0

theorem pureAllArgumentsCorrect_kernel_certificate {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (pureAllArgumentsCorrectSentence w)) := TheoryTransport.sentence (source_pureAllArgumentsCorrect w)

theorem native_pureAllArgumentsCorrect {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (pureAllArgumentsCorrectSentence w)) := ZFReplay.replay (pureAllArgumentsCorrect_kernel_certificate w)

def pureArgumentsInductionDischargedSentence {m} (w n : Fin m) : Source.Sentence := ((omega w).imp ((PureSyntaxListInductionSyntax.allIH w n))).close

theorem source_pureArgumentsInductionDischarged {m} (w n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (pureArgumentsInductionDischargedSentence w n) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact PureSyntaxArgumentInduction.all_ih hZ w n h0

theorem pureArgumentsInductionDischarged_kernel_certificate {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (pureArgumentsInductionDischargedSentence w n)) := TheoryTransport.sentence (source_pureArgumentsInductionDischarged w n)

theorem native_pureArgumentsInductionDischarged {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (pureArgumentsInductionDischargedSentence w n)) := ZFReplay.replay (pureArgumentsInductionDischarged_kernel_certificate w n)

def pureArgumentsQueryIffSentence {m} (w b f k n : Fin m) : Source.Sentence := ((omega w).imp (((PureSyntaxTrace.arguments w b f k n).iff (SyntaxMixedImageCodeSyntax.termList w k b f n)))).close

theorem source_pureArgumentsQueryIff {m} (w b f k n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (pureArgumentsQueryIffSentence w b f k n) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact PureSyntaxArgumentInduction.checked_iff hZ w b f k n h0

theorem pureArgumentsQueryIff_kernel_certificate {m} (w b f k n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (pureArgumentsQueryIffSentence w b f k n)) := TheoryTransport.sentence (source_pureArgumentsQueryIff w b f k n)

theorem native_pureArgumentsQueryIff {m} (w b f k n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (pureArgumentsQueryIffSentence w b f k n)) := ZFReplay.replay (pureArgumentsQueryIff_kernel_certificate w b f k n)

def pureArgumentsQuerySoundSentence {m} (w b f k n : Fin m) : Source.Sentence := ((omega w).imp ((PureSyntaxTrace.arguments w b f k n).imp ((SyntaxMixedImageCodeSyntax.termList w k b f n)))).close

theorem source_pureArgumentsQuerySound {m} (w b f k n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (pureArgumentsQuerySoundSentence w b f k n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PureSyntaxTrace.arguments w b f k n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PureSyntaxTrace.arguments w b f k n) := .hyp (Or.inl rfl)
  exact PureSyntaxArgumentInduction.checked_sound hZ w b f k n h0 h1

theorem pureArgumentsQuerySound_kernel_certificate {m} (w b f k n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (pureArgumentsQuerySoundSentence w b f k n)) := TheoryTransport.sentence (source_pureArgumentsQuerySound w b f k n)

theorem native_pureArgumentsQuerySound {m} (w b f k n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (pureArgumentsQuerySoundSentence w b f k n)) := ZFReplay.replay (pureArgumentsQuerySound_kernel_certificate w b f k n)

def pureArgumentsQueryCompleteSentence {m} (w b f k n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMixedImageCodeSyntax.termList w k b f n).imp ((PureSyntaxTrace.arguments w b f k n)))).close

theorem source_pureArgumentsQueryComplete {m} (w b f k n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (pureArgumentsQueryCompleteSentence w b f k n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMixedImageCodeSyntax.termList w k b f n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxMixedImageCodeSyntax.termList w k b f n) := .hyp (Or.inl rfl)
  exact PureSyntaxArgumentInduction.checked_complete hZ w b f k n h0 h1

theorem pureArgumentsQueryComplete_kernel_certificate {m} (w b f k n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (pureArgumentsQueryCompleteSentence w b f k n)) := TheoryTransport.sentence (source_pureArgumentsQueryComplete w b f k n)

theorem native_pureArgumentsQueryComplete {m} (w b f k n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (pureArgumentsQueryCompleteSentence w b f k n)) := ZFReplay.replay (pureArgumentsQueryComplete_kernel_certificate w b f k n)

def pureEmptyBoundArgumentsQueryIffSentence {m} (w a z c L : Fin m) : Source.Sentence := ((omega w).imp ((empty z).imp (((PureSyntaxTrace.arguments w z c a L).iff (SyntaxFreeSubstSyntax.termList w a c L))))).close

theorem source_pureEmptyBoundArgumentsQueryIff {m} (w a z c L : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (pureEmptyBoundArgumentsQueryIffSentence w a z c L) := by
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
  exact PureArgumentsModeThree.empty_bound_query_iff hZ w a z c L h0 h1

theorem pureEmptyBoundArgumentsQueryIff_kernel_certificate {m} (w a z c L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (pureEmptyBoundArgumentsQueryIffSentence w a z c L)) := TheoryTransport.sentence (source_pureEmptyBoundArgumentsQueryIff w a z c L)

theorem native_pureEmptyBoundArgumentsQueryIff {m} (w a z c L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (pureEmptyBoundArgumentsQueryIffSentence w a z c L)) := ZFReplay.replay (pureEmptyBoundArgumentsQueryIff_kernel_certificate w a z c L)

def pureModeThreeFromArgumentsQueryIffSentence {m} (w mode depth b a z c L n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 3 mode).imp ((OriginalTermTraceSyntax.metadata w depth L).imp ((FormulaCodeSyntax.formulaCode w n b a).imp ((empty z).imp ((PureSyntaxTrace.arguments w z c a L).imp (((OriginalTransformRowSyntax.run 3 w mode depth L n q).iff (FreeSubstProgramSyntax.executed w b a c L n q))))))))).close

theorem source_pureModeThreeFromArgumentsQueryIff {m} (w mode depth b a z c L n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (pureModeThreeFromArgumentsQueryIffSentence w mode depth b a z c L n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PureSyntaxTrace.arguments w z c a L) (Context.add (empty z) (Context.add (FormulaCodeSyntax.formulaCode w n b a) (Context.add (OriginalTermTraceSyntax.metadata w depth L) (Context.add (SyntaxNumeralSyntax.numeral 3 mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
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
  have h5 : Derives Δ (PureSyntaxTrace.arguments w z c a L) := .hyp (Or.inl rfl)
  exact PureArgumentsModeThree.mode_three_iff hZ w mode depth b a z c L n q h0 h1 h2 h3 h4 h5

theorem pureModeThreeFromArgumentsQueryIff_kernel_certificate {m} (w mode depth b a z c L n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (pureModeThreeFromArgumentsQueryIffSentence w mode depth b a z c L n q)) := TheoryTransport.sentence (source_pureModeThreeFromArgumentsQueryIff w mode depth b a z c L n q)

theorem native_pureModeThreeFromArgumentsQueryIff {m} (w mode depth b a z c L n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (pureModeThreeFromArgumentsQueryIffSentence w mode depth b a z c L n q)) := ZFReplay.replay (pureModeThreeFromArgumentsQueryIff_kernel_certificate w mode depth b a z c L n q)

end PPAC.Migration.Internal.ObjectPureSyntaxArgumentChecker
