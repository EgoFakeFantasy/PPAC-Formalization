import PPAC.Migration.Internal.AbstractTopArgumentOperation

/-! 实际零深度抽象参数列及小模式归纳的原核闭句。 -/
namespace PPAC.Migration.Internal.ObjectAbstractTopArguments
open Source SourceAlgebra SourceLogic OmegaSyntax

def smallModeArgumentActualFiberSentence {m} (modeIndex : Fin 4) (w mode depth parameter a b c d n k : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral modeIndex.val mode).imp ((Formula.mem depth w).imp ((Formula.mem parameter w).imp ((SyntaxTermSyntax.contexts w c d).imp ((OriginalNumericTermValueSyntax.promise w mode depth parameter a b c d).imp ((SyntaxMixedImageCodeSyntax.termList w k a b n).imp ((OriginalArgumentValueSyntax.fiber w mode depth parameter k c d n))))))))).close

theorem source_smallModeArgumentActualFiber {m} (modeIndex : Fin 4) (w mode depth parameter a b c d n k : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (smallModeArgumentActualFiberSentence modeIndex w mode depth parameter a b c d n k) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMixedImageCodeSyntax.termList w k a b n) (Context.add (OriginalNumericTermValueSyntax.promise w mode depth parameter a b c d) (Context.add (SyntaxTermSyntax.contexts w c d) (Context.add (Formula.mem parameter w) (Context.add (Formula.mem depth w) (Context.add (SyntaxNumeralSyntax.numeral modeIndex.val mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))
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
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral modeIndex.val mode) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h2 : Derives Δ (Formula.mem depth w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h3 : Derives Δ (Formula.mem parameter w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : Derives Δ (SyntaxTermSyntax.contexts w c d) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h5 : Derives Δ (OriginalNumericTermValueSyntax.promise w mode depth parameter a b c d) := .hyp (Or.inr (Or.inl rfl))
  have h6 : Derives Δ (SyntaxMixedImageCodeSyntax.termList w k a b n) := .hyp (Or.inl rfl)
  exact SmallModeArgumentValueInduction.actual_fiber hZ modeIndex.val modeIndex.isLt w mode depth parameter a b c d n k h0 h1 h2 h3 h4 h5 h6

theorem smallModeArgumentActualFiber_kernel_certificate {m} (modeIndex : Fin 4) (w mode depth parameter a b c d n k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (smallModeArgumentActualFiberSentence modeIndex w mode depth parameter a b c d n k)) := TheoryTransport.sentence (source_smallModeArgumentActualFiber modeIndex w mode depth parameter a b c d n k)

theorem native_smallModeArgumentActualFiber {m} (modeIndex : Fin 4) (w mode depth parameter a b c d n k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (smallModeArgumentActualFiberSentence modeIndex w mode depth parameter a b c d n k)) := ZFReplay.replay (smallModeArgumentActualFiber_kernel_certificate modeIndex w mode depth parameter a b c d n k)

def smallModeArgumentActualFieldsSentence {m} (modeIndex : Fin 4) (w mode depth parameter a b n k q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral modeIndex.val mode).imp ((Formula.mem depth w).imp ((Formula.mem parameter w).imp ((SyntaxMixedImageCodeSyntax.termList w k a b n).imp ((OriginalTransformRowSyntax.run 2 w mode depth parameter n q).imp ((OriginalArgumentFieldSyntax.fields w mode depth parameter k n q)))))))).close

theorem source_smallModeArgumentActualFields {m} (modeIndex : Fin 4) (w mode depth parameter a b n k q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (smallModeArgumentActualFieldsSentence modeIndex w mode depth parameter a b n k q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (OriginalTransformRowSyntax.run 2 w mode depth parameter n q) (Context.add (SyntaxMixedImageCodeSyntax.termList w k a b n) (Context.add (Formula.mem parameter w) (Context.add (Formula.mem depth w) (Context.add (SyntaxNumeralSyntax.numeral modeIndex.val mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral modeIndex.val mode) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (Formula.mem depth w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (Formula.mem parameter w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (SyntaxMixedImageCodeSyntax.termList w k a b n) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (OriginalTransformRowSyntax.run 2 w mode depth parameter n q) := .hyp (Or.inl rfl)
  exact SmallModeArgumentFieldInduction.actual_fields hZ modeIndex.val modeIndex.isLt w mode depth parameter a b n k q h0 h1 h2 h3 h4 h5

theorem smallModeArgumentActualFields_kernel_certificate {m} (modeIndex : Fin 4) (w mode depth parameter a b n k q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (smallModeArgumentActualFieldsSentence modeIndex w mode depth parameter a b n k q)) := TheoryTransport.sentence (source_smallModeArgumentActualFields modeIndex w mode depth parameter a b n k q)

theorem native_smallModeArgumentActualFields {m} (modeIndex : Fin 4) (w mode depth parameter a b n k q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (smallModeArgumentActualFieldsSentence modeIndex w mode depth parameter a b n k q)) := ZFReplay.replay (smallModeArgumentActualFields_kernel_certificate modeIndex w mode depth parameter a b n k q)

def smallModeArgumentCompleteFieldMapIffSentence {m} (modeIndex : Fin 4) (w mode depth parameter a b c d n k q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral modeIndex.val mode).imp ((Formula.mem depth w).imp ((Formula.mem parameter w).imp ((SyntaxTermSyntax.contexts w c d).imp ((OriginalNumericTermValueSyntax.promise w mode depth parameter a b c d).imp ((SyntaxMixedImageCodeSyntax.termList w k a b n).imp (((OriginalTransformRowSyntax.run 2 w mode depth parameter n q).iff (SmallModeArgumentFieldCompletion.mapped w mode depth parameter k c d n q)))))))))).close

theorem source_smallModeArgumentCompleteFieldMapIff {m} (modeIndex : Fin 4) (w mode depth parameter a b c d n k q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (smallModeArgumentCompleteFieldMapIffSentence modeIndex w mode depth parameter a b c d n k q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMixedImageCodeSyntax.termList w k a b n) (Context.add (OriginalNumericTermValueSyntax.promise w mode depth parameter a b c d) (Context.add (SyntaxTermSyntax.contexts w c d) (Context.add (Formula.mem parameter w) (Context.add (Formula.mem depth w) (Context.add (SyntaxNumeralSyntax.numeral modeIndex.val mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))
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
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral modeIndex.val mode) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h2 : Derives Δ (Formula.mem depth w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h3 : Derives Δ (Formula.mem parameter w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : Derives Δ (SyntaxTermSyntax.contexts w c d) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h5 : Derives Δ (OriginalNumericTermValueSyntax.promise w mode depth parameter a b c d) := .hyp (Or.inr (Or.inl rfl))
  have h6 : Derives Δ (SyntaxMixedImageCodeSyntax.termList w k a b n) := .hyp (Or.inl rfl)
  exact SmallModeArgumentFieldCompletion.run_iff hZ modeIndex.val modeIndex.isLt w mode depth parameter a b c d n k q h0 h1 h2 h3 h4 h5 h6

theorem smallModeArgumentCompleteFieldMapIff_kernel_certificate {m} (modeIndex : Fin 4) (w mode depth parameter a b c d n k q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (smallModeArgumentCompleteFieldMapIffSentence modeIndex w mode depth parameter a b c d n k q)) := TheoryTransport.sentence (source_smallModeArgumentCompleteFieldMapIff modeIndex w mode depth parameter a b c d n k q)

theorem native_smallModeArgumentCompleteFieldMapIff {m} (modeIndex : Fin 4) (w mode depth parameter a b c d n k q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (smallModeArgumentCompleteFieldMapIffSentence modeIndex w mode depth parameter a b c d n k q)) := ZFReplay.replay (smallModeArgumentCompleteFieldMapIff_kernel_certificate modeIndex w mode depth parameter a b c d n k q)

def modeOneActualTermAllOutputsAgreementSentence {m} (w mode z P a b A B R S n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 1 mode).imp ((OriginalTermTraceSyntax.metadata w z P).imp ((empty z).imp ((SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S).imp ((SyntaxTermSyntax.term w a B n).imp ((OriginalNumericTermValueSyntax.agreement w mode z P R S n)))))))).close

theorem source_modeOneActualTermAllOutputsAgreement {m} (w mode z P a b A B R S n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeOneActualTermAllOutputsAgreementSentence w mode z P a b A B R S n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTermSyntax.term w a B n) (Context.add (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S) (Context.add (empty z) (Context.add (OriginalTermTraceSyntax.metadata w z P) (Context.add (SyntaxNumeralSyntax.numeral 1 mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
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
  have h5 : Derives Δ (SyntaxTermSyntax.term w a B n) := .hyp (Or.inl rfl)
  exact AbstractTopTermFiber.agreement hZ w mode z P a b A B R S n h0 h1 h2 h3 h4 h5

theorem modeOneActualTermAllOutputsAgreement_kernel_certificate {m} (w mode z P a b A B R S n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeOneActualTermAllOutputsAgreementSentence w mode z P a b A B R S n)) := TheoryTransport.sentence (source_modeOneActualTermAllOutputsAgreement w mode z P a b A B R S n)

theorem native_modeOneActualTermAllOutputsAgreement {m} (w mode z P a b A B R S n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeOneActualTermAllOutputsAgreementSentence w mode z P a b A B R S n)) := ZFReplay.replay (modeOneActualTermAllOutputsAgreement_kernel_certificate w mode z P a b A B R S n)

def modeOneActualTermUniqueTypedFiberSentence {m} (w mode z P a b A B R S n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 1 mode).imp ((OriginalTermTraceSyntax.metadata w z P).imp ((empty z).imp ((SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S).imp ((SyntaxTermSyntax.term w a B n).imp ((OriginalNumericTermValueSyntax.fiber w mode z P A b n)))))))).close

theorem source_modeOneActualTermUniqueTypedFiber {m} (w mode z P a b A B R S n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeOneActualTermUniqueTypedFiberSentence w mode z P a b A B R S n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTermSyntax.term w a B n) (Context.add (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S) (Context.add (empty z) (Context.add (OriginalTermTraceSyntax.metadata w z P) (Context.add (SyntaxNumeralSyntax.numeral 1 mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
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
  have h5 : Derives Δ (SyntaxTermSyntax.term w a B n) := .hyp (Or.inl rfl)
  exact AbstractTopTermFiber.fiber hZ w mode z P a b A B R S n h0 h1 h2 h3 h4 h5

theorem modeOneActualTermUniqueTypedFiber_kernel_certificate {m} (w mode z P a b A B R S n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeOneActualTermUniqueTypedFiberSentence w mode z P a b A B R S n)) := TheoryTransport.sentence (source_modeOneActualTermUniqueTypedFiber w mode z P a b A B R S n)

theorem native_modeOneActualTermUniqueTypedFiber {m} (w mode z P a b A B R S n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeOneActualTermUniqueTypedFiberSentence w mode z P a b A B R S n)) := ZFReplay.replay (modeOneActualTermUniqueTypedFiber_kernel_certificate w mode z P a b A B R S n)

def modeOneActualTermPromiseDischargedSentence {m} (w mode z P a b A B R S : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 1 mode).imp ((OriginalTermTraceSyntax.metadata w z P).imp ((empty z).imp ((SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S).imp ((OriginalNumericTermValueSyntax.promise w mode z P a B A b))))))).close

theorem source_modeOneActualTermPromiseDischarged {m} (w mode z P a b A B R S : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeOneActualTermPromiseDischargedSentence w mode z P a b A B R S) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S) (Context.add (empty z) (Context.add (OriginalTermTraceSyntax.metadata w z P) (Context.add (SyntaxNumeralSyntax.numeral 1 mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 1 mode) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (OriginalTermTraceSyntax.metadata w z P) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (empty z) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S) := .hyp (Or.inl rfl)
  exact AbstractTopTermFiber.promise hZ w mode z P a b A B R S h0 h1 h2 h3 h4

theorem modeOneActualTermPromiseDischarged_kernel_certificate {m} (w mode z P a b A B R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeOneActualTermPromiseDischargedSentence w mode z P a b A B R S)) := TheoryTransport.sentence (source_modeOneActualTermPromiseDischarged w mode z P a b A B R S)

theorem native_modeOneActualTermPromiseDischarged {m} (w mode z P a b A B R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeOneActualTermPromiseDischargedSentence w mode z P a b A B R S)) := ZFReplay.replay (modeOneActualTermPromiseDischarged_kernel_certificate w mode z P a b A B R S)

def modeOneZeroDepthActualArgumentFieldsIffSentence {m} (w mode z P a b A B R S n q k : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 1 mode).imp ((OriginalTermTraceSyntax.metadata w z P).imp ((empty z).imp ((SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S).imp ((SyntaxMixedImageCodeSyntax.termList w k a B n).imp (((OriginalArgumentFieldSyntax.fields w mode z P k n q).iff (ArgumentProgramFieldSyntax.fields w R S k n q))))))))).close

theorem source_modeOneZeroDepthActualArgumentFieldsIff {m} (w mode z P a b A B R S n q k : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeOneZeroDepthActualArgumentFieldsIffSentence w mode z P a b A B R S n q k) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMixedImageCodeSyntax.termList w k a B n) (Context.add (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S) (Context.add (empty z) (Context.add (OriginalTermTraceSyntax.metadata w z P) (Context.add (SyntaxNumeralSyntax.numeral 1 mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
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
  have h5 : Derives Δ (SyntaxMixedImageCodeSyntax.termList w k a B n) := .hyp (Or.inl rfl)
  exact AbstractTopArgumentFields.fields_iff hZ w mode z P a b A B R S n q k h0 h1 h2 h3 h4 h5

theorem modeOneZeroDepthActualArgumentFieldsIff_kernel_certificate {m} (w mode z P a b A B R S n q k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeOneZeroDepthActualArgumentFieldsIffSentence w mode z P a b A B R S n q k)) := TheoryTransport.sentence (source_modeOneZeroDepthActualArgumentFieldsIff w mode z P a b A B R S n q k)

theorem native_modeOneZeroDepthActualArgumentFieldsIff {m} (w mode z P a b A B R S n q k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeOneZeroDepthActualArgumentFieldsIffSentence w mode z P a b A B R S n q k)) := ZFReplay.replay (modeOneZeroDepthActualArgumentFieldsIff_kernel_certificate w mode z P a b A B R S n q k)

def modeOneZeroDepthActualArgumentProgramIffSentence {m} (w mode z P a b A B R S n q k : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 1 mode).imp ((OriginalTermTraceSyntax.metadata w z P).imp ((empty z).imp ((SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S).imp ((SyntaxMixedImageCodeSyntax.termList w k a B n).imp (((OriginalTransformRowSyntax.run 2 w mode z P n q).iff (ArgumentProgramFieldSyntax.mapped w R S k A b n q))))))))).close

theorem source_modeOneZeroDepthActualArgumentProgramIff {m} (w mode z P a b A B R S n q k : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeOneZeroDepthActualArgumentProgramIffSentence w mode z P a b A B R S n q k) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMixedImageCodeSyntax.termList w k a B n) (Context.add (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S) (Context.add (empty z) (Context.add (OriginalTermTraceSyntax.metadata w z P) (Context.add (SyntaxNumeralSyntax.numeral 1 mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
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
  have h5 : Derives Δ (SyntaxMixedImageCodeSyntax.termList w k a B n) := .hyp (Or.inl rfl)
  exact AbstractTopArgumentFields.run_iff hZ w mode z P a b A B R S n q k h0 h1 h2 h3 h4 h5

theorem modeOneZeroDepthActualArgumentProgramIff_kernel_certificate {m} (w mode z P a b A B R S n q k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeOneZeroDepthActualArgumentProgramIffSentence w mode z P a b A B R S n q k)) := TheoryTransport.sentence (source_modeOneZeroDepthActualArgumentProgramIff w mode z P a b A B R S n q k)

theorem native_modeOneZeroDepthActualArgumentProgramIff {m} (w mode z P a b A B R S n q k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeOneZeroDepthActualArgumentProgramIffSentence w mode z P a b A B R S n q k)) := ZFReplay.replay (modeOneZeroDepthActualArgumentProgramIff_kernel_certificate w mode z P a b A B R S n q k)

def modeOneZeroDepthArgumentsAtActualCodesIffSentence {m} (w mode z P a b A B R S n q k : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 1 mode).imp ((OriginalTermTraceSyntax.metadata w z P).imp ((empty z).imp ((SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S).imp ((SyntaxMixedImageCodeSyntax.termList w k a B n).imp (((OriginalTransformRowSyntax.run 2 w mode z P n q).iff (AbstractTopArgumentSyntax.abstracted w a b A B n q k))))))))).close

theorem source_modeOneZeroDepthArgumentsAtActualCodesIff {m} (w mode z P a b A B R S n q k : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeOneZeroDepthArgumentsAtActualCodesIffSentence w mode z P a b A B R S n q k) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMixedImageCodeSyntax.termList w k a B n) (Context.add (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S) (Context.add (empty z) (Context.add (OriginalTermTraceSyntax.metadata w z P) (Context.add (SyntaxNumeralSyntax.numeral 1 mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
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
  have h5 : Derives Δ (SyntaxMixedImageCodeSyntax.termList w k a B n) := .hyp (Or.inl rfl)
  exact AbstractTopArgumentOperation.at_codes_iff hZ w mode z P a b A B R S n q k h0 h1 h2 h3 h4 h5

theorem modeOneZeroDepthArgumentsAtActualCodesIff_kernel_certificate {m} (w mode z P a b A B R S n q k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeOneZeroDepthArgumentsAtActualCodesIffSentence w mode z P a b A B R S n q k)) := TheoryTransport.sentence (source_modeOneZeroDepthArgumentsAtActualCodesIff w mode z P a b A B R S n q k)

theorem native_modeOneZeroDepthArgumentsAtActualCodesIff {m} (w mode z P a b A B R S n q k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeOneZeroDepthArgumentsAtActualCodesIffSentence w mode z P a b A B R S n q k)) := ZFReplay.replay (modeOneZeroDepthArgumentsAtActualCodesIff_kernel_certificate w mode z P a b A B R S n q k)

def modeOneZeroDepthArgumentsActualOperationIffSentence {m} (w mode z P a b A B n q k : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 1 mode).imp ((OriginalTermTraceSyntax.metadata w z P).imp ((empty z).imp ((SyntaxTopEnvironmentSyntax.abstractInput w a b A B).imp ((SyntaxMixedImageCodeSyntax.termList w k a B n).imp (((OriginalTransformRowSyntax.run 2 w mode z P n q).iff (AbstractTopArgumentSyntax.abstracted w a b A B n q k))))))))).close

theorem source_modeOneZeroDepthArgumentsActualOperationIff {m} (w mode z P a b A B n q k : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeOneZeroDepthArgumentsActualOperationIffSentence w mode z P a b A B n q k) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMixedImageCodeSyntax.termList w k a B n) (Context.add (SyntaxTopEnvironmentSyntax.abstractInput w a b A B) (Context.add (empty z) (Context.add (OriginalTermTraceSyntax.metadata w z P) (Context.add (SyntaxNumeralSyntax.numeral 1 mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
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
  have h4 : Derives Δ (SyntaxTopEnvironmentSyntax.abstractInput w a b A B) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (SyntaxMixedImageCodeSyntax.termList w k a B n) := .hyp (Or.inl rfl)
  exact AbstractTopArgumentOperation.run_iff hZ w mode z P a b A B n q k h0 h1 h2 h3 h4 h5

theorem modeOneZeroDepthArgumentsActualOperationIff_kernel_certificate {m} (w mode z P a b A B n q k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeOneZeroDepthArgumentsActualOperationIffSentence w mode z P a b A B n q k)) := TheoryTransport.sentence (source_modeOneZeroDepthArgumentsActualOperationIff w mode z P a b A B n q k)

theorem native_modeOneZeroDepthArgumentsActualOperationIff {m} (w mode z P a b A B n q k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeOneZeroDepthArgumentsActualOperationIffSentence w mode z P a b A B n q k)) := ZFReplay.replay (modeOneZeroDepthArgumentsActualOperationIff_kernel_certificate w mode z P a b A B n q k)

def modeOneZeroDepthGuardedArgumentsActualOperationIffSentence {m} (w mode z P a b A B n q k : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 1 mode).imp ((OriginalTermTraceSyntax.metadata w z P).imp ((empty z).imp ((SyntaxTopEnvironmentSyntax.abstractInput w a b A B).imp ((((SyntaxMixedImageCodeSyntax.termList w k a B n).conj (OriginalTransformRowSyntax.run 2 w mode z P n q)).iff (AbstractTopArgumentSyntax.abstracted w a b A B n q k)))))))).close

theorem source_modeOneZeroDepthGuardedArgumentsActualOperationIff {m} (w mode z P a b A B n q k : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeOneZeroDepthGuardedArgumentsActualOperationIffSentence w mode z P a b A B n q k) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTopEnvironmentSyntax.abstractInput w a b A B) (Context.add (empty z) (Context.add (OriginalTermTraceSyntax.metadata w z P) (Context.add (SyntaxNumeralSyntax.numeral 1 mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 1 mode) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (OriginalTermTraceSyntax.metadata w z P) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (empty z) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (SyntaxTopEnvironmentSyntax.abstractInput w a b A B) := .hyp (Or.inl rfl)
  exact AbstractTopArgumentOperation.guarded_iff hZ w mode z P a b A B n q k h0 h1 h2 h3 h4

theorem modeOneZeroDepthGuardedArgumentsActualOperationIff_kernel_certificate {m} (w mode z P a b A B n q k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeOneZeroDepthGuardedArgumentsActualOperationIffSentence w mode z P a b A B n q k)) := TheoryTransport.sentence (source_modeOneZeroDepthGuardedArgumentsActualOperationIff w mode z P a b A B n q k)

theorem native_modeOneZeroDepthGuardedArgumentsActualOperationIff {m} (w mode z P a b A B n q k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeOneZeroDepthGuardedArgumentsActualOperationIffSentence w mode z P a b A B n q k)) := ZFReplay.replay (modeOneZeroDepthGuardedArgumentsActualOperationIff_kernel_certificate w mode z P a b A B n q k)

end PPAC.Migration.Internal.ObjectAbstractTopArguments
