import PPAC.Migration.Internal.ProjectCompilerSourceAccepted

/-! Actual compiler input validity and exact source acceptance; original byte-packet bridge remains unproved in the original nativeZF kernel; complete schema tests and Con remain unproved. -/
namespace PPAC.Migration.Internal.ObjectProjectCompilerSourceValid
open Source SourceAlgebra SourceLogic OmegaSyntax

def compilerSourceChildValidityFromMemberIHSentence {m} (w n f : Fin m) : Source.Sentence := ((Formula.mem f w).imp ((ProjectCompilerSourceSyntax.allIH w n).imp ((ProjectCompilerSourceSyntax.goodQueries ProjectCompilerRecursiveSyntax.codeMatrix (ProjectCompilerRecursiveSyntax.parameters w) w n f)))).close

theorem source_compilerSourceChildValidityFromMemberIH {m} (w n f : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (compilerSourceChildValidityFromMemberIHSentence w n f) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ProjectCompilerSourceSyntax.allIH w n) (Context.add (Formula.mem f w) (Source.SetLanguage.ZF.at m))
  have h0 : Derives Δ (Formula.mem f w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (ProjectCompilerSourceSyntax.allIH w n) := .hyp (Or.inl rfl)
  exact ProjectCompilerSourceIH.supply_queries w n f h0 h1

theorem compilerSourceChildValidityFromMemberIH_kernel_certificate {m} (w n f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (compilerSourceChildValidityFromMemberIHSentence w n f)) := TheoryTransport.sentence (source_compilerSourceChildValidityFromMemberIH w n f)

theorem native_compilerSourceChildValidityFromMemberIH {m} (w n f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (compilerSourceChildValidityFromMemberIHSentence w n f)) := ZFReplay.replay (compilerSourceChildValidityFromMemberIH_kernel_certificate w n f)

def compilerActualCasesRecoverSourceGrammarSentence {m} (w b z n q f : Fin m) : Source.Sentence := ((SyntaxTermSyntax.contexts w b f).imp ((ProjectCompilerSourceSyntax.goodQueries ProjectCompilerRecursiveSyntax.codeMatrix (ProjectCompilerRecursiveSyntax.parameters w) w n f).imp ((ProjectCompilerRecursiveSyntax.casesAt w b z n q).imp ((ProjectSourceCodeRecursiveSyntax.allCases w n b f))))).close

theorem source_compilerActualCasesRecoverSourceGrammar {m} (w b z n q f : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (compilerActualCasesRecoverSourceGrammarSentence w b z n q f) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ProjectCompilerRecursiveSyntax.casesAt w b z n q) (Context.add (ProjectCompilerSourceSyntax.goodQueries ProjectCompilerRecursiveSyntax.codeMatrix (ProjectCompilerRecursiveSyntax.parameters w) w n f) (Context.add (SyntaxTermSyntax.contexts w b f) (Source.SetLanguage.ZF.at m)))
  have h0 : Derives Δ (SyntaxTermSyntax.contexts w b f) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (ProjectCompilerSourceSyntax.goodQueries ProjectCompilerRecursiveSyntax.codeMatrix (ProjectCompilerRecursiveSyntax.parameters w) w n f) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (ProjectCompilerRecursiveSyntax.casesAt w b z n q) := .hyp (Or.inl rfl)
  exact ProjectCompilerSourceCases.actual_source_cases w b z n q f h0 h1 h2

theorem compilerActualCasesRecoverSourceGrammar_kernel_certificate {m} (w b z n q f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (compilerActualCasesRecoverSourceGrammarSentence w b z n q f)) := TheoryTransport.sentence (source_compilerActualCasesRecoverSourceGrammar w b z n q f)

theorem native_compilerActualCasesRecoverSourceGrammar {m} (w b z n q f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (compilerActualCasesRecoverSourceGrammarSentence w b z n q f)) := ZFReplay.replay (compilerActualCasesRecoverSourceGrammar_kernel_certificate w b z n q f)

def compilerInputValidFromMemberIHSentence {m} (w n b q f : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem f w).imp ((ProjectCompilerSourceSyntax.allIH w n).imp ((ProjectCompilerCodeSyntax.compiled w n b q).imp ((ProjectSourceCodeSyntax.sourceCode w n b f)))))).close

theorem source_compilerInputValidFromMemberIH {m} (w n b q f : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (compilerInputValidFromMemberIHSentence w n b q f) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ProjectCompilerCodeSyntax.compiled w n b q) (Context.add (ProjectCompilerSourceSyntax.allIH w n) (Context.add (Formula.mem f w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (Formula.mem f w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (ProjectCompilerSourceSyntax.allIH w n) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (ProjectCompilerCodeSyntax.compiled w n b q) := .hyp (Or.inl rfl)
  exact ProjectCompilerSourceStep.input_from_induction hZ w n b q f h0 h1 h2 h3

theorem compilerInputValidFromMemberIH_kernel_certificate {m} (w n b q f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (compilerInputValidFromMemberIHSentence w n b q f)) := TheoryTransport.sentence (source_compilerInputValidFromMemberIH w n b q f)

theorem native_compilerInputValidFromMemberIH {m} (w n b q f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (compilerInputValidFromMemberIHSentence w n b q f)) := ZFReplay.replay (compilerInputValidFromMemberIH_kernel_certificate w n b q f)

def compilerSourceValidityProgressiveSentence {m} (w : Fin m) : Source.Sentence := ((omega w).imp ((SetInductionSyntax.progressive ProjectCompilerSourceValid.inductionMatrix (fun _ : Fin 1 => w)))).close

theorem source_compilerSourceValidityProgressive {m} (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (compilerSourceValidityProgressiveSentence w) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact ProjectCompilerSourceValid.progressive hZ w h0

theorem compilerSourceValidityProgressive_kernel_certificate {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (compilerSourceValidityProgressiveSentence w)) := TheoryTransport.sentence (source_compilerSourceValidityProgressive w)

theorem native_compilerSourceValidityProgressive {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (compilerSourceValidityProgressiveSentence w)) := ZFReplay.replay (compilerSourceValidityProgressive_kernel_certificate w)

def compilerAllInternalActualInputsValidSentence {m} (w : Fin m) : Source.Sentence := ((omega w).imp ((.all (ProjectCompilerSourceSyntax.correct w.castSucc (Fin.last m))))).close

theorem source_compilerAllInternalActualInputsValid {m} (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (compilerAllInternalActualInputsValidSentence w) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact ProjectCompilerSourceValid.all_correct hZ w h0

theorem compilerAllInternalActualInputsValid_kernel_certificate {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (compilerAllInternalActualInputsValidSentence w)) := TheoryTransport.sentence (source_compilerAllInternalActualInputsValid w)

theorem native_compilerAllInternalActualInputsValid {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (compilerAllInternalActualInputsValidSentence w)) := ZFReplay.replay (compilerAllInternalActualInputsValid_kernel_certificate w)

def compilerActualInputValidSentence {m} (w n b q f : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem f w).imp ((ProjectCompilerCodeSyntax.compiled w n b q).imp ((ProjectSourceCodeSyntax.sourceCode w n b f))))).close

theorem source_compilerActualInputValid {m} (w n b q f : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (compilerActualInputValidSentence w n b q f) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ProjectCompilerCodeSyntax.compiled w n b q) (Context.add (Formula.mem f w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (Formula.mem f w) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (ProjectCompilerCodeSyntax.compiled w n b q) := .hyp (Or.inl rfl)
  exact ProjectCompilerSourceValid.valid_input hZ w n b q f h0 h1 h2

theorem compilerActualInputValid_kernel_certificate {m} (w n b q f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (compilerActualInputValidSentence w n b q f)) := TheoryTransport.sentence (source_compilerActualInputValid w n b q f)

theorem native_compilerActualInputValid {m} (w n b q f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (compilerActualInputValidSentence w n b q f)) := ZFReplay.replay (compilerActualInputValid_kernel_certificate w n b q f)

def compilerSourceAcceptanceIffSentence {m} (w n b f : Fin m) : Source.Sentence := ((omega w).imp (((ProjectSourceCodeSyntax.sourceCode w n b f).iff (ProjectCompilerSourceAcceptedSyntax.accepted w n b f)))).close

theorem source_compilerSourceAcceptanceIff {m} (w n b f : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (compilerSourceAcceptanceIffSentence w n b f) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact ProjectCompilerSourceAccepted.source_iff_exists hZ w n b f h0

theorem compilerSourceAcceptanceIff_kernel_certificate {m} (w n b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (compilerSourceAcceptanceIffSentence w n b f)) := TheoryTransport.sentence (source_compilerSourceAcceptanceIff w n b f)

theorem native_compilerSourceAcceptanceIff {m} (w n b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (compilerSourceAcceptanceIffSentence w n b f)) := ZFReplay.replay (compilerSourceAcceptanceIff_kernel_certificate w n b f)

def compilerSourceTypedUniqueAcceptanceIffSentence {m} (w n b f z : Fin m) : Source.Sentence := ((omega w).imp ((empty z).imp (((ProjectSourceCodeSyntax.sourceCode w n b f).iff (ProjectCompilerSourceAcceptedSyntax.typedAccepted w n b f z))))).close

theorem source_compilerSourceTypedUniqueAcceptanceIff {m} (w n b f z : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (compilerSourceTypedUniqueAcceptanceIffSentence w n b f z) := by
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
  exact ProjectCompilerSourceAccepted.source_iff_typed_fiber hZ w n b f z h0 h1

theorem compilerSourceTypedUniqueAcceptanceIff_kernel_certificate {m} (w n b f z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (compilerSourceTypedUniqueAcceptanceIffSentence w n b f z)) := TheoryTransport.sentence (source_compilerSourceTypedUniqueAcceptanceIff w n b f z)

theorem native_compilerSourceTypedUniqueAcceptanceIff {m} (w n b f z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (compilerSourceTypedUniqueAcceptanceIffSentence w n b f z)) := ZFReplay.replay (compilerSourceTypedUniqueAcceptanceIff_kernel_certificate w n b f z)

def compilerAllInternalSourceAcceptanceIffSentence {m} (w : Fin m) : Source.Sentence := ((omega w).imp ((ProjectCompilerSourceAcceptedSyntax.allAcceptanceLaw w))).close

theorem source_compilerAllInternalSourceAcceptanceIff {m} (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (compilerAllInternalSourceAcceptanceIffSentence w) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact ProjectCompilerSourceAccepted.all_source_iff_exists hZ w h0

theorem compilerAllInternalSourceAcceptanceIff_kernel_certificate {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (compilerAllInternalSourceAcceptanceIffSentence w)) := TheoryTransport.sentence (source_compilerAllInternalSourceAcceptanceIff w)

theorem native_compilerAllInternalSourceAcceptanceIff {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (compilerAllInternalSourceAcceptanceIffSentence w)) := ZFReplay.replay (compilerAllInternalSourceAcceptanceIff_kernel_certificate w)

def compilerAllInternalSourceTypedUniqueAcceptanceIffSentence {m} (w : Fin m) : Source.Sentence := ((omega w).imp ((ProjectCompilerSourceAcceptedSyntax.allTypedAcceptanceLaw w))).close

theorem source_compilerAllInternalSourceTypedUniqueAcceptanceIff {m} (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (compilerAllInternalSourceTypedUniqueAcceptanceIffSentence w) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact ProjectCompilerSourceAccepted.all_source_iff_typed_fiber hZ w h0

theorem compilerAllInternalSourceTypedUniqueAcceptanceIff_kernel_certificate {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (compilerAllInternalSourceTypedUniqueAcceptanceIffSentence w)) := TheoryTransport.sentence (source_compilerAllInternalSourceTypedUniqueAcceptanceIff w)

theorem native_compilerAllInternalSourceTypedUniqueAcceptanceIff {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (compilerAllInternalSourceTypedUniqueAcceptanceIffSentence w)) := ZFReplay.replay (compilerAllInternalSourceTypedUniqueAcceptanceIff_kernel_certificate w)

def compilerClosedSourceTypedUniqueAcceptanceIffSentence {m} (w n b z : Fin m) : Source.Sentence := ((omega w).imp ((empty z).imp (((ProjectSourceCodeSyntax.sourceCode w n b z).iff (ProjectCompilerUniqueFiberSyntax.typedFiber w n b z))))).close

theorem source_compilerClosedSourceTypedUniqueAcceptanceIff {m} (w n b z : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (compilerClosedSourceTypedUniqueAcceptanceIffSentence w n b z) := by
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
  exact ProjectCompilerSourceAccepted.closed_source_iff_typed_fiber hZ w n b z h0 h1

theorem compilerClosedSourceTypedUniqueAcceptanceIff_kernel_certificate {m} (w n b z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (compilerClosedSourceTypedUniqueAcceptanceIffSentence w n b z)) := TheoryTransport.sentence (source_compilerClosedSourceTypedUniqueAcceptanceIff w n b z)

theorem native_compilerClosedSourceTypedUniqueAcceptanceIff {m} (w n b z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (compilerClosedSourceTypedUniqueAcceptanceIffSentence w n b z)) := ZFReplay.replay (compilerClosedSourceTypedUniqueAcceptanceIff_kernel_certificate w n b z)

def compilerInvalidSourceRejectedSentence {m} (w n b q f : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem f w).imp (((ProjectSourceCodeSyntax.sourceCode w n b f).neg).imp (((ProjectCompilerCodeSyntax.compiled w n b q).neg))))).close

theorem source_compilerInvalidSourceRejected {m} (w n b q f : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (compilerInvalidSourceRejectedSentence w n b q f) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add ((ProjectSourceCodeSyntax.sourceCode w n b f).neg) (Context.add (Formula.mem f w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (Formula.mem f w) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ ((ProjectSourceCodeSyntax.sourceCode w n b f).neg) := .hyp (Or.inl rfl)
  exact ProjectCompilerSourceAccepted.reject_invalid_source hZ w n b q f h0 h1 h2

theorem compilerInvalidSourceRejected_kernel_certificate {m} (w n b q f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (compilerInvalidSourceRejectedSentence w n b q f)) := TheoryTransport.sentence (source_compilerInvalidSourceRejected w n b q f)

theorem native_compilerInvalidSourceRejected {m} (w n b q f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (compilerInvalidSourceRejectedSentence w n b q f)) := ZFReplay.replay (compilerInvalidSourceRejected_kernel_certificate w n b q f)

end PPAC.Migration.Internal.ObjectProjectCompilerSourceValid
