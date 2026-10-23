import PPAC.Migration.Internal.OriginalAtomicExistingAtom

/-! 原App异标签排除、等词和常量完整运行到既有原子接口的对象闭句。 -/
namespace PPAC.Migration.Internal.ObjectWholeAtomicInterfaces
open Source SourceAlgebra SourceLogic OmegaSyntax
open YesMetaZFC.Automation.ObjectHorn (Rule)

def rawApplicationWrongTagRejectedSentence {m} (k tag : Nat) (xs : Fin k → Fin m) (w symbol args n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNodeSyntax.constructor k tag w xs n).imp ((OriginalFormulaApplicationSyntax.application w symbol args n).imp ((Formula.bot))))).close

theorem source_rawApplicationWrongTagRejected {m} (k tag : Nat) (hne : tag ≠ 2) (xs : Fin k → Fin m) (w symbol args n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (rawApplicationWrongTagRejectedSentence k tag xs w symbol args n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (OriginalFormulaApplicationSyntax.application w symbol args n) (Context.add (SyntaxNodeSyntax.constructor k tag w xs n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxNodeSyntax.constructor k tag w xs n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (OriginalFormulaApplicationSyntax.application w symbol args n) := .hyp (Or.inl rfl)
  exact OriginalFormulaTagRejection.raw_application_rejected hZ k tag hne w symbol args n xs h0 h1 h2

theorem rawApplicationWrongTagRejected_kernel_certificate {m} (k tag : Nat) (hne : tag ≠ 2) (xs : Fin k → Fin m) (w symbol args n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (rawApplicationWrongTagRejectedSentence k tag xs w symbol args n)) := TheoryTransport.sentence (source_rawApplicationWrongTagRejected k tag hne xs w symbol args n)

theorem native_rawApplicationWrongTagRejected {m} (k tag : Nat) (hne : tag ≠ 2) (xs : Fin k → Fin m) (w symbol args n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (rawApplicationWrongTagRejectedSentence k tag xs w symbol args n)) := ZFReplay.replay (rawApplicationWrongTagRejected_kernel_certificate k tag hne xs w symbol args n)

def applicationCaseWrongTagRejectedSentence {m} (k tag : Nat) (xs : Fin k → Fin m) (w mode depth parameter n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNodeSyntax.constructor k tag w xs n).imp ((OriginalFormulaCaseSyntax.applicationCase w mode depth parameter n q).imp ((Formula.bot))))).close

theorem source_applicationCaseWrongTagRejected {m} (k tag : Nat) (hne : tag ≠ 2) (xs : Fin k → Fin m) (w mode depth parameter n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (applicationCaseWrongTagRejectedSentence k tag xs w mode depth parameter n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (OriginalFormulaCaseSyntax.applicationCase w mode depth parameter n q) (Context.add (SyntaxNodeSyntax.constructor k tag w xs n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxNodeSyntax.constructor k tag w xs n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (OriginalFormulaCaseSyntax.applicationCase w mode depth parameter n q) := .hyp (Or.inl rfl)
  exact OriginalFormulaTagRejection.application_rejected hZ k tag hne w mode depth parameter n q xs h0 h1 h2

theorem applicationCaseWrongTagRejected_kernel_certificate {m} (k tag : Nat) (hne : tag ≠ 2) (xs : Fin k → Fin m) (w mode depth parameter n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (applicationCaseWrongTagRejectedSentence k tag xs w mode depth parameter n q)) := TheoryTransport.sentence (source_applicationCaseWrongTagRejected k tag hne xs w mode depth parameter n q)

theorem native_applicationCaseWrongTagRejected {m} (k tag : Nat) (hne : tag ≠ 2) (xs : Fin k → Fin m) (w mode depth parameter n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (applicationCaseWrongTagRejectedSentence k tag xs w mode depth parameter n q)) := ZFReplay.replay (applicationCaseWrongTagRejected_kernel_certificate k tag hne xs w mode depth parameter n q)

def wholeFalseDispatchIffSentence {m} (three : Bool) (w mode depth parameter n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode).imp ((OriginalTermTraceSyntax.metadata w depth parameter).imp ((SyntaxNodeSyntax.constructor 0 0 w Fin.elim0 n).imp (((OriginalTransformRowSyntax.run 3 w mode depth parameter n q).iff (OriginalFormulaLocalData.constant 0 w n q))))))).close

theorem source_wholeFalseDispatchIff {m} (three : Bool) (w mode depth parameter n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (wholeFalseDispatchIffSentence three w mode depth parameter n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNodeSyntax.constructor 0 0 w Fin.elim0 n) (Context.add (OriginalTermTraceSyntax.metadata w depth parameter) (Context.add (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (OriginalTermTraceSyntax.metadata w depth parameter) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxNodeSyntax.constructor 0 0 w Fin.elim0 n) := .hyp (Or.inl rfl)
  exact OriginalAtomicRunDispatch.run_iff_false hZ three w mode depth parameter n q h0 h1 (.conjL h2) (.conjR h2) h3

theorem wholeFalseDispatchIff_kernel_certificate {m} (three : Bool) (w mode depth parameter n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (wholeFalseDispatchIffSentence three w mode depth parameter n q)) := TheoryTransport.sentence (source_wholeFalseDispatchIff three w mode depth parameter n q)

theorem native_wholeFalseDispatchIff {m} (three : Bool) (w mode depth parameter n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (wholeFalseDispatchIffSentence three w mode depth parameter n q)) := ZFReplay.replay (wholeFalseDispatchIff_kernel_certificate three w mode depth parameter n q)

def wholeTrueDispatchIffSentence {m} (three : Bool) (w mode depth parameter n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode).imp ((OriginalTermTraceSyntax.metadata w depth parameter).imp ((SyntaxNodeSyntax.constructor 0 1 w Fin.elim0 n).imp (((OriginalTransformRowSyntax.run 3 w mode depth parameter n q).iff (OriginalFormulaLocalData.constant 1 w n q))))))).close

theorem source_wholeTrueDispatchIff {m} (three : Bool) (w mode depth parameter n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (wholeTrueDispatchIffSentence three w mode depth parameter n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNodeSyntax.constructor 0 1 w Fin.elim0 n) (Context.add (OriginalTermTraceSyntax.metadata w depth parameter) (Context.add (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (OriginalTermTraceSyntax.metadata w depth parameter) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxNodeSyntax.constructor 0 1 w Fin.elim0 n) := .hyp (Or.inl rfl)
  exact OriginalAtomicRunDispatch.run_iff_true hZ three w mode depth parameter n q h0 h1 (.conjL h2) (.conjR h2) h3

theorem wholeTrueDispatchIff_kernel_certificate {m} (three : Bool) (w mode depth parameter n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (wholeTrueDispatchIffSentence three w mode depth parameter n q)) := TheoryTransport.sentence (source_wholeTrueDispatchIff three w mode depth parameter n q)

theorem native_wholeTrueDispatchIff {m} (three : Bool) (w mode depth parameter n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (wholeTrueDispatchIffSentence three w mode depth parameter n q)) := ZFReplay.replay (wholeTrueDispatchIff_kernel_certificate three w mode depth parameter n q)

def wholeEqualityDispatchIffSentence {m} (three : Bool) (w mode depth parameter n q x y : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode).imp ((OriginalTermTraceSyntax.metadata w depth parameter).imp ((SyntaxAtomSyntax.equalCode w x y n).imp (((OriginalTransformRowSyntax.run 3 w mode depth parameter n q).iff (OriginalFormulaCaseSyntax.binaryCase 3 1 w mode depth parameter n q))))))).close

theorem source_wholeEqualityDispatchIff {m} (three : Bool) (w mode depth parameter n q x y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (wholeEqualityDispatchIffSentence three w mode depth parameter n q x y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxAtomSyntax.equalCode w x y n) (Context.add (OriginalTermTraceSyntax.metadata w depth parameter) (Context.add (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (OriginalTermTraceSyntax.metadata w depth parameter) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxAtomSyntax.equalCode w x y n) := .hyp (Or.inl rfl)
  exact OriginalAtomicRunDispatch.run_iff_equality hZ three w mode depth parameter n q x y h0 h1 (.conjL h2) (.conjR h2) h3

theorem wholeEqualityDispatchIff_kernel_certificate {m} (three : Bool) (w mode depth parameter n q x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (wholeEqualityDispatchIffSentence three w mode depth parameter n q x y)) := TheoryTransport.sentence (source_wholeEqualityDispatchIff three w mode depth parameter n q x y)

theorem native_wholeEqualityDispatchIff {m} (three : Bool) (w mode depth parameter n q x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (wholeEqualityDispatchIffSentence three w mode depth parameter n q x y)) := ZFReplay.replay (wholeEqualityDispatchIff_kernel_certificate three w mode depth parameter n q x y)

def replaceWholeEqualityExistingAtomIffSentence {m} (w mode depth a b c L I R n q x y : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 3 mode).imp ((OriginalTermTraceSyntax.metadata w depth L).imp ((SyntaxIdentityMapSyntax.identityCode w a I).imp ((IndexTermImageCodeSyntax.converted true w I R a a c).imp ((SyntaxMixedImageCodeSyntax.termList w b a c L).imp ((SyntaxAtomSyntax.equalCode w x y n).imp ((ArgumentForestProgramSyntax.typedInputs 2 w a b (SyntaxAtomSyntax.two x y)).imp (((OriginalTransformRowSyntax.run 3 w mode depth L n q).iff (FormulaTransformAtomSyntax.equality w R L a b a c n q))))))))))).close

theorem source_replaceWholeEqualityExistingAtomIff {m} (w mode depth a b c L I R n q x y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (replaceWholeEqualityExistingAtomIffSentence w mode depth a b c L I R n q x y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ArgumentForestProgramSyntax.typedInputs 2 w a b (SyntaxAtomSyntax.two x y)) (Context.add (SyntaxAtomSyntax.equalCode w x y n) (Context.add (SyntaxMixedImageCodeSyntax.termList w b a c L) (Context.add (IndexTermImageCodeSyntax.converted true w I R a a c) (Context.add (SyntaxIdentityMapSyntax.identityCode w a I) (Context.add (OriginalTermTraceSyntax.metadata w depth L) (Context.add (SyntaxNumeralSyntax.numeral 3 mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 3 mode) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h2 : Derives Δ (OriginalTermTraceSyntax.metadata w depth L) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h3 : Derives Δ (SyntaxIdentityMapSyntax.identityCode w a I) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h4 : Derives Δ (IndexTermImageCodeSyntax.converted true w I R a a c) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h5 : Derives Δ (SyntaxMixedImageCodeSyntax.termList w b a c L) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h6 : Derives Δ (SyntaxAtomSyntax.equalCode w x y n) := .hyp (Or.inr (Or.inl rfl))
  have h7 : Derives Δ (ArgumentForestProgramSyntax.typedInputs 2 w a b (SyntaxAtomSyntax.two x y)) := .hyp (Or.inl rfl)
  exact OriginalAtomicExistingAtom.replace_equality_iff hZ w mode depth a b c L I R n q x y h0 h1 h2 h3 h4 h5 h6 h7

theorem replaceWholeEqualityExistingAtomIff_kernel_certificate {m} (w mode depth a b c L I R n q x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (replaceWholeEqualityExistingAtomIffSentence w mode depth a b c L I R n q x y)) := TheoryTransport.sentence (source_replaceWholeEqualityExistingAtomIff w mode depth a b c L I R n q x y)

theorem native_replaceWholeEqualityExistingAtomIff {m} (w mode depth a b c L I R n q x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (replaceWholeEqualityExistingAtomIffSentence w mode depth a b c L I R n q x y)) := ZFReplay.replay (replaceWholeEqualityExistingAtomIff_kernel_certificate w mode depth a b c L I R n q x y)

def weakenWholeEqualityExistingAtomIffSentence {m} (w mode depth parameter a b B I J R S n q x y : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 0 mode).imp ((OriginalTermTraceSyntax.metadata w depth parameter).imp ((SyntaxIdentityMapSyntax.identityCode w a I).imp ((SyntaxFreeShiftSyntax.shiftCode w b B J).imp ((IndexTermImageCodeSyntax.converted true w I R a a B).imp ((IndexTermImageCodeSyntax.converted false w J S b a B).imp ((SyntaxAtomSyntax.equalCode w x y n).imp ((ArgumentForestProgramSyntax.typedInputs 2 w a b (SyntaxAtomSyntax.two x y)).imp (((OriginalTransformRowSyntax.run 3 w mode depth parameter n q).iff (FormulaTransformAtomSyntax.equality w R S a b a B n q)))))))))))).close

theorem source_weakenWholeEqualityExistingAtomIff {m} (w mode depth parameter a b B I J R S n q x y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (weakenWholeEqualityExistingAtomIffSentence w mode depth parameter a b B I J R S n q x y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ArgumentForestProgramSyntax.typedInputs 2 w a b (SyntaxAtomSyntax.two x y)) (Context.add (SyntaxAtomSyntax.equalCode w x y n) (Context.add (IndexTermImageCodeSyntax.converted false w J S b a B) (Context.add (IndexTermImageCodeSyntax.converted true w I R a a B) (Context.add (SyntaxFreeShiftSyntax.shiftCode w b B J) (Context.add (SyntaxIdentityMapSyntax.identityCode w a I) (Context.add (OriginalTermTraceSyntax.metadata w depth parameter) (Context.add (SyntaxNumeralSyntax.numeral 0 mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 0 mode) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  have h2 : Derives Δ (OriginalTermTraceSyntax.metadata w depth parameter) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h3 : Derives Δ (SyntaxIdentityMapSyntax.identityCode w a I) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h4 : Derives Δ (SyntaxFreeShiftSyntax.shiftCode w b B J) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h5 : Derives Δ (IndexTermImageCodeSyntax.converted true w I R a a B) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h6 : Derives Δ (IndexTermImageCodeSyntax.converted false w J S b a B) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h7 : Derives Δ (SyntaxAtomSyntax.equalCode w x y n) := .hyp (Or.inr (Or.inl rfl))
  have h8 : Derives Δ (ArgumentForestProgramSyntax.typedInputs 2 w a b (SyntaxAtomSyntax.two x y)) := .hyp (Or.inl rfl)
  exact OriginalAtomicExistingAtom.weaken_equality_iff hZ w mode depth parameter a b B I J R S n q x y h0 h1 h2 h3 h4 h5 h6 h7 h8

theorem weakenWholeEqualityExistingAtomIff_kernel_certificate {m} (w mode depth parameter a b B I J R S n q x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (weakenWholeEqualityExistingAtomIffSentence w mode depth parameter a b B I J R S n q x y)) := TheoryTransport.sentence (source_weakenWholeEqualityExistingAtomIff w mode depth parameter a b B I J R S n q x y)

theorem native_weakenWholeEqualityExistingAtomIff {m} (w mode depth parameter a b B I J R S n q x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (weakenWholeEqualityExistingAtomIffSentence w mode depth parameter a b B I J R S n q x y)) := ZFReplay.replay (weakenWholeEqualityExistingAtomIff_kernel_certificate w mode depth parameter a b B I J R S n q x y)

def wholeConstantExistingAtomIffSentence {m} (three truth : Bool) (w mode depth parameter a b c d n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode).imp ((OriginalTermTraceSyntax.metadata w depth parameter).imp ((SyntaxAtomSyntax.nullary truth w a b n).imp ((SyntaxTermSyntax.contexts w c d).imp (((OriginalTransformRowSyntax.run 3 w mode depth parameter n q).iff (FormulaTransformAtomSyntax.nullary truth w a b c d n q)))))))).close

theorem source_wholeConstantExistingAtomIff {m} (three truth : Bool) (w mode depth parameter a b c d n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (wholeConstantExistingAtomIffSentence three truth w mode depth parameter a b c d n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTermSyntax.contexts w c d) (Context.add (SyntaxAtomSyntax.nullary truth w a b n) (Context.add (OriginalTermTraceSyntax.metadata w depth parameter) (Context.add (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (OriginalTermTraceSyntax.metadata w depth parameter) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (SyntaxAtomSyntax.nullary truth w a b n) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (SyntaxTermSyntax.contexts w c d) := .hyp (Or.inl rfl)
  exact OriginalAtomicExistingAtom.constant_iff hZ three truth w mode depth parameter a b c d n q h0 h1 h2 h3 h4

theorem wholeConstantExistingAtomIff_kernel_certificate {m} (three truth : Bool) (w mode depth parameter a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (wholeConstantExistingAtomIffSentence three truth w mode depth parameter a b c d n q)) := TheoryTransport.sentence (source_wholeConstantExistingAtomIff three truth w mode depth parameter a b c d n q)

theorem native_wholeConstantExistingAtomIff {m} (three truth : Bool) (w mode depth parameter a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (wholeConstantExistingAtomIffSentence three truth w mode depth parameter a b c d n q)) := ZFReplay.replay (wholeConstantExistingAtomIff_kernel_certificate three truth w mode depth parameter a b c d n q)

end PPAC.Migration.Internal.ObjectWholeAtomicInterfaces
