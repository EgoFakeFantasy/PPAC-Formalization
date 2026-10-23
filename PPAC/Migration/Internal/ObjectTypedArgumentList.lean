import PPAC.Migration.Internal.TypedArgumentListCases

/-! 有类型内部列表构造与分解、原数值项桥的闭句原核证书。 -/
namespace PPAC.Migration.Internal.ObjectTypedArgumentList
open Source SourceAlgebra SourceLogic OmegaSyntax
open YesMetaZFC.Automation.ObjectHorn (Rule)

def numericTermModeRunIffSentence {m} (three : Bool) (w mode depth parameter input output : Fin m) : Source.Sentence := ((SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode).imp (((OriginalTransformRowSyntax.run 1 w mode depth parameter input output).iff (OriginalTermTraceSyntax.run three w depth parameter input output)))).close

theorem source_numericTermModeRunIff {m} (three : Bool) (w mode depth parameter input output : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (numericTermModeRunIffSentence three w mode depth parameter input output) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode) := .hyp (Or.inl rfl)
  exact OriginalTermModeBridge.run_iff hZ three w mode depth parameter input output h0

theorem numericTermModeRunIff_kernel_certificate {m} (three : Bool) (w mode depth parameter input output : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (numericTermModeRunIffSentence three w mode depth parameter input output)) := TheoryTransport.sentence (source_numericTermModeRunIff three w mode depth parameter input output)

theorem native_numericTermModeRunIff {m} (three : Bool) (w mode depth parameter input output : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (numericTermModeRunIffSentence three w mode depth parameter input output)) := ZFReplay.replay (numericTermModeRunIff_kernel_certificate three w mode depth parameter input output)

def numericReplaceOnTypedTermSentence {m} (w mode depth a b c L I R n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 3 mode).imp ((OriginalTermTraceSyntax.metadata w depth L).imp ((SyntaxIdentityMapSyntax.identityCode w a I).imp ((IndexTermImageCodeSyntax.converted true w I R a a c).imp ((SyntaxMixedImageCodeSyntax.termList w b a c L).imp ((SyntaxTermSyntax.term w a b n).imp (((OriginalTransformRowSyntax.run 1 w mode depth L n q).iff (TermTransformProgramSyntax.run TermTransformProgramSyntax.termProgram w R L n q)))))))))).close

theorem source_numericReplaceOnTypedTerm {m} (w mode depth a b c L I R n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (numericReplaceOnTypedTermSentence w mode depth a b c L I R n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTermSyntax.term w a b n) (Context.add (SyntaxMixedImageCodeSyntax.termList w b a c L) (Context.add (IndexTermImageCodeSyntax.converted true w I R a a c) (Context.add (SyntaxIdentityMapSyntax.identityCode w a I) (Context.add (OriginalTermTraceSyntax.metadata w depth L) (Context.add (SyntaxNumeralSyntax.numeral 3 mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))
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
  have h3 : Derives Δ (SyntaxIdentityMapSyntax.identityCode w a I) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : Derives Δ (IndexTermImageCodeSyntax.converted true w I R a a c) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h5 : Derives Δ (SyntaxMixedImageCodeSyntax.termList w b a c L) := .hyp (Or.inr (Or.inl rfl))
  have h6 : Derives Δ (SyntaxTermSyntax.term w a b n) := .hyp (Or.inl rfl)
  exact OriginalNumericTermProgram.replace_on_term hZ w mode depth a b c L I R n q h0 h1 h2 h3 h4 h5 h6

theorem numericReplaceOnTypedTerm_kernel_certificate {m} (w mode depth a b c L I R n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (numericReplaceOnTypedTermSentence w mode depth a b c L I R n q)) := TheoryTransport.sentence (source_numericReplaceOnTypedTerm w mode depth a b c L I R n q)

theorem native_numericReplaceOnTypedTerm {m} (w mode depth a b c L I R n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (numericReplaceOnTypedTermSentence w mode depth a b c L I R n q)) := ZFReplay.replay (numericReplaceOnTypedTerm_kernel_certificate w mode depth a b c L I R n q)

def numericWeakenOnTypedTermSentence {m} (w mode depth parameter a b B I J R S n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 0 mode).imp ((OriginalTermTraceSyntax.metadata w depth parameter).imp ((SyntaxIdentityMapSyntax.identityCode w a I).imp ((SyntaxFreeShiftSyntax.shiftCode w b B J).imp ((IndexTermImageCodeSyntax.converted true w I R a a B).imp ((IndexTermImageCodeSyntax.converted false w J S b a B).imp ((SyntaxTermSyntax.term w a b n).imp (((OriginalTransformRowSyntax.run 1 w mode depth parameter n q).iff (TermTransformProgramSyntax.run TermTransformProgramSyntax.termProgram w R S n q))))))))))).close

theorem source_numericWeakenOnTypedTerm {m} (w mode depth parameter a b B I J R S n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (numericWeakenOnTypedTermSentence w mode depth parameter a b B I J R S n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTermSyntax.term w a b n) (Context.add (IndexTermImageCodeSyntax.converted false w J S b a B) (Context.add (IndexTermImageCodeSyntax.converted true w I R a a B) (Context.add (SyntaxFreeShiftSyntax.shiftCode w b B J) (Context.add (SyntaxIdentityMapSyntax.identityCode w a I) (Context.add (OriginalTermTraceSyntax.metadata w depth parameter) (Context.add (SyntaxNumeralSyntax.numeral 0 mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))))
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
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 0 mode) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h2 : Derives Δ (OriginalTermTraceSyntax.metadata w depth parameter) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h3 : Derives Δ (SyntaxIdentityMapSyntax.identityCode w a I) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h4 : Derives Δ (SyntaxFreeShiftSyntax.shiftCode w b B J) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h5 : Derives Δ (IndexTermImageCodeSyntax.converted true w I R a a B) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h6 : Derives Δ (IndexTermImageCodeSyntax.converted false w J S b a B) := .hyp (Or.inr (Or.inl rfl))
  have h7 : Derives Δ (SyntaxTermSyntax.term w a b n) := .hyp (Or.inl rfl)
  exact OriginalNumericTermProgram.weaken_on_term hZ w mode depth parameter a b B I J R S n q h0 h1 h2 h3 h4 h5 h6 h7

theorem numericWeakenOnTypedTerm_kernel_certificate {m} (w mode depth parameter a b B I J R S n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (numericWeakenOnTypedTermSentence w mode depth parameter a b B I J R S n q)) := TheoryTransport.sentence (source_numericWeakenOnTypedTerm w mode depth parameter a b B I J R S n q)

theorem native_numericWeakenOnTypedTerm {m} (w mode depth parameter a b B I J R S n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (numericWeakenOnTypedTermSentence w mode depth parameter a b B I J R S n q)) := ZFReplay.replay (numericWeakenOnTypedTerm_kernel_certificate w mode depth parameter a b B I J R S n q)

def typedNilListIntroductionSentence {m} (w z a b n : Fin m) : Source.Sentence := ((omega w).imp ((empty z).imp ((SyntaxTermSyntax.contexts w a b).imp ((StructuralListSyntax.nilCode w n).imp ((SyntaxMixedImageCodeSyntax.termList w z a b n)))))).close

theorem source_typedNilListIntroduction {m} (w z a b n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (typedNilListIntroductionSentence w z a b n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralListSyntax.nilCode w n) (Context.add (SyntaxTermSyntax.contexts w a b) (Context.add (empty z) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (empty z) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxTermSyntax.contexts w a b) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (StructuralListSyntax.nilCode w n) := .hyp (Or.inl rfl)
  exact TypedArgumentListConstruction.nil_list hZ w z a b n h0 h1 h2 h3

theorem typedNilListIntroduction_kernel_certificate {m} (w z a b n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (typedNilListIntroductionSentence w z a b n)) := TheoryTransport.sentence (source_typedNilListIntroduction w z a b n)

theorem native_typedNilListIntroduction {m} (w z a b n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (typedNilListIntroductionSentence w z a b n)) := ZFReplay.replay (typedNilListIntroduction_kernel_certificate w z a b n)

def typedConsListIntroductionSentence {m} (w ell k a b h t n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxTermSyntax.term w a b h).imp ((SyntaxMixedImageCodeSyntax.termList w ell a b t).imp ((StructuralListSyntax.consCode w h t n).imp ((successor k ell).imp ((SyntaxMixedImageCodeSyntax.termList w k a b n))))))).close

theorem source_typedConsListIntroduction {m} (w ell k a b h t n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (typedConsListIntroductionSentence w ell k a b h t n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor k ell) (Context.add (StructuralListSyntax.consCode w h t n) (Context.add (SyntaxMixedImageCodeSyntax.termList w ell a b t) (Context.add (SyntaxTermSyntax.term w a b h) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxTermSyntax.term w a b h) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (SyntaxMixedImageCodeSyntax.termList w ell a b t) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (StructuralListSyntax.consCode w h t n) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (successor k ell) := .hyp (Or.inl rfl)
  exact TypedArgumentListConstruction.cons_list hZ w ell k a b h t n h0 h1 h2 h3 h4

theorem typedConsListIntroduction_kernel_certificate {m} (w ell k a b h t n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (typedConsListIntroductionSentence w ell k a b h t n)) := TheoryTransport.sentence (source_typedConsListIntroduction w ell k a b h t n)

theorem native_typedConsListIntroduction {m} (w ell k a b h t n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (typedConsListIntroductionSentence w ell k a b h t n)) := ZFReplay.replay (typedConsListIntroduction_kernel_certificate w ell k a b h t n)

def typedConsActualPredecessorSentence {m} (w k a b h t n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMixedImageCodeSyntax.termList w k a b n).imp ((Formula.mem h w).imp ((Formula.mem t w).imp ((StructuralListSyntax.consCode w h t n).imp ((TypedArgumentListElimination.consParts w k a b h t))))))).close

theorem source_typedConsActualPredecessor {m} (w k a b h t n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (typedConsActualPredecessorSentence w k a b h t n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralListSyntax.consCode w h t n) (Context.add (Formula.mem t w) (Context.add (Formula.mem h w) (Context.add (SyntaxMixedImageCodeSyntax.termList w k a b n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxMixedImageCodeSyntax.termList w k a b n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (Formula.mem h w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (Formula.mem t w) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (StructuralListSyntax.consCode w h t n) := .hyp (Or.inl rfl)
  exact TypedArgumentListElimination.cons_parts hZ w k a b h t n h0 h1 h2 h3 h4

theorem typedConsActualPredecessor_kernel_certificate {m} (w k a b h t n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (typedConsActualPredecessorSentence w k a b h t n)) := TheoryTransport.sentence (source_typedConsActualPredecessor w k a b h t n)

theorem native_typedConsActualPredecessor {m} (w k a b h t n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (typedConsActualPredecessorSentence w k a b h t n)) := ZFReplay.replay (typedConsActualPredecessor_kernel_certificate w k a b h t n)

def typedConsHeadSentence {m} (w k a b h t n ell : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMixedImageCodeSyntax.termList w k a b n).imp ((Formula.mem h w).imp ((Formula.mem t w).imp ((StructuralListSyntax.consCode w h t n).imp ((Formula.mem ell w).imp ((successor k ell).imp ((SyntaxTermSyntax.term w a b h))))))))).close

theorem source_typedConsHead {m} (w k a b h t n ell : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (typedConsHeadSentence w k a b h t n ell) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor k ell) (Context.add (Formula.mem ell w) (Context.add (StructuralListSyntax.consCode w h t n) (Context.add (Formula.mem t w) (Context.add (Formula.mem h w) (Context.add (SyntaxMixedImageCodeSyntax.termList w k a b n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))
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
  have h1 : Derives Δ (SyntaxMixedImageCodeSyntax.termList w k a b n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h2 : Derives Δ (Formula.mem h w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h3 : Derives Δ (Formula.mem t w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : Derives Δ (StructuralListSyntax.consCode w h t n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h5 : Derives Δ (Formula.mem ell w) := .hyp (Or.inr (Or.inl rfl))
  have h6 : Derives Δ (successor k ell) := .hyp (Or.inl rfl)
  exact TypedArgumentListElimination.head_term hZ w k a b h t n ell h0 h1 h2 h3 h4 h5 h6

theorem typedConsHead_kernel_certificate {m} (w k a b h t n ell : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (typedConsHeadSentence w k a b h t n ell)) := TheoryTransport.sentence (source_typedConsHead w k a b h t n ell)

theorem native_typedConsHead {m} (w k a b h t n ell : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (typedConsHeadSentence w k a b h t n ell)) := ZFReplay.replay (typedConsHead_kernel_certificate w k a b h t n ell)

def typedConsTailSentence {m} (w k a b h t n ell : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMixedImageCodeSyntax.termList w k a b n).imp ((Formula.mem h w).imp ((Formula.mem t w).imp ((StructuralListSyntax.consCode w h t n).imp ((Formula.mem ell w).imp ((successor k ell).imp ((StructuralListLengthSyntax.hasLength w t ell).imp ((SyntaxMixedImageCodeSyntax.termList w ell a b t)))))))))).close

theorem source_typedConsTail {m} (w k a b h t n ell : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (typedConsTailSentence w k a b h t n ell) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralListLengthSyntax.hasLength w t ell) (Context.add (successor k ell) (Context.add (Formula.mem ell w) (Context.add (StructuralListSyntax.consCode w h t n) (Context.add (Formula.mem t w) (Context.add (Formula.mem h w) (Context.add (SyntaxMixedImageCodeSyntax.termList w k a b n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))))
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
  have h1 : Derives Δ (SyntaxMixedImageCodeSyntax.termList w k a b n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h2 : Derives Δ (Formula.mem h w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h3 : Derives Δ (Formula.mem t w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h4 : Derives Δ (StructuralListSyntax.consCode w h t n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h5 : Derives Δ (Formula.mem ell w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h6 : Derives Δ (successor k ell) := .hyp (Or.inr (Or.inl rfl))
  have h7 : Derives Δ (StructuralListLengthSyntax.hasLength w t ell) := .hyp (Or.inl rfl)
  exact TypedArgumentListElimination.tail_list hZ w k a b h t n ell h0 h1 h2 h3 h4 h5 h6 h7

theorem typedConsTail_kernel_certificate {m} (w k a b h t n ell : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (typedConsTailSentence w k a b h t n ell)) := TheoryTransport.sentence (source_typedConsTail w k a b h t n ell)

theorem native_typedConsTail {m} (w k a b h t n ell : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (typedConsTailSentence w k a b h t n ell)) := ZFReplay.replay (typedConsTail_kernel_certificate w k a b h t n ell)

def typedNilListIffSentence {m} (w k a b n : Fin m) : Source.Sentence := ((omega w).imp ((StructuralListSyntax.nilCode w n).imp (((SyntaxMixedImageCodeSyntax.termList w k a b n).iff ((empty k).conj (SyntaxTermSyntax.contexts w a b)))))).close

theorem source_typedNilListIff {m} (w k a b n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (typedNilListIffSentence w k a b n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralListSyntax.nilCode w n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (StructuralListSyntax.nilCode w n) := .hyp (Or.inl rfl)
  exact TypedArgumentListCases.nil_iff hZ w k a b n h0 h1

theorem typedNilListIff_kernel_certificate {m} (w k a b n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (typedNilListIffSentence w k a b n)) := TheoryTransport.sentence (source_typedNilListIff w k a b n)

theorem native_typedNilListIff {m} (w k a b n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (typedNilListIffSentence w k a b n)) := ZFReplay.replay (typedNilListIff_kernel_certificate w k a b n)

def typedConsListIffSentence {m} (w k a b n h t : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem h w).imp ((Formula.mem t w).imp ((StructuralListSyntax.consCode w h t n).imp (((SyntaxMixedImageCodeSyntax.termList w k a b n).iff (TypedArgumentListElimination.consParts w k a b h t))))))).close

theorem source_typedConsListIff {m} (w k a b n h t : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (typedConsListIffSentence w k a b n h t) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralListSyntax.consCode w h t n) (Context.add (Formula.mem t w) (Context.add (Formula.mem h w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (Formula.mem h w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (Formula.mem t w) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (StructuralListSyntax.consCode w h t n) := .hyp (Or.inl rfl)
  exact TypedArgumentListCases.cons_iff hZ w k a b n h t h0 h1 h2 h3

theorem typedConsListIff_kernel_certificate {m} (w k a b n h t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (typedConsListIffSentence w k a b n h t)) := TheoryTransport.sentence (source_typedConsListIff w k a b n h t)

theorem native_typedConsListIff {m} (w k a b n h t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (typedConsListIffSentence w k a b n h t)) := ZFReplay.replay (typedConsListIff_kernel_certificate w k a b n h t)

def typedWholeListCasesIffSentence {m} (w k a b n : Fin m) : Source.Sentence := ((omega w).imp (((SyntaxMixedImageCodeSyntax.termList w k a b n).iff (TypedArgumentListCases.cases w k a b n)))).close

theorem source_typedWholeListCasesIff {m} (w k a b n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (typedWholeListCasesIffSentence w k a b n) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact TypedArgumentListCases.cases_iff hZ w k a b n h0

theorem typedWholeListCasesIff_kernel_certificate {m} (w k a b n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (typedWholeListCasesIffSentence w k a b n)) := TheoryTransport.sentence (source_typedWholeListCasesIff w k a b n)

theorem native_typedWholeListCasesIff {m} (w k a b n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (typedWholeListCasesIffSentence w k a b n)) := ZFReplay.replay (typedWholeListCasesIff_kernel_certificate w k a b n)

end PPAC.Migration.Internal.ObjectTypedArgumentList
