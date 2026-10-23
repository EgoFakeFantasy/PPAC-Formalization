import PPAC.Migration.Internal.OriginalNumericTermFiber

/-! 原数值项的实际有类型唯一输出及全内部项承诺之原核证书。 -/
namespace PPAC.Migration.Internal.ObjectOriginalNumericTermFiber
open Source SourceAlgebra SourceLogic OmegaSyntax
open YesMetaZFC.Automation.ObjectHorn (Rule)

def replaceWholeTermAgreementSentence {m} (w mode depth a b c L I R n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 3 mode).imp ((OriginalTermTraceSyntax.metadata w depth L).imp ((SyntaxIdentityMapSyntax.identityCode w a I).imp ((IndexTermImageCodeSyntax.converted true w I R a a c).imp ((SyntaxMixedImageCodeSyntax.termList w b a c L).imp ((SyntaxTermSyntax.term w a b n).imp ((OriginalNumericTermValueSyntax.agreement w mode depth L R L n))))))))).close

theorem source_replaceWholeTermAgreement {m} (w mode depth a b c L I R n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (replaceWholeTermAgreementSentence w mode depth a b c L I R n) := by
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
  exact OriginalNumericTermFiber.replace_agreement hZ w mode depth a b c L I R n h0 h1 h2 h3 h4 h5 h6

theorem replaceWholeTermAgreement_kernel_certificate {m} (w mode depth a b c L I R n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (replaceWholeTermAgreementSentence w mode depth a b c L I R n)) := TheoryTransport.sentence (source_replaceWholeTermAgreement w mode depth a b c L I R n)

theorem native_replaceWholeTermAgreement {m} (w mode depth a b c L I R n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (replaceWholeTermAgreementSentence w mode depth a b c L I R n)) := ZFReplay.replay (replaceWholeTermAgreement_kernel_certificate w mode depth a b c L I R n)

def replaceActualOriginalTermFiberSentence {m} (w mode depth a b c L I R n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 3 mode).imp ((OriginalTermTraceSyntax.metadata w depth L).imp ((SyntaxIdentityMapSyntax.identityCode w a I).imp ((IndexTermImageCodeSyntax.converted true w I R a a c).imp ((SyntaxMixedImageCodeSyntax.termList w b a c L).imp ((SyntaxTermSyntax.term w a b n).imp ((OriginalNumericTermValueSyntax.fiber w mode depth L a c n))))))))).close

theorem source_replaceActualOriginalTermFiber {m} (w mode depth a b c L I R n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (replaceActualOriginalTermFiberSentence w mode depth a b c L I R n) := by
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
  exact OriginalNumericTermFiber.replace_fiber hZ w mode depth a b c L I R n h0 h1 h2 h3 h4 h5 h6

theorem replaceActualOriginalTermFiber_kernel_certificate {m} (w mode depth a b c L I R n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (replaceActualOriginalTermFiberSentence w mode depth a b c L I R n)) := TheoryTransport.sentence (source_replaceActualOriginalTermFiber w mode depth a b c L I R n)

theorem native_replaceActualOriginalTermFiber {m} (w mode depth a b c L I R n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (replaceActualOriginalTermFiberSentence w mode depth a b c L I R n)) := ZFReplay.replay (replaceActualOriginalTermFiber_kernel_certificate w mode depth a b c L I R n)

def replaceAllInternalTermPromiseSentence {m} (w mode depth a b c L I R : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 3 mode).imp ((OriginalTermTraceSyntax.metadata w depth L).imp ((SyntaxIdentityMapSyntax.identityCode w a I).imp ((IndexTermImageCodeSyntax.converted true w I R a a c).imp ((SyntaxMixedImageCodeSyntax.termList w b a c L).imp ((OriginalNumericTermValueSyntax.promise w mode depth L a b a c)))))))).close

theorem source_replaceAllInternalTermPromise {m} (w mode depth a b c L I R : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (replaceAllInternalTermPromiseSentence w mode depth a b c L I R) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMixedImageCodeSyntax.termList w b a c L) (Context.add (IndexTermImageCodeSyntax.converted true w I R a a c) (Context.add (SyntaxIdentityMapSyntax.identityCode w a I) (Context.add (OriginalTermTraceSyntax.metadata w depth L) (Context.add (SyntaxNumeralSyntax.numeral 3 mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
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
  have h3 : Derives Δ (SyntaxIdentityMapSyntax.identityCode w a I) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (IndexTermImageCodeSyntax.converted true w I R a a c) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (SyntaxMixedImageCodeSyntax.termList w b a c L) := .hyp (Or.inl rfl)
  exact OriginalNumericTermFiber.replace_promise hZ w mode depth a b c L I R h0 h1 h2 h3 h4 h5

theorem replaceAllInternalTermPromise_kernel_certificate {m} (w mode depth a b c L I R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (replaceAllInternalTermPromiseSentence w mode depth a b c L I R)) := TheoryTransport.sentence (source_replaceAllInternalTermPromise w mode depth a b c L I R)

theorem native_replaceAllInternalTermPromise {m} (w mode depth a b c L I R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (replaceAllInternalTermPromiseSentence w mode depth a b c L I R)) := ZFReplay.replay (replaceAllInternalTermPromise_kernel_certificate w mode depth a b c L I R)

def weakenWholeTermAgreementSentence {m} (w mode depth parameter a b B I J R S n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 0 mode).imp ((OriginalTermTraceSyntax.metadata w depth parameter).imp ((SyntaxIdentityMapSyntax.identityCode w a I).imp ((SyntaxFreeShiftSyntax.shiftCode w b B J).imp ((IndexTermImageCodeSyntax.converted true w I R a a B).imp ((IndexTermImageCodeSyntax.converted false w J S b a B).imp ((SyntaxTermSyntax.term w a b n).imp ((OriginalNumericTermValueSyntax.agreement w mode depth parameter R S n)))))))))).close

theorem source_weakenWholeTermAgreement {m} (w mode depth parameter a b B I J R S n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (weakenWholeTermAgreementSentence w mode depth parameter a b B I J R S n) := by
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
  exact OriginalNumericTermFiber.weaken_agreement hZ w mode depth parameter a b B I J R S n h0 h1 h2 h3 h4 h5 h6 h7

theorem weakenWholeTermAgreement_kernel_certificate {m} (w mode depth parameter a b B I J R S n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (weakenWholeTermAgreementSentence w mode depth parameter a b B I J R S n)) := TheoryTransport.sentence (source_weakenWholeTermAgreement w mode depth parameter a b B I J R S n)

theorem native_weakenWholeTermAgreement {m} (w mode depth parameter a b B I J R S n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (weakenWholeTermAgreementSentence w mode depth parameter a b B I J R S n)) := ZFReplay.replay (weakenWholeTermAgreement_kernel_certificate w mode depth parameter a b B I J R S n)

def weakenActualOriginalTermFiberSentence {m} (w mode depth parameter a b B I J R S n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 0 mode).imp ((OriginalTermTraceSyntax.metadata w depth parameter).imp ((SyntaxIdentityMapSyntax.identityCode w a I).imp ((SyntaxFreeShiftSyntax.shiftCode w b B J).imp ((IndexTermImageCodeSyntax.converted true w I R a a B).imp ((IndexTermImageCodeSyntax.converted false w J S b a B).imp ((SyntaxTermSyntax.term w a b n).imp ((OriginalNumericTermValueSyntax.fiber w mode depth parameter a B n)))))))))).close

theorem source_weakenActualOriginalTermFiber {m} (w mode depth parameter a b B I J R S n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (weakenActualOriginalTermFiberSentence w mode depth parameter a b B I J R S n) := by
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
  exact OriginalNumericTermFiber.weaken_fiber hZ w mode depth parameter a b B I J R S n h0 h1 h2 h3 h4 h5 h6 h7

theorem weakenActualOriginalTermFiber_kernel_certificate {m} (w mode depth parameter a b B I J R S n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (weakenActualOriginalTermFiberSentence w mode depth parameter a b B I J R S n)) := TheoryTransport.sentence (source_weakenActualOriginalTermFiber w mode depth parameter a b B I J R S n)

theorem native_weakenActualOriginalTermFiber {m} (w mode depth parameter a b B I J R S n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (weakenActualOriginalTermFiberSentence w mode depth parameter a b B I J R S n)) := ZFReplay.replay (weakenActualOriginalTermFiber_kernel_certificate w mode depth parameter a b B I J R S n)

def weakenAllInternalTermPromiseSentence {m} (w mode depth parameter a b B I J R S : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 0 mode).imp ((OriginalTermTraceSyntax.metadata w depth parameter).imp ((SyntaxIdentityMapSyntax.identityCode w a I).imp ((SyntaxFreeShiftSyntax.shiftCode w b B J).imp ((IndexTermImageCodeSyntax.converted true w I R a a B).imp ((IndexTermImageCodeSyntax.converted false w J S b a B).imp ((OriginalNumericTermValueSyntax.promise w mode depth parameter a b a B))))))))).close

theorem source_weakenAllInternalTermPromise {m} (w mode depth parameter a b B I J R S : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (weakenAllInternalTermPromiseSentence w mode depth parameter a b B I J R S) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (IndexTermImageCodeSyntax.converted false w J S b a B) (Context.add (IndexTermImageCodeSyntax.converted true w I R a a B) (Context.add (SyntaxFreeShiftSyntax.shiftCode w b B J) (Context.add (SyntaxIdentityMapSyntax.identityCode w a I) (Context.add (OriginalTermTraceSyntax.metadata w depth parameter) (Context.add (SyntaxNumeralSyntax.numeral 0 mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))
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
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 0 mode) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h2 : Derives Δ (OriginalTermTraceSyntax.metadata w depth parameter) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h3 : Derives Δ (SyntaxIdentityMapSyntax.identityCode w a I) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : Derives Δ (SyntaxFreeShiftSyntax.shiftCode w b B J) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h5 : Derives Δ (IndexTermImageCodeSyntax.converted true w I R a a B) := .hyp (Or.inr (Or.inl rfl))
  have h6 : Derives Δ (IndexTermImageCodeSyntax.converted false w J S b a B) := .hyp (Or.inl rfl)
  exact OriginalNumericTermFiber.weaken_promise hZ w mode depth parameter a b B I J R S h0 h1 h2 h3 h4 h5 h6

theorem weakenAllInternalTermPromise_kernel_certificate {m} (w mode depth parameter a b B I J R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (weakenAllInternalTermPromiseSentence w mode depth parameter a b B I J R S)) := TheoryTransport.sentence (source_weakenAllInternalTermPromise w mode depth parameter a b B I J R S)

theorem native_weakenAllInternalTermPromise {m} (w mode depth parameter a b B I J R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (weakenAllInternalTermPromiseSentence w mode depth parameter a b B I J R S)) := ZFReplay.replay (weakenAllInternalTermPromise_kernel_certificate w mode depth parameter a b B I J R S)

def originalTermValueTransferSentence {m} (w mode depth parameter R S a b c d n q : Fin m) : Source.Sentence := ((OriginalNumericTermValueSyntax.agreement w mode depth parameter R S n).imp ((TermTransformProgramValueSyntax.value w R S a b c d n q).imp ((OriginalNumericTermValueSyntax.value w mode depth parameter c d n q)))).close

theorem source_originalTermValueTransfer {m} (w mode depth parameter R S a b c d n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalTermValueTransferSentence w mode depth parameter R S a b c d n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (TermTransformProgramValueSyntax.value w R S a b c d n q) (Context.add (OriginalNumericTermValueSyntax.agreement w mode depth parameter R S n) (Source.SetLanguage.ZF.at m))
  have h0 : Derives Δ (OriginalNumericTermValueSyntax.agreement w mode depth parameter R S n) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (TermTransformProgramValueSyntax.value w R S a b c d n q) := .hyp (Or.inl rfl)
  exact OriginalNumericTermValueTransfer.value_of_program w mode depth parameter R S a b c d n q h0 h1

theorem originalTermValueTransfer_kernel_certificate {m} (w mode depth parameter R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalTermValueTransferSentence w mode depth parameter R S a b c d n q)) := TheoryTransport.sentence (source_originalTermValueTransfer w mode depth parameter R S a b c d n q)

theorem native_originalTermValueTransfer {m} (w mode depth parameter R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalTermValueTransferSentence w mode depth parameter R S a b c d n q)) := ZFReplay.replay (originalTermValueTransfer_kernel_certificate w mode depth parameter R S a b c d n q)

def originalTermFiberTransferSentence {m} (w mode depth parameter R S a b c d n : Fin m) : Source.Sentence := ((OriginalNumericTermValueSyntax.agreement w mode depth parameter R S n).imp ((TermTransformProgramValueSyntax.fiber w R S a b c d n).imp ((OriginalNumericTermValueSyntax.fiber w mode depth parameter c d n)))).close

theorem source_originalTermFiberTransfer {m} (w mode depth parameter R S a b c d n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalTermFiberTransferSentence w mode depth parameter R S a b c d n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (TermTransformProgramValueSyntax.fiber w R S a b c d n) (Context.add (OriginalNumericTermValueSyntax.agreement w mode depth parameter R S n) (Source.SetLanguage.ZF.at m))
  have h0 : Derives Δ (OriginalNumericTermValueSyntax.agreement w mode depth parameter R S n) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (TermTransformProgramValueSyntax.fiber w R S a b c d n) := .hyp (Or.inl rfl)
  exact OriginalNumericTermValueTransfer.fiber_of_program w mode depth parameter R S a b c d n h0 h1

theorem originalTermFiberTransfer_kernel_certificate {m} (w mode depth parameter R S a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalTermFiberTransferSentence w mode depth parameter R S a b c d n)) := TheoryTransport.sentence (source_originalTermFiberTransfer w mode depth parameter R S a b c d n)

theorem native_originalTermFiberTransfer {m} (w mode depth parameter R S a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalTermFiberTransferSentence w mode depth parameter R S a b c d n)) := ZFReplay.replay (originalTermFiberTransfer_kernel_certificate w mode depth parameter R S a b c d n)

def originalTermValueTargetTypeSentence {m} (w mode depth parameter c d n q : Fin m) : Source.Sentence := ((OriginalNumericTermValueSyntax.value w mode depth parameter c d n q).imp ((SyntaxTermSyntax.term w c d q))).close

theorem source_originalTermValueTargetType {m} (w mode depth parameter c d n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalTermValueTargetTypeSentence w mode depth parameter c d n q) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (OriginalNumericTermValueSyntax.value w mode depth parameter c d n q) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (OriginalNumericTermValueSyntax.value w mode depth parameter c d n q) := .hyp (Or.inl rfl)
  exact OriginalNumericTermValueSyntax.target_type w mode depth parameter c d n q h0

theorem originalTermValueTargetType_kernel_certificate {m} (w mode depth parameter c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalTermValueTargetTypeSentence w mode depth parameter c d n q)) := TheoryTransport.sentence (source_originalTermValueTargetType w mode depth parameter c d n q)

theorem native_originalTermValueTargetType {m} (w mode depth parameter c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalTermValueTargetTypeSentence w mode depth parameter c d n q)) := ZFReplay.replay (originalTermValueTargetType_kernel_certificate w mode depth parameter c d n q)

def originalTermAllCandidateUniqueSentence {m} (w mode depth parameter c d n q v : Fin m) : Source.Sentence := ((OriginalNumericTermValueSyntax.value w mode depth parameter c d n q).imp ((OriginalTransformRowSyntax.run 1 w mode depth parameter n v).imp ((Formula.equal v q)))).close

theorem source_originalTermAllCandidateUnique {m} (w mode depth parameter c d n q v : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalTermAllCandidateUniqueSentence w mode depth parameter c d n q v) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (OriginalTransformRowSyntax.run 1 w mode depth parameter n v) (Context.add (OriginalNumericTermValueSyntax.value w mode depth parameter c d n q) (Source.SetLanguage.ZF.at m))
  have h0 : Derives Δ (OriginalNumericTermValueSyntax.value w mode depth parameter c d n q) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (OriginalTransformRowSyntax.run 1 w mode depth parameter n v) := .hyp (Or.inl rfl)
  exact OriginalNumericTermValueSyntax.unique w mode depth parameter c d n q v h0 h1

theorem originalTermAllCandidateUnique_kernel_certificate {m} (w mode depth parameter c d n q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalTermAllCandidateUniqueSentence w mode depth parameter c d n q v)) := TheoryTransport.sentence (source_originalTermAllCandidateUnique w mode depth parameter c d n q v)

theorem native_originalTermAllCandidateUnique {m} (w mode depth parameter c d n q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalTermAllCandidateUniqueSentence w mode depth parameter c d n q v)) := ZFReplay.replay (originalTermAllCandidateUnique_kernel_certificate w mode depth parameter c d n q v)

end PPAC.Migration.Internal.ObjectOriginalNumericTermFiber
