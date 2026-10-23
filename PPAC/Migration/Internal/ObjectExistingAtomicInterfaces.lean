import PPAC.Migration.Internal.ConstantExistingAtomBridge

/-! 原成员整体运行、等词局部分支和常量数据到既有原子程序接口的对象闭句。 -/
namespace PPAC.Migration.Internal.ObjectExistingAtomicInterfaces
open Source SourceAlgebra SourceLogic OmegaSyntax
open YesMetaZFC.Automation.ObjectHorn (Rule)

def memberResultExistingAtomIffSentence {m} (w R S a b c d s x y n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxAtomSyntax.zeroScalar w s).imp ((SyntaxAtomSyntax.memberCode w s x y n).imp ((ArgumentForestProgramSyntax.typedInputs 2 w a b (SyntaxAtomSyntax.two x y)).imp ((SyntaxMixedImageCodeSyntax.termLists w a b c d R S).imp (((MemberProgramSyntax.returned w R S c d s x y q).iff (FormulaTransformAtomSyntax.membership w R S a b c d n q)))))))).close

theorem source_memberResultExistingAtomIff {m} (w R S a b c d s x y n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (memberResultExistingAtomIffSentence w R S a b c d s x y n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMixedImageCodeSyntax.termLists w a b c d R S) (Context.add (ArgumentForestProgramSyntax.typedInputs 2 w a b (SyntaxAtomSyntax.two x y)) (Context.add (SyntaxAtomSyntax.memberCode w s x y n) (Context.add (SyntaxAtomSyntax.zeroScalar w s) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxAtomSyntax.zeroScalar w s) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (SyntaxAtomSyntax.memberCode w s x y n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (ArgumentForestProgramSyntax.typedInputs 2 w a b (SyntaxAtomSyntax.two x y)) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (SyntaxMixedImageCodeSyntax.termLists w a b c d R S) := .hyp (Or.inl rfl)
  exact MemberExistingAtomBridge.iff_existing hZ w R S a b c d s x y n q h0 h1 h2 h3 h4

theorem memberResultExistingAtomIff_kernel_certificate {m} (w R S a b c d s x y n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (memberResultExistingAtomIffSentence w R S a b c d s x y n q)) := TheoryTransport.sentence (source_memberResultExistingAtomIff w R S a b c d s x y n q)

theorem native_memberResultExistingAtomIff {m} (w R S a b c d s x y n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (memberResultExistingAtomIffSentence w R S a b c d s x y n q)) := ZFReplay.replay (memberResultExistingAtomIff_kernel_certificate w R S a b c d s x y n q)

def replaceWholeMemberExistingAtomIffSentence {m} (w mode depth a b c L I R n q x y s : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 3 mode).imp ((OriginalTermTraceSyntax.metadata w depth L).imp ((SyntaxIdentityMapSyntax.identityCode w a I).imp ((IndexTermImageCodeSyntax.converted true w I R a a c).imp ((SyntaxMixedImageCodeSyntax.termList w b a c L).imp ((SyntaxAtomSyntax.zeroScalar w s).imp ((SyntaxAtomSyntax.memberCode w s x y n).imp ((ArgumentForestProgramSyntax.typedInputs 2 w a b (SyntaxAtomSyntax.two x y)).imp (((OriginalTransformRowSyntax.run 3 w mode depth L n q).iff (FormulaTransformAtomSyntax.membership w R L a b a c n q)))))))))))).close

theorem source_replaceWholeMemberExistingAtomIff {m} (w mode depth a b c L I R n q x y s : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (replaceWholeMemberExistingAtomIffSentence w mode depth a b c L I R n q x y s) := by
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
  let Δ : Context m := Context.add (ArgumentForestProgramSyntax.typedInputs 2 w a b (SyntaxAtomSyntax.two x y)) (Context.add (SyntaxAtomSyntax.memberCode w s x y n) (Context.add (SyntaxAtomSyntax.zeroScalar w s) (Context.add (SyntaxMixedImageCodeSyntax.termList w b a c L) (Context.add (IndexTermImageCodeSyntax.converted true w I R a a c) (Context.add (SyntaxIdentityMapSyntax.identityCode w a I) (Context.add (OriginalTermTraceSyntax.metadata w depth L) (Context.add (SyntaxNumeralSyntax.numeral 3 mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))))
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
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 3 mode) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  have h2 : Derives Δ (OriginalTermTraceSyntax.metadata w depth L) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h3 : Derives Δ (SyntaxIdentityMapSyntax.identityCode w a I) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h4 : Derives Δ (IndexTermImageCodeSyntax.converted true w I R a a c) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h5 : Derives Δ (SyntaxMixedImageCodeSyntax.termList w b a c L) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h6 : Derives Δ (SyntaxAtomSyntax.zeroScalar w s) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h7 : Derives Δ (SyntaxAtomSyntax.memberCode w s x y n) := .hyp (Or.inr (Or.inl rfl))
  have h8 : Derives Δ (ArgumentForestProgramSyntax.typedInputs 2 w a b (SyntaxAtomSyntax.two x y)) := .hyp (Or.inl rfl)
  exact OriginalMemberExistingAtom.replace_iff hZ w mode depth a b c L I R n q x y s h0 h1 h2 h3 h4 h5 h6 h7 h8

theorem replaceWholeMemberExistingAtomIff_kernel_certificate {m} (w mode depth a b c L I R n q x y s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (replaceWholeMemberExistingAtomIffSentence w mode depth a b c L I R n q x y s)) := TheoryTransport.sentence (source_replaceWholeMemberExistingAtomIff w mode depth a b c L I R n q x y s)

theorem native_replaceWholeMemberExistingAtomIff {m} (w mode depth a b c L I R n q x y s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (replaceWholeMemberExistingAtomIffSentence w mode depth a b c L I R n q x y s)) := ZFReplay.replay (replaceWholeMemberExistingAtomIff_kernel_certificate w mode depth a b c L I R n q x y s)

def weakenWholeMemberExistingAtomIffSentence {m} (w mode depth parameter a b B I J R S n q x y s : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 0 mode).imp ((OriginalTermTraceSyntax.metadata w depth parameter).imp ((SyntaxIdentityMapSyntax.identityCode w a I).imp ((SyntaxFreeShiftSyntax.shiftCode w b B J).imp ((IndexTermImageCodeSyntax.converted true w I R a a B).imp ((IndexTermImageCodeSyntax.converted false w J S b a B).imp ((SyntaxAtomSyntax.zeroScalar w s).imp ((SyntaxAtomSyntax.memberCode w s x y n).imp ((ArgumentForestProgramSyntax.typedInputs 2 w a b (SyntaxAtomSyntax.two x y)).imp (((OriginalTransformRowSyntax.run 3 w mode depth parameter n q).iff (FormulaTransformAtomSyntax.membership w R S a b a B n q))))))))))))).close

theorem source_weakenWholeMemberExistingAtomIff {m} (w mode depth parameter a b B I J R S n q x y s : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (weakenWholeMemberExistingAtomIffSentence w mode depth parameter a b B I J R S n q x y s) := by
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
  apply Derives.impI
  let Δ : Context m := Context.add (ArgumentForestProgramSyntax.typedInputs 2 w a b (SyntaxAtomSyntax.two x y)) (Context.add (SyntaxAtomSyntax.memberCode w s x y n) (Context.add (SyntaxAtomSyntax.zeroScalar w s) (Context.add (IndexTermImageCodeSyntax.converted false w J S b a B) (Context.add (IndexTermImageCodeSyntax.converted true w I R a a B) (Context.add (SyntaxFreeShiftSyntax.shiftCode w b B J) (Context.add (SyntaxIdentityMapSyntax.identityCode w a I) (Context.add (OriginalTermTraceSyntax.metadata w depth parameter) (Context.add (SyntaxNumeralSyntax.numeral 0 mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))))))
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
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 0 mode) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))
  have h2 : Derives Δ (OriginalTermTraceSyntax.metadata w depth parameter) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  have h3 : Derives Δ (SyntaxIdentityMapSyntax.identityCode w a I) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h4 : Derives Δ (SyntaxFreeShiftSyntax.shiftCode w b B J) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h5 : Derives Δ (IndexTermImageCodeSyntax.converted true w I R a a B) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h6 : Derives Δ (IndexTermImageCodeSyntax.converted false w J S b a B) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h7 : Derives Δ (SyntaxAtomSyntax.zeroScalar w s) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h8 : Derives Δ (SyntaxAtomSyntax.memberCode w s x y n) := .hyp (Or.inr (Or.inl rfl))
  have h9 : Derives Δ (ArgumentForestProgramSyntax.typedInputs 2 w a b (SyntaxAtomSyntax.two x y)) := .hyp (Or.inl rfl)
  exact OriginalMemberExistingAtom.weaken_iff hZ w mode depth parameter a b B I J R S n q x y s h0 h1 h2 h3 h4 h5 h6 h7 h8 h9

theorem weakenWholeMemberExistingAtomIff_kernel_certificate {m} (w mode depth parameter a b B I J R S n q x y s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (weakenWholeMemberExistingAtomIffSentence w mode depth parameter a b B I J R S n q x y s)) := TheoryTransport.sentence (source_weakenWholeMemberExistingAtomIff w mode depth parameter a b B I J R S n q x y s)

theorem native_weakenWholeMemberExistingAtomIff {m} (w mode depth parameter a b B I J R S n q x y s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (weakenWholeMemberExistingAtomIffSentence w mode depth parameter a b B I J R S n q x y s)) := ZFReplay.replay (weakenWholeMemberExistingAtomIff_kernel_certificate w mode depth parameter a b B I J R S n q x y s)

def replaceAllInternalCheckedTermAgreementSentence {m} (w mode depth a b c L I R : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 3 mode).imp ((OriginalTermTraceSyntax.metadata w depth L).imp ((SyntaxIdentityMapSyntax.identityCode w a I).imp ((IndexTermImageCodeSyntax.converted true w I R a a c).imp ((SyntaxMixedImageCodeSyntax.termList w b a c L).imp ((AtomicTermAgreementSyntax.agreement w mode depth L R L a b a c)))))))).close

theorem source_replaceAllInternalCheckedTermAgreement {m} (w mode depth a b c L I R : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (replaceAllInternalCheckedTermAgreementSentence w mode depth a b c L I R) := by
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
  exact AtomicTermAgreement.replace_agreement hZ w mode depth a b c L I R h0 h1 h2 h3 h4 h5

theorem replaceAllInternalCheckedTermAgreement_kernel_certificate {m} (w mode depth a b c L I R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (replaceAllInternalCheckedTermAgreementSentence w mode depth a b c L I R)) := TheoryTransport.sentence (source_replaceAllInternalCheckedTermAgreement w mode depth a b c L I R)

theorem native_replaceAllInternalCheckedTermAgreement {m} (w mode depth a b c L I R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (replaceAllInternalCheckedTermAgreementSentence w mode depth a b c L I R)) := ZFReplay.replay (replaceAllInternalCheckedTermAgreement_kernel_certificate w mode depth a b c L I R)

def weakenAllInternalCheckedTermAgreementSentence {m} (w mode depth parameter a b B I J R S : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 0 mode).imp ((OriginalTermTraceSyntax.metadata w depth parameter).imp ((SyntaxIdentityMapSyntax.identityCode w a I).imp ((SyntaxFreeShiftSyntax.shiftCode w b B J).imp ((IndexTermImageCodeSyntax.converted true w I R a a B).imp ((IndexTermImageCodeSyntax.converted false w J S b a B).imp ((AtomicTermAgreementSyntax.agreement w mode depth parameter R S a b a B))))))))).close

theorem source_weakenAllInternalCheckedTermAgreement {m} (w mode depth parameter a b B I J R S : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (weakenAllInternalCheckedTermAgreementSentence w mode depth parameter a b B I J R S) := by
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
  exact AtomicTermAgreement.weaken_agreement hZ w mode depth parameter a b B I J R S h0 h1 h2 h3 h4 h5 h6

theorem weakenAllInternalCheckedTermAgreement_kernel_certificate {m} (w mode depth parameter a b B I J R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (weakenAllInternalCheckedTermAgreementSentence w mode depth parameter a b B I J R S)) := TheoryTransport.sentence (source_weakenAllInternalCheckedTermAgreement w mode depth parameter a b B I J R S)

theorem native_weakenAllInternalCheckedTermAgreement {m} (w mode depth parameter a b B I J R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (weakenAllInternalCheckedTermAgreementSentence w mode depth parameter a b B I J R S)) := ZFReplay.replay (weakenAllInternalCheckedTermAgreement_kernel_certificate w mode depth parameter a b B I J R S)

def equalityLocalCaseExistingAtomIffSentence {m} (w mode depth parameter R S a b c d x y n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxAtomSyntax.equalCode w x y n).imp ((ArgumentForestProgramSyntax.typedInputs 2 w a b (SyntaxAtomSyntax.two x y)).imp ((AtomicTermAgreementSyntax.agreement w mode depth parameter R S a b c d).imp (((OriginalFormulaCaseSyntax.binaryCase 3 1 w mode depth parameter n q).iff (FormulaTransformAtomSyntax.equality w R S a b c d n q))))))).close

theorem source_equalityLocalCaseExistingAtomIff {m} (w mode depth parameter R S a b c d x y n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (equalityLocalCaseExistingAtomIffSentence w mode depth parameter R S a b c d x y n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (AtomicTermAgreementSyntax.agreement w mode depth parameter R S a b c d) (Context.add (ArgumentForestProgramSyntax.typedInputs 2 w a b (SyntaxAtomSyntax.two x y)) (Context.add (SyntaxAtomSyntax.equalCode w x y n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxAtomSyntax.equalCode w x y n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (ArgumentForestProgramSyntax.typedInputs 2 w a b (SyntaxAtomSyntax.two x y)) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (AtomicTermAgreementSyntax.agreement w mode depth parameter R S a b c d) := .hyp (Or.inl rfl)
  exact EqualityExistingAtomBridge.iff_existing hZ w mode depth parameter R S a b c d x y n q h0 h1 h2 h3

theorem equalityLocalCaseExistingAtomIff_kernel_certificate {m} (w mode depth parameter R S a b c d x y n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (equalityLocalCaseExistingAtomIffSentence w mode depth parameter R S a b c d x y n q)) := TheoryTransport.sentence (source_equalityLocalCaseExistingAtomIff w mode depth parameter R S a b c d x y n q)

theorem native_equalityLocalCaseExistingAtomIff {m} (w mode depth parameter R S a b c d x y n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (equalityLocalCaseExistingAtomIffSentence w mode depth parameter R S a b c d x y n q)) := ZFReplay.replay (equalityLocalCaseExistingAtomIff_kernel_certificate w mode depth parameter R S a b c d x y n q)

def replaceEqualityLocalExistingAtomIffSentence {m} (w mode depth a b c L I R n q x y : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 3 mode).imp ((OriginalTermTraceSyntax.metadata w depth L).imp ((SyntaxIdentityMapSyntax.identityCode w a I).imp ((IndexTermImageCodeSyntax.converted true w I R a a c).imp ((SyntaxMixedImageCodeSyntax.termList w b a c L).imp ((SyntaxAtomSyntax.equalCode w x y n).imp ((ArgumentForestProgramSyntax.typedInputs 2 w a b (SyntaxAtomSyntax.two x y)).imp (((OriginalFormulaCaseSyntax.binaryCase 3 1 w mode depth L n q).iff (FormulaTransformAtomSyntax.equality w R L a b a c n q))))))))))).close

theorem source_replaceEqualityLocalExistingAtomIff {m} (w mode depth a b c L I R n q x y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (replaceEqualityLocalExistingAtomIffSentence w mode depth a b c L I R n q x y) := by
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
  exact OriginalEqualityExistingAtom.replace_case_iff hZ w mode depth a b c L I R n q x y h0 h1 h2 h3 h4 h5 h6 h7

theorem replaceEqualityLocalExistingAtomIff_kernel_certificate {m} (w mode depth a b c L I R n q x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (replaceEqualityLocalExistingAtomIffSentence w mode depth a b c L I R n q x y)) := TheoryTransport.sentence (source_replaceEqualityLocalExistingAtomIff w mode depth a b c L I R n q x y)

theorem native_replaceEqualityLocalExistingAtomIff {m} (w mode depth a b c L I R n q x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (replaceEqualityLocalExistingAtomIffSentence w mode depth a b c L I R n q x y)) := ZFReplay.replay (replaceEqualityLocalExistingAtomIff_kernel_certificate w mode depth a b c L I R n q x y)

def weakenEqualityLocalExistingAtomIffSentence {m} (w mode depth parameter a b B I J R S n q x y : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 0 mode).imp ((OriginalTermTraceSyntax.metadata w depth parameter).imp ((SyntaxIdentityMapSyntax.identityCode w a I).imp ((SyntaxFreeShiftSyntax.shiftCode w b B J).imp ((IndexTermImageCodeSyntax.converted true w I R a a B).imp ((IndexTermImageCodeSyntax.converted false w J S b a B).imp ((SyntaxAtomSyntax.equalCode w x y n).imp ((ArgumentForestProgramSyntax.typedInputs 2 w a b (SyntaxAtomSyntax.two x y)).imp (((OriginalFormulaCaseSyntax.binaryCase 3 1 w mode depth parameter n q).iff (FormulaTransformAtomSyntax.equality w R S a b a B n q)))))))))))).close

theorem source_weakenEqualityLocalExistingAtomIff {m} (w mode depth parameter a b B I J R S n q x y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (weakenEqualityLocalExistingAtomIffSentence w mode depth parameter a b B I J R S n q x y) := by
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
  exact OriginalEqualityExistingAtom.weaken_case_iff hZ w mode depth parameter a b B I J R S n q x y h0 h1 h2 h3 h4 h5 h6 h7 h8

theorem weakenEqualityLocalExistingAtomIff_kernel_certificate {m} (w mode depth parameter a b B I J R S n q x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (weakenEqualityLocalExistingAtomIffSentence w mode depth parameter a b B I J R S n q x y)) := TheoryTransport.sentence (source_weakenEqualityLocalExistingAtomIff w mode depth parameter a b B I J R S n q x y)

theorem native_weakenEqualityLocalExistingAtomIff {m} (w mode depth parameter a b B I J R S n q x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (weakenEqualityLocalExistingAtomIffSentence w mode depth parameter a b B I J R S n q x y)) := ZFReplay.replay (weakenEqualityLocalExistingAtomIff_kernel_certificate w mode depth parameter a b B I J R S n q x y)

def constantDataExistingAtomIffSentence {m} (truth : Bool) (w a b c d n q : Fin m) : Source.Sentence := ((SyntaxTermSyntax.contexts w a b).imp ((SyntaxTermSyntax.contexts w c d).imp (((OriginalFormulaLocalData.constant (SyntaxAtomSyntax.nullaryTag truth) w n q).iff (FormulaTransformAtomSyntax.nullary truth w a b c d n q))))).close

theorem source_constantDataExistingAtomIff {m} (truth : Bool) (w a b c d n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (constantDataExistingAtomIffSentence truth w a b c d n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTermSyntax.contexts w c d) (Context.add (SyntaxTermSyntax.contexts w a b) (Source.SetLanguage.ZF.at m))
  have h0 : Derives Δ (SyntaxTermSyntax.contexts w a b) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxTermSyntax.contexts w c d) := .hyp (Or.inl rfl)
  exact ConstantExistingAtomBridge.constant_iff truth w a b c d n q h0 h1

theorem constantDataExistingAtomIff_kernel_certificate {m} (truth : Bool) (w a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (constantDataExistingAtomIffSentence truth w a b c d n q)) := TheoryTransport.sentence (source_constantDataExistingAtomIff truth w a b c d n q)

theorem native_constantDataExistingAtomIff {m} (truth : Bool) (w a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (constantDataExistingAtomIffSentence truth w a b c d n q)) := ZFReplay.replay (constantDataExistingAtomIff_kernel_certificate truth w a b c d n q)

end PPAC.Migration.Internal.ObjectExistingAtomicInterfaces
