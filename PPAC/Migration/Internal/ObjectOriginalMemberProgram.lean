import PPAC.Migration.Internal.OriginalMemberProgram

/-! 原mode0／3完整成员公式Run₃与独立项程序的全候选输出对象闭句。 -/
namespace PPAC.Migration.Internal.ObjectOriginalMemberProgram
open Source SourceAlgebra SourceLogic OmegaSyntax
open YesMetaZFC.Automation.ObjectHorn (Rule)

def replaceMemberPairAllInternalAgreementSentence {m} (w mode depth a b c L I R x y : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 3 mode).imp ((OriginalTermTraceSyntax.metadata w depth L).imp ((SyntaxIdentityMapSyntax.identityCode w a I).imp ((IndexTermImageCodeSyntax.converted true w I R a a c).imp ((SyntaxMixedImageCodeSyntax.termList w b a c L).imp ((ArgumentForestProgramSyntax.typedInputs 2 w a b (SyntaxAtomSyntax.two x y)).imp ((MemberPairAgreementSyntax.agreement w mode depth L R L a c x y))))))))).close

theorem source_replaceMemberPairAllInternalAgreement {m} (w mode depth a b c L I R x y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (replaceMemberPairAllInternalAgreementSentence w mode depth a b c L I R x y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ArgumentForestProgramSyntax.typedInputs 2 w a b (SyntaxAtomSyntax.two x y)) (Context.add (SyntaxMixedImageCodeSyntax.termList w b a c L) (Context.add (IndexTermImageCodeSyntax.converted true w I R a a c) (Context.add (SyntaxIdentityMapSyntax.identityCode w a I) (Context.add (OriginalTermTraceSyntax.metadata w depth L) (Context.add (SyntaxNumeralSyntax.numeral 3 mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))
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
  have h6 : Derives Δ (ArgumentForestProgramSyntax.typedInputs 2 w a b (SyntaxAtomSyntax.two x y)) := .hyp (Or.inl rfl)
  exact MemberPairAgreement.replace_agreement hZ w mode depth a b c L I R x y h0 h1 h2 h3 h4 h5 h6

theorem replaceMemberPairAllInternalAgreement_kernel_certificate {m} (w mode depth a b c L I R x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (replaceMemberPairAllInternalAgreementSentence w mode depth a b c L I R x y)) := TheoryTransport.sentence (source_replaceMemberPairAllInternalAgreement w mode depth a b c L I R x y)

theorem native_replaceMemberPairAllInternalAgreement {m} (w mode depth a b c L I R x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (replaceMemberPairAllInternalAgreementSentence w mode depth a b c L I R x y)) := ZFReplay.replay (replaceMemberPairAllInternalAgreement_kernel_certificate w mode depth a b c L I R x y)

def weakenMemberPairAllInternalAgreementSentence {m} (w mode depth parameter a b B I J R S x y : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 0 mode).imp ((OriginalTermTraceSyntax.metadata w depth parameter).imp ((SyntaxIdentityMapSyntax.identityCode w a I).imp ((SyntaxFreeShiftSyntax.shiftCode w b B J).imp ((IndexTermImageCodeSyntax.converted true w I R a a B).imp ((IndexTermImageCodeSyntax.converted false w J S b a B).imp ((ArgumentForestProgramSyntax.typedInputs 2 w a b (SyntaxAtomSyntax.two x y)).imp ((MemberPairAgreementSyntax.agreement w mode depth parameter R S a B x y)))))))))).close

theorem source_weakenMemberPairAllInternalAgreement {m} (w mode depth parameter a b B I J R S x y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (weakenMemberPairAllInternalAgreementSentence w mode depth parameter a b B I J R S x y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ArgumentForestProgramSyntax.typedInputs 2 w a b (SyntaxAtomSyntax.two x y)) (Context.add (IndexTermImageCodeSyntax.converted false w J S b a B) (Context.add (IndexTermImageCodeSyntax.converted true w I R a a B) (Context.add (SyntaxFreeShiftSyntax.shiftCode w b B J) (Context.add (SyntaxIdentityMapSyntax.identityCode w a I) (Context.add (OriginalTermTraceSyntax.metadata w depth parameter) (Context.add (SyntaxNumeralSyntax.numeral 0 mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))))
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
  have h7 : Derives Δ (ArgumentForestProgramSyntax.typedInputs 2 w a b (SyntaxAtomSyntax.two x y)) := .hyp (Or.inl rfl)
  exact MemberPairAgreement.weaken_agreement hZ w mode depth parameter a b B I J R S x y h0 h1 h2 h3 h4 h5 h6 h7

theorem weakenMemberPairAllInternalAgreement_kernel_certificate {m} (w mode depth parameter a b B I J R S x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (weakenMemberPairAllInternalAgreementSentence w mode depth parameter a b B I J R S x y)) := TheoryTransport.sentence (source_weakenMemberPairAllInternalAgreement w mode depth parameter a b B I J R S x y)

theorem native_weakenMemberPairAllInternalAgreement {m} (w mode depth parameter a b B I J R S x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (weakenMemberPairAllInternalAgreementSentence w mode depth parameter a b B I J R S x y)) := ZFReplay.replay (weakenMemberPairAllInternalAgreement_kernel_certificate w mode depth parameter a b B I J R S x y)

def originalMemberWholeElevenCaseDispatchIffSentence {m} (w mode depth parameter s x y n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxAtomSyntax.memberCode w s x y n).imp (((OriginalFormulaTraceEquation.outcomes w mode depth parameter n q).iff (OriginalFormulaCaseSyntax.applicationCase w mode depth parameter n q))))).close

theorem source_originalMemberWholeElevenCaseDispatchIff {m} (w mode depth parameter s x y n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalMemberWholeElevenCaseDispatchIffSentence w mode depth parameter s x y n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxAtomSyntax.memberCode w s x y n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxAtomSyntax.memberCode w s x y n) := .hyp (Or.inl rfl)
  exact OriginalMemberRunDispatch.outcomes_iff_application hZ w mode depth parameter s x y n q h0 h1

theorem originalMemberWholeElevenCaseDispatchIff_kernel_certificate {m} (w mode depth parameter s x y n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalMemberWholeElevenCaseDispatchIffSentence w mode depth parameter s x y n q)) := TheoryTransport.sentence (source_originalMemberWholeElevenCaseDispatchIff w mode depth parameter s x y n q)

theorem native_originalMemberWholeElevenCaseDispatchIff {m} (w mode depth parameter s x y n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalMemberWholeElevenCaseDispatchIffSentence w mode depth parameter s x y n q)) := ZFReplay.replay (originalMemberWholeElevenCaseDispatchIff_kernel_certificate w mode depth parameter s x y n q)

def originalMemberWholeRunApplicationIffSentence {m} (three : Bool) (w mode depth parameter s x y n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode).imp ((Formula.mem depth w).imp ((Formula.mem parameter w).imp ((SyntaxAtomSyntax.memberCode w s x y n).imp (((OriginalTransformRowSyntax.run 3 w mode depth parameter n q).iff (OriginalFormulaCaseSyntax.applicationCase w mode depth parameter n q)))))))).close

theorem source_originalMemberWholeRunApplicationIff {m} (three : Bool) (w mode depth parameter s x y n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalMemberWholeRunApplicationIffSentence three w mode depth parameter s x y n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxAtomSyntax.memberCode w s x y n) (Context.add (Formula.mem parameter w) (Context.add (Formula.mem depth w) (Context.add (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (Formula.mem depth w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (Formula.mem parameter w) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (SyntaxAtomSyntax.memberCode w s x y n) := .hyp (Or.inl rfl)
  exact OriginalMemberRunDispatch.run_iff_application hZ three w mode depth parameter s x y n q h0 h1 h2 h3 h4

theorem originalMemberWholeRunApplicationIff_kernel_certificate {m} (three : Bool) (w mode depth parameter s x y n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalMemberWholeRunApplicationIffSentence three w mode depth parameter s x y n q)) := TheoryTransport.sentence (source_originalMemberWholeRunApplicationIff three w mode depth parameter s x y n q)

theorem native_originalMemberWholeRunApplicationIff {m} (three : Bool) (w mode depth parameter s x y n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalMemberWholeRunApplicationIffSentence three w mode depth parameter s x y n q)) := ZFReplay.replay (originalMemberWholeRunApplicationIff_kernel_certificate three w mode depth parameter s x y n q)

def originalMembershipCaseProgramIffSentence {m} (w mode depth parameter R S c d s x y q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxAtomSyntax.zeroScalar w s).imp ((SyntaxForestSyntax.inputs 2 w (SyntaxAtomSyntax.two x y)).imp ((MemberPairAgreementSyntax.agreement w mode depth parameter R S c d x y).imp (((OriginalFormulaMemberCaseSyntax.membershipCase w mode depth parameter x y q).iff (MemberProgramSyntax.returned w R S c d s x y q))))))).close

theorem source_originalMembershipCaseProgramIff {m} (w mode depth parameter R S c d s x y q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalMembershipCaseProgramIffSentence w mode depth parameter R S c d s x y q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (MemberPairAgreementSyntax.agreement w mode depth parameter R S c d x y) (Context.add (SyntaxForestSyntax.inputs 2 w (SyntaxAtomSyntax.two x y)) (Context.add (SyntaxAtomSyntax.zeroScalar w s) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxAtomSyntax.zeroScalar w s) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxForestSyntax.inputs 2 w (SyntaxAtomSyntax.two x y)) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (MemberPairAgreementSyntax.agreement w mode depth parameter R S c d x y) := .hyp (Or.inl rfl)
  exact MemberProgramCase.membership_iff hZ w mode depth parameter R S c d s x y q h0 h1 h2 h3

theorem originalMembershipCaseProgramIff_kernel_certificate {m} (w mode depth parameter R S c d s x y q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalMembershipCaseProgramIffSentence w mode depth parameter R S c d s x y q)) := TheoryTransport.sentence (source_originalMembershipCaseProgramIff w mode depth parameter R S c d s x y q)

theorem native_originalMembershipCaseProgramIff {m} (w mode depth parameter R S c d s x y q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalMembershipCaseProgramIffSentence w mode depth parameter R S c d s x y q)) := ZFReplay.replay (originalMembershipCaseProgramIff_kernel_certificate w mode depth parameter R S c d s x y q)

def originalMemberApplicationProgramIffSentence {m} (w mode depth parameter R S c d s x y n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxAtomSyntax.zeroScalar w s).imp ((SyntaxAtomSyntax.memberCode w s x y n).imp ((SyntaxForestSyntax.inputs 2 w (SyntaxAtomSyntax.two x y)).imp ((MemberPairAgreementSyntax.agreement w mode depth parameter R S c d x y).imp (((OriginalFormulaCaseSyntax.applicationCase w mode depth parameter n q).iff (MemberProgramSyntax.returned w R S c d s x y q)))))))).close

theorem source_originalMemberApplicationProgramIff {m} (w mode depth parameter R S c d s x y n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalMemberApplicationProgramIffSentence w mode depth parameter R S c d s x y n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (MemberPairAgreementSyntax.agreement w mode depth parameter R S c d x y) (Context.add (SyntaxForestSyntax.inputs 2 w (SyntaxAtomSyntax.two x y)) (Context.add (SyntaxAtomSyntax.memberCode w s x y n) (Context.add (SyntaxAtomSyntax.zeroScalar w s) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
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
  have h3 : Derives Δ (SyntaxForestSyntax.inputs 2 w (SyntaxAtomSyntax.two x y)) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (MemberPairAgreementSyntax.agreement w mode depth parameter R S c d x y) := .hyp (Or.inl rfl)
  exact MemberProgramCase.application_iff hZ w mode depth parameter R S c d s x y n q h0 h1 h2 h3 h4

theorem originalMemberApplicationProgramIff_kernel_certificate {m} (w mode depth parameter R S c d s x y n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalMemberApplicationProgramIffSentence w mode depth parameter R S c d s x y n q)) := TheoryTransport.sentence (source_originalMemberApplicationProgramIff w mode depth parameter R S c d s x y n q)

theorem native_originalMemberApplicationProgramIff {m} (w mode depth parameter R S c d s x y n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalMemberApplicationProgramIffSentence w mode depth parameter R S c d s x y n q)) := ZFReplay.replay (originalMemberApplicationProgramIff_kernel_certificate w mode depth parameter R S c d s x y n q)

def replaceOriginalMemberApplicationProgramIffSentence {m} (w mode depth a b c L I R n q x y s : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 3 mode).imp ((OriginalTermTraceSyntax.metadata w depth L).imp ((SyntaxIdentityMapSyntax.identityCode w a I).imp ((IndexTermImageCodeSyntax.converted true w I R a a c).imp ((SyntaxMixedImageCodeSyntax.termList w b a c L).imp ((SyntaxAtomSyntax.zeroScalar w s).imp ((SyntaxAtomSyntax.memberCode w s x y n).imp ((ArgumentForestProgramSyntax.typedInputs 2 w a b (SyntaxAtomSyntax.two x y)).imp (((OriginalFormulaCaseSyntax.applicationCase w mode depth L n q).iff (MemberProgramSyntax.returned w R L a c s x y q)))))))))))).close

theorem source_replaceOriginalMemberApplicationProgramIff {m} (w mode depth a b c L I R n q x y s : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (replaceOriginalMemberApplicationProgramIffSentence w mode depth a b c L I R n q x y s) := by
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
  exact OriginalMemberProgram.replace_application_iff hZ w mode depth a b c L I R n q x y s h0 h1 h2 h3 h4 h5 h6 h7 h8

theorem replaceOriginalMemberApplicationProgramIff_kernel_certificate {m} (w mode depth a b c L I R n q x y s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (replaceOriginalMemberApplicationProgramIffSentence w mode depth a b c L I R n q x y s)) := TheoryTransport.sentence (source_replaceOriginalMemberApplicationProgramIff w mode depth a b c L I R n q x y s)

theorem native_replaceOriginalMemberApplicationProgramIff {m} (w mode depth a b c L I R n q x y s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (replaceOriginalMemberApplicationProgramIffSentence w mode depth a b c L I R n q x y s)) := ZFReplay.replay (replaceOriginalMemberApplicationProgramIff_kernel_certificate w mode depth a b c L I R n q x y s)

def replaceOriginalMemberWholeRunProgramIffSentence {m} (w mode depth a b c L I R n q x y s : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 3 mode).imp ((OriginalTermTraceSyntax.metadata w depth L).imp ((SyntaxIdentityMapSyntax.identityCode w a I).imp ((IndexTermImageCodeSyntax.converted true w I R a a c).imp ((SyntaxMixedImageCodeSyntax.termList w b a c L).imp ((SyntaxAtomSyntax.zeroScalar w s).imp ((SyntaxAtomSyntax.memberCode w s x y n).imp ((ArgumentForestProgramSyntax.typedInputs 2 w a b (SyntaxAtomSyntax.two x y)).imp (((OriginalTransformRowSyntax.run 3 w mode depth L n q).iff (MemberProgramSyntax.returned w R L a c s x y q)))))))))))).close

theorem source_replaceOriginalMemberWholeRunProgramIff {m} (w mode depth a b c L I R n q x y s : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (replaceOriginalMemberWholeRunProgramIffSentence w mode depth a b c L I R n q x y s) := by
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
  exact OriginalMemberProgram.replace_run_iff hZ w mode depth a b c L I R n q x y s h0 h1 h2 h3 h4 h5 h6 h7 h8

theorem replaceOriginalMemberWholeRunProgramIff_kernel_certificate {m} (w mode depth a b c L I R n q x y s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (replaceOriginalMemberWholeRunProgramIffSentence w mode depth a b c L I R n q x y s)) := TheoryTransport.sentence (source_replaceOriginalMemberWholeRunProgramIff w mode depth a b c L I R n q x y s)

theorem native_replaceOriginalMemberWholeRunProgramIff {m} (w mode depth a b c L I R n q x y s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (replaceOriginalMemberWholeRunProgramIffSentence w mode depth a b c L I R n q x y s)) := ZFReplay.replay (replaceOriginalMemberWholeRunProgramIff_kernel_certificate w mode depth a b c L I R n q x y s)

def weakenOriginalMemberApplicationProgramIffSentence {m} (w mode depth parameter a b B I J R S n q x y s : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 0 mode).imp ((OriginalTermTraceSyntax.metadata w depth parameter).imp ((SyntaxIdentityMapSyntax.identityCode w a I).imp ((SyntaxFreeShiftSyntax.shiftCode w b B J).imp ((IndexTermImageCodeSyntax.converted true w I R a a B).imp ((IndexTermImageCodeSyntax.converted false w J S b a B).imp ((SyntaxAtomSyntax.zeroScalar w s).imp ((SyntaxAtomSyntax.memberCode w s x y n).imp ((ArgumentForestProgramSyntax.typedInputs 2 w a b (SyntaxAtomSyntax.two x y)).imp (((OriginalFormulaCaseSyntax.applicationCase w mode depth parameter n q).iff (MemberProgramSyntax.returned w R S a B s x y q))))))))))))).close

theorem source_weakenOriginalMemberApplicationProgramIff {m} (w mode depth parameter a b B I J R S n q x y s : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (weakenOriginalMemberApplicationProgramIffSentence w mode depth parameter a b B I J R S n q x y s) := by
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
  exact OriginalMemberProgram.weaken_application_iff hZ w mode depth parameter a b B I J R S n q x y s h0 h1 h2 h3 h4 h5 h6 h7 h8 h9

theorem weakenOriginalMemberApplicationProgramIff_kernel_certificate {m} (w mode depth parameter a b B I J R S n q x y s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (weakenOriginalMemberApplicationProgramIffSentence w mode depth parameter a b B I J R S n q x y s)) := TheoryTransport.sentence (source_weakenOriginalMemberApplicationProgramIff w mode depth parameter a b B I J R S n q x y s)

theorem native_weakenOriginalMemberApplicationProgramIff {m} (w mode depth parameter a b B I J R S n q x y s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (weakenOriginalMemberApplicationProgramIffSentence w mode depth parameter a b B I J R S n q x y s)) := ZFReplay.replay (weakenOriginalMemberApplicationProgramIff_kernel_certificate w mode depth parameter a b B I J R S n q x y s)

def weakenOriginalMemberWholeRunProgramIffSentence {m} (w mode depth parameter a b B I J R S n q x y s : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 0 mode).imp ((OriginalTermTraceSyntax.metadata w depth parameter).imp ((SyntaxIdentityMapSyntax.identityCode w a I).imp ((SyntaxFreeShiftSyntax.shiftCode w b B J).imp ((IndexTermImageCodeSyntax.converted true w I R a a B).imp ((IndexTermImageCodeSyntax.converted false w J S b a B).imp ((SyntaxAtomSyntax.zeroScalar w s).imp ((SyntaxAtomSyntax.memberCode w s x y n).imp ((ArgumentForestProgramSyntax.typedInputs 2 w a b (SyntaxAtomSyntax.two x y)).imp (((OriginalTransformRowSyntax.run 3 w mode depth parameter n q).iff (MemberProgramSyntax.returned w R S a B s x y q))))))))))))).close

theorem source_weakenOriginalMemberWholeRunProgramIff {m} (w mode depth parameter a b B I J R S n q x y s : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (weakenOriginalMemberWholeRunProgramIffSentence w mode depth parameter a b B I J R S n q x y s) := by
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
  exact OriginalMemberProgram.weaken_run_iff hZ w mode depth parameter a b B I J R S n q x y s h0 h1 h2 h3 h4 h5 h6 h7 h8 h9

theorem weakenOriginalMemberWholeRunProgramIff_kernel_certificate {m} (w mode depth parameter a b B I J R S n q x y s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (weakenOriginalMemberWholeRunProgramIffSentence w mode depth parameter a b B I J R S n q x y s)) := TheoryTransport.sentence (source_weakenOriginalMemberWholeRunProgramIff w mode depth parameter a b B I J R S n q x y s)

theorem native_weakenOriginalMemberWholeRunProgramIff {m} (w mode depth parameter a b B I J R S n q x y s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (weakenOriginalMemberWholeRunProgramIffSentence w mode depth parameter a b B I J R S n q x y s)) := ZFReplay.replay (weakenOriginalMemberWholeRunProgramIff_kernel_certificate w mode depth parameter a b B I J R S n q x y s)

end PPAC.Migration.Internal.ObjectOriginalMemberProgram
