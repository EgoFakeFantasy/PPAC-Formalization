import PPAC.Migration.Internal.OriginalMemberRunDispatch

/-! 原mode0／3完整Run₃在纯成员输入处，与独立项程序成员分支对全部内部输出双向对应。 -/
namespace PPAC.Migration.Internal.OriginalMemberProgram
open Source SourceAlgebra SourceLogic OmegaSyntax

theorem replace_application_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w mode depth a b c L I R n q x y s : Fin m)
    (h0 : Derives Γ (omega w))
    (h1 : Derives Γ (SyntaxNumeralSyntax.numeral 3 mode))
    (h2 : Derives Γ (OriginalTermTraceSyntax.metadata w depth L))
    (h3 : Derives Γ (SyntaxIdentityMapSyntax.identityCode w a I))
    (h4 : Derives Γ (IndexTermImageCodeSyntax.converted true w I R a a c))
    (h5 : Derives Γ (SyntaxMixedImageCodeSyntax.termList w b a c L))
    (hs : Derives Γ (SyntaxAtomSyntax.zeroScalar w s))
    (hn : Derives Γ (SyntaxAtomSyntax.memberCode w s x y n))
    (hT : Derives Γ (ArgumentForestProgramSyntax.typedInputs 2 w a b (SyntaxAtomSyntax.two x y))) :
    Derives Γ ((OriginalFormulaCaseSyntax.applicationCase w mode depth L n q).iff (MemberProgramSyntax.returned w R L a c s x y q)) := by
  have hAgreement := MemberPairAgreement.replace_agreement hZ w mode depth a b c L I R x y h0 h1 h2 h3 h4 h5 hT
  have hInputs := MemberProgramSyntax.inputs_from_types hZ w a b x y h0 hT
  exact MemberProgramCase.application_iff hZ w mode depth L R L a c s x y n q h0 hs hn hInputs hAgreement

theorem replace_run_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w mode depth a b c L I R n q x y s : Fin m)
    (h0 : Derives Γ (omega w))
    (h1 : Derives Γ (SyntaxNumeralSyntax.numeral 3 mode))
    (h2 : Derives Γ (OriginalTermTraceSyntax.metadata w depth L))
    (h3 : Derives Γ (SyntaxIdentityMapSyntax.identityCode w a I))
    (h4 : Derives Γ (IndexTermImageCodeSyntax.converted true w I R a a c))
    (h5 : Derives Γ (SyntaxMixedImageCodeSyntax.termList w b a c L))
    (hs : Derives Γ (SyntaxAtomSyntax.zeroScalar w s))
    (hn : Derives Γ (SyntaxAtomSyntax.memberCode w s x y n))
    (hT : Derives Γ (ArgumentForestProgramSyntax.typedInputs 2 w a b (SyntaxAtomSyntax.two x y))) :
    Derives Γ ((OriginalTransformRowSyntax.run 3 w mode depth L n q).iff (MemberProgramSyntax.returned w R L a c s x y q)) := by
  have hDispatch := OriginalMemberRunDispatch.run_iff_application hZ true w mode depth L s x y n q h0 h1 (.conjL h2) (.conjR h2) hn
  exact SyntaxTypeLocalTransfer.iff_trans hDispatch (replace_application_iff hZ w mode depth a b c L I R n q x y s h0 h1 h2 h3 h4 h5 hs hn hT)

theorem weaken_application_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w mode depth parameter a b B I J R S n q x y s : Fin m)
    (h0 : Derives Γ (omega w))
    (h1 : Derives Γ (SyntaxNumeralSyntax.numeral 0 mode))
    (h2 : Derives Γ (OriginalTermTraceSyntax.metadata w depth parameter))
    (h3 : Derives Γ (SyntaxIdentityMapSyntax.identityCode w a I))
    (h4 : Derives Γ (SyntaxFreeShiftSyntax.shiftCode w b B J))
    (h5 : Derives Γ (IndexTermImageCodeSyntax.converted true w I R a a B))
    (h6 : Derives Γ (IndexTermImageCodeSyntax.converted false w J S b a B))
    (hs : Derives Γ (SyntaxAtomSyntax.zeroScalar w s))
    (hn : Derives Γ (SyntaxAtomSyntax.memberCode w s x y n))
    (hT : Derives Γ (ArgumentForestProgramSyntax.typedInputs 2 w a b (SyntaxAtomSyntax.two x y))) :
    Derives Γ ((OriginalFormulaCaseSyntax.applicationCase w mode depth parameter n q).iff (MemberProgramSyntax.returned w R S a B s x y q)) := by
  have hAgreement := MemberPairAgreement.weaken_agreement hZ w mode depth parameter a b B I J R S x y h0 h1 h2 h3 h4 h5 h6 hT
  have hInputs := MemberProgramSyntax.inputs_from_types hZ w a b x y h0 hT
  exact MemberProgramCase.application_iff hZ w mode depth parameter R S a B s x y n q h0 hs hn hInputs hAgreement

theorem weaken_run_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w mode depth parameter a b B I J R S n q x y s : Fin m)
    (h0 : Derives Γ (omega w))
    (h1 : Derives Γ (SyntaxNumeralSyntax.numeral 0 mode))
    (h2 : Derives Γ (OriginalTermTraceSyntax.metadata w depth parameter))
    (h3 : Derives Γ (SyntaxIdentityMapSyntax.identityCode w a I))
    (h4 : Derives Γ (SyntaxFreeShiftSyntax.shiftCode w b B J))
    (h5 : Derives Γ (IndexTermImageCodeSyntax.converted true w I R a a B))
    (h6 : Derives Γ (IndexTermImageCodeSyntax.converted false w J S b a B))
    (hs : Derives Γ (SyntaxAtomSyntax.zeroScalar w s))
    (hn : Derives Γ (SyntaxAtomSyntax.memberCode w s x y n))
    (hT : Derives Γ (ArgumentForestProgramSyntax.typedInputs 2 w a b (SyntaxAtomSyntax.two x y))) :
    Derives Γ ((OriginalTransformRowSyntax.run 3 w mode depth parameter n q).iff (MemberProgramSyntax.returned w R S a B s x y q)) := by
  have hDispatch := OriginalMemberRunDispatch.run_iff_application hZ false w mode depth parameter s x y n q h0 h1 (.conjL h2) (.conjR h2) hn
  exact SyntaxTypeLocalTransfer.iff_trans hDispatch (weaken_application_iff hZ w mode depth parameter a b B I J R S n q x y s h0 h1 h2 h3 h4 h5 h6 hs hn hT)

end PPAC.Migration.Internal.OriginalMemberProgram
