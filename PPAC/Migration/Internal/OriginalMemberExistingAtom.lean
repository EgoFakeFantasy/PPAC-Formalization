import PPAC.Migration.Internal.MemberExistingAtomBridge

/-! 原mode0／3完整成员Run₃实际接入既有FormulaTransformAtomSyntax.membership。 -/
namespace PPAC.Migration.Internal.OriginalMemberExistingAtom
open Source SourceAlgebra SourceLogic OmegaSyntax

theorem replace_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
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
    Derives Γ ((OriginalTransformRowSyntax.run 3 w mode depth L n q).iff (FormulaTransformAtomSyntax.membership w R L a b a c n q)) := by
  have hR := IndexTermImageCodeTyping.term_list true w I R a a c h4
  have hMaps : Derives Γ (SyntaxMixedImageCodeSyntax.termLists w a b a c R L) := .conjI hR h5
  exact SyntaxTypeLocalTransfer.iff_trans (OriginalMemberProgram.replace_run_iff hZ w mode depth a b c L I R n q x y s h0 h1 h2 h3 h4 h5 hs hn hT)
    (MemberExistingAtomBridge.iff_existing hZ w R L a b a c s x y n q h0 hs hn hT hMaps)

theorem weaken_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
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
    Derives Γ ((OriginalTransformRowSyntax.run 3 w mode depth parameter n q).iff (FormulaTransformAtomSyntax.membership w R S a b a B n q)) := by
  have hR := IndexTermImageCodeTyping.term_list true w I R a a B h5
  have hS := IndexTermImageCodeTyping.term_list false w J S b a B h6
  have hMaps : Derives Γ (SyntaxMixedImageCodeSyntax.termLists w a b a B R S) := .conjI hR hS
  exact SyntaxTypeLocalTransfer.iff_trans (OriginalMemberProgram.weaken_run_iff hZ w mode depth parameter a b B I J R S n q x y s h0 h1 h2 h3 h4 h5 h6 hs hn hT)
    (MemberExistingAtomBridge.iff_existing hZ w R S a b a B s x y n q h0 hs hn hT hMaps)

end PPAC.Migration.Internal.OriginalMemberExistingAtom
