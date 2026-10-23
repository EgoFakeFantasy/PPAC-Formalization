import PPAC.Migration.Internal.EqualityExistingAtomBridge

/-! 原mode0／3等词局部二元分支实际接入既有等词项程序；比较前提已推导。 -/
namespace PPAC.Migration.Internal.OriginalEqualityExistingAtom
open Source SourceAlgebra SourceLogic OmegaSyntax

theorem replace_case_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w mode depth a b c L I R n q x y : Fin m)
    (h0 : Derives Γ (omega w))
    (h1 : Derives Γ (SyntaxNumeralSyntax.numeral 3 mode))
    (h2 : Derives Γ (OriginalTermTraceSyntax.metadata w depth L))
    (h3 : Derives Γ (SyntaxIdentityMapSyntax.identityCode w a I))
    (h4 : Derives Γ (IndexTermImageCodeSyntax.converted true w I R a a c))
    (h5 : Derives Γ (SyntaxMixedImageCodeSyntax.termList w b a c L))
    (hn : Derives Γ (SyntaxAtomSyntax.equalCode w x y n))
    (hT : Derives Γ (ArgumentForestProgramSyntax.typedInputs 2 w a b (SyntaxAtomSyntax.two x y))) :
    Derives Γ ((OriginalFormulaCaseSyntax.binaryCase 3 1 w mode depth L n q).iff (FormulaTransformAtomSyntax.equality w R L a b a c n q)) := by
  have ha := AtomicTermAgreement.replace_agreement hZ w mode depth a b c L I R h0 h1 h2 h3 h4 h5
  exact EqualityExistingAtomBridge.iff_existing hZ w mode depth L R L a b a c x y n q h0 hn hT ha

theorem weaken_case_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w mode depth parameter a b B I J R S n q x y : Fin m)
    (h0 : Derives Γ (omega w))
    (h1 : Derives Γ (SyntaxNumeralSyntax.numeral 0 mode))
    (h2 : Derives Γ (OriginalTermTraceSyntax.metadata w depth parameter))
    (h3 : Derives Γ (SyntaxIdentityMapSyntax.identityCode w a I))
    (h4 : Derives Γ (SyntaxFreeShiftSyntax.shiftCode w b B J))
    (h5 : Derives Γ (IndexTermImageCodeSyntax.converted true w I R a a B))
    (h6 : Derives Γ (IndexTermImageCodeSyntax.converted false w J S b a B))
    (hn : Derives Γ (SyntaxAtomSyntax.equalCode w x y n))
    (hT : Derives Γ (ArgumentForestProgramSyntax.typedInputs 2 w a b (SyntaxAtomSyntax.two x y))) :
    Derives Γ ((OriginalFormulaCaseSyntax.binaryCase 3 1 w mode depth parameter n q).iff (FormulaTransformAtomSyntax.equality w R S a b a B n q)) := by
  have ha := AtomicTermAgreement.weaken_agreement hZ w mode depth parameter a b B I J R S h0 h1 h2 h3 h4 h5 h6
  exact EqualityExistingAtomBridge.iff_existing hZ w mode depth parameter R S a b a B x y n q h0 hn hT ha

end PPAC.Migration.Internal.OriginalEqualityExistingAtom
