import PPAC.Migration.Internal.OriginalArgumentValueInduction

/-! 全内部列表实际唯一输出特化到原mode3替换与mode0弱化，头Promise由实际环境消去。 -/
namespace PPAC.Migration.Internal.OriginalArgumentModeFiber
open Source SourceAlgebra SourceLogic OmegaSyntax OriginalArgumentValueSyntax

theorem replace_fiber {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w mode depth a b c L I R n k : Fin m)
    (h0 : Derives Γ (omega w))
    (h1 : Derives Γ (SyntaxNumeralSyntax.numeral 3 mode))
    (h2 : Derives Γ (OriginalTermTraceSyntax.metadata w depth L))
    (h3 : Derives Γ (SyntaxIdentityMapSyntax.identityCode w a I))
    (h4 : Derives Γ (IndexTermImageCodeSyntax.converted true w I R a a c))
    (h5 : Derives Γ (SyntaxMixedImageCodeSyntax.termList w b a c L))
    (hL : Derives Γ (SyntaxMixedImageCodeSyntax.termList w k a b n))
    : Derives Γ (fiber w mode depth L k a c n) := by
  have hpr := OriginalNumericTermFiber.replace_promise hZ w mode depth a b c L I R h0 h1 h2 h3 h4 h5
  have hc : Derives Γ (SyntaxTermSyntax.contexts w a c) := .conjL (.conjR (IndexTermImageCodeTyping.term_list true w I R a a c h4))
  exact OriginalArgumentValueInduction.actual_fiber hZ true w mode depth L a b a c n k h0 h1 (.conjL h2) (.conjR h2) hc hpr hL

theorem weaken_fiber {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w mode depth parameter a b B I J R S n k : Fin m)
    (h0 : Derives Γ (omega w))
    (h1 : Derives Γ (SyntaxNumeralSyntax.numeral 0 mode))
    (h2 : Derives Γ (OriginalTermTraceSyntax.metadata w depth parameter))
    (h3 : Derives Γ (SyntaxIdentityMapSyntax.identityCode w a I))
    (h4 : Derives Γ (SyntaxFreeShiftSyntax.shiftCode w b B J))
    (h5 : Derives Γ (IndexTermImageCodeSyntax.converted true w I R a a B))
    (h6 : Derives Γ (IndexTermImageCodeSyntax.converted false w J S b a B))
    (hL : Derives Γ (SyntaxMixedImageCodeSyntax.termList w k a b n))
    : Derives Γ (fiber w mode depth parameter k a B n) := by
  have hpr := OriginalNumericTermFiber.weaken_promise hZ w mode depth parameter a b B I J R S h0 h1 h2 h3 h4 h5 h6
  have hc : Derives Γ (SyntaxTermSyntax.contexts w a B) := .conjL (.conjR (IndexTermImageCodeTyping.term_list true w I R a a B h5))
  exact OriginalArgumentValueInduction.actual_fiber hZ false w mode depth parameter a b a B n k h0 h1 (.conjL h2) (.conjR h2) hc hpr hL

end PPAC.Migration.Internal.OriginalArgumentModeFiber
