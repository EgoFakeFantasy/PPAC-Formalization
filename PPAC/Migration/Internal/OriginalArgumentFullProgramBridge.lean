import PPAC.Migration.Internal.OriginalArgumentFieldCompletion

/-! 原mode0／3列表与独立项程序全内部字段像的完整对应；实际环境消去Promise。 -/
namespace PPAC.Migration.Internal.OriginalArgumentFullProgramBridge
open Source SourceAlgebra SourceLogic OmegaSyntax

theorem replace_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w mode depth a b c L I R n q k : Fin m)
    (h0 : Derives Γ (omega w))
    (h1 : Derives Γ (SyntaxNumeralSyntax.numeral 3 mode))
    (h2 : Derives Γ (OriginalTermTraceSyntax.metadata w depth L))
    (h3 : Derives Γ (SyntaxIdentityMapSyntax.identityCode w a I))
    (h4 : Derives Γ (IndexTermImageCodeSyntax.converted true w I R a a c))
    (h5 : Derives Γ (SyntaxMixedImageCodeSyntax.termList w b a c L))
    (hL : Derives Γ (SyntaxMixedImageCodeSyntax.termList w k a b n))
    : Derives Γ ((OriginalTransformRowSyntax.run 2 w mode depth L n q).iff (ArgumentProgramFieldSyntax.mapped w R L k a c n q)) := by
  have hpr := OriginalNumericTermFiber.replace_promise hZ w mode depth a b c L I R h0 h1 h2 h3 h4 h5
  have hc : Derives Γ (SyntaxTermSyntax.contexts w a c) := .conjL (.conjR (IndexTermImageCodeTyping.term_list true w I R a a c h4))
  have hRaw := OriginalArgumentFieldCompletion.run_iff hZ true w mode depth L a b a c n k q h0 h1 (.conjL h2) (.conjR h2) hc hpr hL
  have hFields := OriginalArgumentProgramFields.replace_fields_iff hZ w mode depth a b c L I R n q k h0 h1 h2 h3 h4 h5 hL
  exact SyntaxTypeLocalTransfer.iff_trans hRaw (FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl (SyntaxMixedImageCodeSyntax.termList w k a c q)) hFields)

theorem weaken_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w mode depth parameter a b B I J R S n q k : Fin m)
    (h0 : Derives Γ (omega w))
    (h1 : Derives Γ (SyntaxNumeralSyntax.numeral 0 mode))
    (h2 : Derives Γ (OriginalTermTraceSyntax.metadata w depth parameter))
    (h3 : Derives Γ (SyntaxIdentityMapSyntax.identityCode w a I))
    (h4 : Derives Γ (SyntaxFreeShiftSyntax.shiftCode w b B J))
    (h5 : Derives Γ (IndexTermImageCodeSyntax.converted true w I R a a B))
    (h6 : Derives Γ (IndexTermImageCodeSyntax.converted false w J S b a B))
    (hL : Derives Γ (SyntaxMixedImageCodeSyntax.termList w k a b n))
    : Derives Γ ((OriginalTransformRowSyntax.run 2 w mode depth parameter n q).iff (ArgumentProgramFieldSyntax.mapped w R S k a B n q)) := by
  have hpr := OriginalNumericTermFiber.weaken_promise hZ w mode depth parameter a b B I J R S h0 h1 h2 h3 h4 h5 h6
  have hc : Derives Γ (SyntaxTermSyntax.contexts w a B) := .conjL (.conjR (IndexTermImageCodeTyping.term_list true w I R a a B h5))
  have hRaw := OriginalArgumentFieldCompletion.run_iff hZ false w mode depth parameter a b a B n k q h0 h1 (.conjL h2) (.conjR h2) hc hpr hL
  have hFields := OriginalArgumentProgramFields.weaken_fields_iff hZ w mode depth parameter a b B I J R S n q k h0 h1 h2 h3 h4 h5 h6 hL
  exact SyntaxTypeLocalTransfer.iff_trans hRaw (FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl (SyntaxMixedImageCodeSyntax.termList w k a B q)) hFields)

end PPAC.Migration.Internal.OriginalArgumentFullProgramBridge
