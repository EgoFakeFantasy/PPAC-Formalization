import PPAC.Migration.Internal.ArgumentForestProgramFields

/-! 原mode0／3列表在实际有限输入／输出森林处与独立项程序逐参数双向对应。 -/
namespace PPAC.Migration.Internal.OriginalArgumentForestProgram
open Source SourceAlgebra SourceLogic OmegaSyntax ArgumentForestProgramSyntax

theorem replace_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k : Nat)
    (xs ys : Fin k → Fin m) (w mode depth a b c L I R n q len : Fin m)
    (h0 : Derives Γ (omega w)) (h1 : Derives Γ (SyntaxNumeralSyntax.numeral 3 mode))
    (h2 : Derives Γ (OriginalTermTraceSyntax.metadata w depth L))
    (h3 : Derives Γ (SyntaxIdentityMapSyntax.identityCode w a I))
    (h4 : Derives Γ (IndexTermImageCodeSyntax.converted true w I R a a c))
    (h5 : Derives Γ (SyntaxMixedImageCodeSyntax.termList w b a c L))
    (hLen : Derives Γ (SyntaxNumeralSyntax.numeral k len))
    (hCtx : Derives Γ (SyntaxTermSyntax.contexts w a b))
    (hN : Derives Γ (SyntaxForestSyntax.forest k w xs n))
    (hQ : Derives Γ (SyntaxForestSyntax.forest k w ys q))
    (hT : Derives Γ (typedInputs k w a b xs)) :
    Derives Γ ((OriginalTransformRowSyntax.run 2 w mode depth L n q).iff
      ((typedInputs k w a c ys).conj (runs k w R L xs ys))) := by
  have hList := ArgumentForestTyping.list_of_forest hZ k w len a b n xs h0 hLen hCtx hN hT
  have hOriginal := OriginalArgumentFullProgramBridge.replace_iff hZ w mode depth a b c L I R n q len h0 h1 h2 h3 h4 h5 hList
  exact SyntaxTypeLocalTransfer.iff_trans hOriginal
    (ArgumentForestProgramFields.mapped_iff hZ k w R L len a c n q xs ys h0 hLen (.conjL (.conjR h5)) hN hQ)

theorem weaken_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k : Nat)
    (xs ys : Fin k → Fin m) (w mode depth parameter a b B I J R S n q len : Fin m)
    (h0 : Derives Γ (omega w)) (h1 : Derives Γ (SyntaxNumeralSyntax.numeral 0 mode))
    (h2 : Derives Γ (OriginalTermTraceSyntax.metadata w depth parameter))
    (h3 : Derives Γ (SyntaxIdentityMapSyntax.identityCode w a I))
    (h4 : Derives Γ (SyntaxFreeShiftSyntax.shiftCode w b B J))
    (h5 : Derives Γ (IndexTermImageCodeSyntax.converted true w I R a a B))
    (h6 : Derives Γ (IndexTermImageCodeSyntax.converted false w J S b a B))
    (hLen : Derives Γ (SyntaxNumeralSyntax.numeral k len))
    (hCtx : Derives Γ (SyntaxTermSyntax.contexts w a b))
    (hN : Derives Γ (SyntaxForestSyntax.forest k w xs n))
    (hQ : Derives Γ (SyntaxForestSyntax.forest k w ys q))
    (hT : Derives Γ (typedInputs k w a b xs)) :
    Derives Γ ((OriginalTransformRowSyntax.run 2 w mode depth parameter n q).iff
      ((typedInputs k w a B ys).conj (runs k w R S xs ys))) := by
  have hList := ArgumentForestTyping.list_of_forest hZ k w len a b n xs h0 hLen hCtx hN hT
  have hOriginal := OriginalArgumentFullProgramBridge.weaken_iff hZ w mode depth parameter a b B I J R S n q len h0 h1 h2 h3 h4 h5 h6 hList
  have hTarget := IndexTermImageCodeTyping.term_list true w I R a a B h5
  exact SyntaxTypeLocalTransfer.iff_trans hOriginal
    (ArgumentForestProgramFields.mapped_iff hZ k w R S len a B n q xs ys h0 hLen (.conjL (.conjR hTarget)) hN hQ)

end PPAC.Migration.Internal.OriginalArgumentForestProgram
