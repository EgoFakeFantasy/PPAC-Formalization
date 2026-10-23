import PPAC.Migration.Internal.OriginalTermModeBridge

/-! 实际Num0/Num3数值项运行接原独立项程序；所有作用域和环境仍由对象公式指定。 -/
namespace PPAC.Migration.Internal.OriginalNumericTermProgram
open Source SourceAlgebra SourceLogic OmegaSyntax

theorem replace_on_term {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w mode depth a b c L I R n q : Fin m) (hw : Derives Γ (omega w))
    (hmode : Derives Γ (SyntaxNumeralSyntax.numeral 3 mode))
    (hm : Derives Γ (OriginalTermTraceSyntax.metadata w depth L))
    (hI : Derives Γ (SyntaxIdentityMapSyntax.identityCode w a I))
    (hR : Derives Γ (IndexTermImageCodeSyntax.converted true w I R a a c))
    (hL : Derives Γ (SyntaxMixedImageCodeSyntax.termList w b a c L))
    (ht : Derives Γ (SyntaxTermSyntax.term w a b n)) :
    Derives Γ ((OriginalTransformRowSyntax.run 1 w mode depth L n q).iff (TermTransformProgramSyntax.run TermTransformProgramSyntax.termProgram w R L n q)) :=
  SyntaxTypeLocalTransfer.iff_trans (OriginalTermModeBridge.run_iff hZ true w mode depth L n q hmode)
    (OriginalTermProgramBridge.replace_on_term hZ w depth a b c L I R n q hw hm hI hR hL ht)

theorem weaken_on_term {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w mode depth parameter a b B I J R S n q : Fin m) (hw : Derives Γ (omega w))
    (hmode : Derives Γ (SyntaxNumeralSyntax.numeral 0 mode))
    (hm : Derives Γ (OriginalTermTraceSyntax.metadata w depth parameter))
    (hI : Derives Γ (SyntaxIdentityMapSyntax.identityCode w a I))
    (hJ : Derives Γ (SyntaxFreeShiftSyntax.shiftCode w b B J))
    (hR : Derives Γ (IndexTermImageCodeSyntax.converted true w I R a a B))
    (hS : Derives Γ (IndexTermImageCodeSyntax.converted false w J S b a B))
    (ht : Derives Γ (SyntaxTermSyntax.term w a b n)) :
    Derives Γ ((OriginalTransformRowSyntax.run 1 w mode depth parameter n q).iff (TermTransformProgramSyntax.run TermTransformProgramSyntax.termProgram w R S n q)) :=
  SyntaxTypeLocalTransfer.iff_trans (OriginalTermModeBridge.run_iff hZ false w mode depth parameter n q hmode)
    (OriginalTermProgramBridge.weaken_on_term hZ w depth parameter a b B I J R S n q hw hm hI hJ hR hS ht)

end PPAC.Migration.Internal.OriginalNumericTermProgram
