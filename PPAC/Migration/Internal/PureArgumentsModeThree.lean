import PPAC.Migration.Internal.PureSyntaxArgumentInduction
import PPAC.Migration.Internal.OriginalFreeSubstFormulaRun

/-! 专用纯参数查询连接空绑定界自由变量像及原mode3全公式运行；原数值quotation对应另待证明。 -/
namespace PPAC.Migration.Internal.PureArgumentsModeThree
open Source SourceAlgebra SourceLogic OmegaSyntax

theorem empty_bound_query_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a z c L : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) :
    Derives Γ ((PureSyntaxTrace.arguments w z c a L).iff (SyntaxFreeSubstSyntax.termList w a c L)) :=
  SyntaxTypeLocalTransfer.iff_trans (PureSyntaxArgumentInduction.checked_iff hZ w z c a L hw)
    (EmptyBoundFreeInputs.list_iff hZ w a z c L hw hz)

theorem mode_three_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w mode depth b a z c L n q : Fin m) (hw : Derives Γ (omega w))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral 3 mode)) (hd : Derives Γ (OriginalTermTraceSyntax.metadata w depth L))
    (hn : Derives Γ (FormulaCodeSyntax.formulaCode w n b a)) (hz : Derives Γ (empty z))
    (hL : Derives Γ (PureSyntaxTrace.arguments w z c a L)) :
    Derives Γ ((OriginalTransformRowSyntax.run 3 w mode depth L n q).iff
      (FreeSubstProgramSyntax.executed w b a c L n q)) :=
  OriginalFreeSubstFormulaRun.empty_bound_arguments_iff hZ w mode depth b a z c L n q hw hm hd hn hz
    (PureSyntaxArgumentInduction.checked_sound hZ w z c a L hw hL)

end PPAC.Migration.Internal.PureArgumentsModeThree
