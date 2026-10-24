import PPAC.Migration.Internal.SmallModeFormulaRun
import PPAC.Migration.Internal.OriginalLogicalRunDispatch
import PPAC.Migration.Internal.OriginalBinderRunDispatch

/-! 小模式完整否定、二元和量词运行分派，原递归子查询保持不变。 -/
namespace PPAC.Migration.Internal.SmallModeLogicalDispatch
open Source SourceAlgebra SourceLogic OmegaSyntax OriginalFormulaCaseSyntax

theorem run_iff_negation {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (modeIndex : Nat) (hSmall : modeIndex < 4)
    (w mode depth parameter n q x : Fin m) (hw : Derives Γ (omega w))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral modeIndex mode))
    (hd : Derives Γ (.mem depth w)) (hp : Derives Γ (.mem parameter w))
    (hn : Derives Γ (SyntaxLogicalSyntax.singleCode 4 w x n)) :
    Derives Γ ((OriginalTransformRowSyntax.run 3 w mode depth parameter n q).iff (unaryCase 4 w mode depth parameter n q)) :=
  SyntaxTypeLocalTransfer.iff_trans (SmallModeFormulaRun.run_iff hZ modeIndex hSmall w mode depth parameter n q hw hm hd hp)
    (OriginalLogicalRunDispatch.outcomes_iff_negation hZ w mode depth parameter n q x hw hn)

theorem run_iff_binary {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (modeIndex : Nat) (hSmall : modeIndex < 4) (kind : Fin 4)
    (w mode depth parameter n q x y : Fin m) (hw : Derives Γ (omega w))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral modeIndex mode))
    (hd : Derives Γ (.mem depth w)) (hp : Derives Γ (.mem parameter w))
    (hn : Derives Γ (SyntaxLogicalSyntax.binaryCode kind w x y n)) :
    Derives Γ ((OriginalTransformRowSyntax.run 3 w mode depth parameter n q).iff (binaryCase (SyntaxLogicalSyntax.binaryTag kind) 3 w mode depth parameter n q)) :=
  SyntaxTypeLocalTransfer.iff_trans (SmallModeFormulaRun.run_iff hZ modeIndex hSmall w mode depth parameter n q hw hm hd hp)
    (OriginalLogicalRunDispatch.outcomes_iff_binary hZ kind w mode depth parameter n q x y hw hn)

theorem run_iff_quantified {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (modeIndex : Nat) (hSmall : modeIndex < 4) (universal : Bool)
    (w mode depth parameter n q x : Fin m) (hw : Derives Γ (omega w))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral modeIndex mode))
    (hd : Derives Γ (.mem depth w)) (hp : Derives Γ (.mem parameter w))
    (hn : Derives Γ (SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w x n)) :
    Derives Γ ((OriginalTransformRowSyntax.run 3 w mode depth parameter n q).iff
      (binderCase (SyntaxLogicalSyntax.quantifierTag universal) w mode depth parameter n q)) :=
  SyntaxTypeLocalTransfer.iff_trans (SmallModeFormulaRun.run_iff hZ modeIndex hSmall w mode depth parameter n q hw hm hd hp)
    (OriginalBinderRunDispatch.outcomes_iff_quantified hZ universal w mode depth parameter n q x hw hn)

end PPAC.Migration.Internal.SmallModeLogicalDispatch
