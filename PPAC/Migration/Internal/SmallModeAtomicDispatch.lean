import PPAC.Migration.Internal.SmallModeFormulaRun
import PPAC.Migration.Internal.OriginalAtomicRunDispatch
import PPAC.Migration.Internal.OriginalMemberRunDispatch

/-! 每个固定mode<4的原常量／等词／成员整条运行分派，复用原outcomes排斥证明。 -/
namespace PPAC.Migration.Internal.SmallModeAtomicDispatch
open Source SourceAlgebra SourceLogic OmegaSyntax OriginalFormulaCaseSyntax

theorem run_iff_false {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (modeIndex : Nat) (hSmall : modeIndex < 4)
    (w mode depth parameter n q : Fin m) (hw : Derives Γ (omega w))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral modeIndex mode))
    (hd : Derives Γ (.mem depth w)) (hp : Derives Γ (.mem parameter w))
    (hn : Derives Γ (SyntaxNodeSyntax.constructor 0 0 w Fin.elim0 n)) :
    Derives Γ ((OriginalTransformRowSyntax.run 3 w mode depth parameter n q).iff (OriginalFormulaLocalData.constant 0 w n q)) :=
  SyntaxTypeLocalTransfer.iff_trans (SmallModeFormulaRun.run_iff hZ modeIndex hSmall w mode depth parameter n q hw hm hd hp)
    (OriginalAtomicRunDispatch.outcomes_iff_false hZ w mode depth parameter n q hw hn)

theorem run_iff_true {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (modeIndex : Nat) (hSmall : modeIndex < 4)
    (w mode depth parameter n q : Fin m) (hw : Derives Γ (omega w))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral modeIndex mode))
    (hd : Derives Γ (.mem depth w)) (hp : Derives Γ (.mem parameter w))
    (hn : Derives Γ (SyntaxNodeSyntax.constructor 0 1 w Fin.elim0 n)) :
    Derives Γ ((OriginalTransformRowSyntax.run 3 w mode depth parameter n q).iff (OriginalFormulaLocalData.constant 1 w n q)) :=
  SyntaxTypeLocalTransfer.iff_trans (SmallModeFormulaRun.run_iff hZ modeIndex hSmall w mode depth parameter n q hw hm hd hp)
    (OriginalAtomicRunDispatch.outcomes_iff_true hZ w mode depth parameter n q hw hn)

theorem run_iff_equality {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (modeIndex : Nat) (hSmall : modeIndex < 4)
    (w mode depth parameter n q x y : Fin m) (hw : Derives Γ (omega w))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral modeIndex mode))
    (hd : Derives Γ (.mem depth w)) (hp : Derives Γ (.mem parameter w))
    (hn : Derives Γ (SyntaxAtomSyntax.equalCode w x y n)) :
    Derives Γ ((OriginalTransformRowSyntax.run 3 w mode depth parameter n q).iff (binaryCase 3 1 w mode depth parameter n q)) :=
  SyntaxTypeLocalTransfer.iff_trans (SmallModeFormulaRun.run_iff hZ modeIndex hSmall w mode depth parameter n q hw hm hd hp)
    (OriginalAtomicRunDispatch.outcomes_iff_equality hZ w mode depth parameter n q x y hw hn)

theorem run_iff_application {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (modeIndex : Nat) (hSmall : modeIndex < 4)
    (w mode depth parameter s x y n q : Fin m) (hw : Derives Γ (omega w))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral modeIndex mode))
    (hd : Derives Γ (.mem depth w)) (hp : Derives Γ (.mem parameter w))
    (hn : Derives Γ (SyntaxAtomSyntax.memberCode w s x y n)) :
    Derives Γ ((OriginalTransformRowSyntax.run 3 w mode depth parameter n q).iff
      (applicationCase w mode depth parameter n q)) :=
  SyntaxTypeLocalTransfer.iff_trans (SmallModeFormulaRun.run_iff hZ modeIndex hSmall w mode depth parameter n q hw hm hd hp)
    (OriginalMemberRunDispatch.outcomes_iff_application hZ w mode depth parameter s x y n q hw hn)

end PPAC.Migration.Internal.SmallModeAtomicDispatch
