import PPAC.Migration.Internal.OriginalFormulaMatrix
import PPAC.Migration.Internal.SmallModeArgumentsGuard

/-! 原公式常量的mode<4守卫及原矩阵方程覆盖每个固定小模式，不改写常量规则。 -/
namespace PPAC.Migration.Internal.SmallModeFormulaMatrix
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax HornUniversalTraceRules
open YesMetaZFC.Automation.ObjectSyntaxTransform (constant)

theorem constant_guard {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (modeIndex : Nat) (hSmall : modeIndex < 4)
    (tag : Nat) (w : Fin m) (env : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 3 w env))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral modeIndex (env 0))) :
    Derives Γ (HornRuleSyntax.guards (constant tag).guards w env) :=
  SmallModeArgumentsGuard.nil_guard hZ modeIndex hSmall w env hw hn hm

theorem constant_at_row {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (modeIndex : Nat) (hSmall : modeIndex < 4)
    (tag : Nat) (w n q r : Fin m) (env : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 3 w env))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral modeIndex (env 0)))
    (hc : Derives Γ (OriginalTransformRowSyntax.row 3 w (env 0) (env 1) (env 2) n q r)) :
    Derives Γ ((tracedMatrix (constant tag) w r env).iff (OriginalFormulaLocalData.constant tag w n q)) :=
  SyntaxTypeLocalTransfer.iff_trans (OriginalFormulaMatrix.constant_matrix_iff_head tag w r env (constant_guard hZ modeIndex hSmall tag w env hw hn hm))
    (OriginalFormulaExpr.constant_at_row hZ tag w n q r env hw hn hc)

end PPAC.Migration.Internal.SmallModeFormulaMatrix
