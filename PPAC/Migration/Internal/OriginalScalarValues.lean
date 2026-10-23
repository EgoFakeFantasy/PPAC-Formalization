import PPAC.Migration.Internal.FreeWeakenOutcome
import PPAC.Migration.Internal.OriginalBoundIdentity
import PPAC.Migration.Internal.OriginalFreeReplace

/-! 四个原mode0/3变量分支的统一对象规格；外部Bool仅索引固定有限原规则模式。 -/
namespace PPAC.Migration.Internal.OriginalScalarValues
open Source SourceAlgebra SourceLogic OmegaSyntax

def valueSpec {m} (three bound : Bool) (w parameter input idx output : Fin m) : Formula m :=
  if bound then .equal output input else
    if three then LookupTableExecutionSyntax.executed w parameter idx output else FreeWeakenValueSyntax.shifted w idx output

theorem valueSpec_rename {m k} (three bound : Bool) (w parameter input idx output : Fin m) (ρ : Fin m → Fin k) :
    (valueSpec three bound w parameter input idx output).rename ρ = valueSpec three bound (ρ w) (ρ parameter) (ρ input) (ρ idx) (ρ output) := by
  cases bound with
  | true => rfl
  | false =>
    cases three with
    | true => exact LookupTableExecutionSyntax.executed_rename w parameter idx output ρ
    | false => exact FreeWeakenValueSyntax.shifted_rename w idx output ρ

theorem trace_iff_value {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (three bound : Bool)
    (w r idx : Fin m) (xs : Fin 5 → Fin m) (hw : Derives Γ (omega w))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 5 1 w xs r))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) (xs 0)))
    (hv : Derives Γ (SyntaxVariableSyntax.code bound w idx (xs 3))) :
    Derives Γ ((HornLookupConditionSyntax.condition w r).iff (valueSpec three bound w (xs 2) (xs 3) idx (xs 4))) := by
  cases bound with
  | true => exact OriginalBoundIdentity.trace_iff_identity hZ three w r idx xs hw hc hm hv
  | false =>
    cases three with
    | true => exact OriginalFreeReplace.trace_iff_execution hZ w r idx xs hw hc hm hv
    | false => exact OriginalFreeWeaken.trace_iff_shifted hZ w r idx xs hw hc hm hv

theorem power_trace_iff_value {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (three bound : Bool)
    (w r idx : Fin m) (xs : Fin 5 → Fin m) (hw : Derives Γ (omega w))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 5 1 w xs r))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) (xs 0)))
    (hv : Derives Γ (SyntaxVariableSyntax.code bound w idx (xs 3))) :
    Derives Γ ((HornLookupPowerCondition.condition w r).iff (valueSpec three bound w (xs 2) (xs 3) idx (xs 4))) := by
  cases bound with
  | true => exact OriginalBoundIdentity.power_trace_iff_identity hZ three w r idx xs hw hc hm hv
  | false =>
    cases three with
    | true => exact OriginalFreeReplace.power_trace_iff_execution hZ w r idx xs hw hc hm hv
    | false => exact OriginalFreeWeaken.power_trace_iff_shifted hZ w r idx xs hw hc hm hv

theorem rejected_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (three bound : Bool)
    (w r idx : Fin m) (xs : Fin 5 → Fin m) (hw : Derives Γ (omega w))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 5 1 w xs r))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) (xs 0)))
    (hv : Derives Γ (SyntaxVariableSyntax.code bound w idx (xs 3))) :
    Derives Γ ((HornLookupConditionSyntax.condition w r).neg.iff (valueSpec three bound w (xs 2) (xs 3) idx (xs 4)).neg) :=
  FormulaTransformCongruence.imp_congr (trace_iff_value hZ three bound w r idx xs hw hc hm hv) (SyntaxTypeLocalTransfer.iff_refl .bot)

end PPAC.Migration.Internal.OriginalScalarValues
