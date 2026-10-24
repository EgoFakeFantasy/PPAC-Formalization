import PPAC.Migration.Internal.SmallModeArgumentsNilApplication
import PPAC.Migration.Internal.OriginalArgumentRoots

/-! 任意固定k<4的原kind2完整轨迹方程；实际Separation全根见证在对象EX中消去。 -/
namespace PPAC.Migration.Internal.SmallModeArgumentsTrace
open Source SourceAlgebra SourceLogic OmegaSyntax OriginalArgumentCaseSyntax
open SyntaxRenameQuerySyntax (of_eq)
open OriginalArgumentsTraceEquation (selected_iff)
open YesMetaZFC.Automation.ObjectSyntaxTransform (nilArguments consArguments)

theorem at_row_value {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k : Nat) (hk : k < 4)
    (w mode depth parameter input output r V : Fin m) (hw : Derives Γ (omega w))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral k mode))
    (hc : Derives Γ (OriginalTransformRowSyntax.row 2 w mode depth parameter input output r))
    (hv : Derives Γ (HornUniversalTraceSyntax.value w V)) :
    Derives Γ ((HornLookupConditionSyntax.condition w r).iff (outcomes w mode depth parameter input output)) :=
  SyntaxTypeLocalTransfer.iff_trans
    (OriginalArgumentsDispatch.trace_iff_selected hZ w r V (HornRowFields.five mode depth parameter input output) hw hc hv)
    (SyntaxTypeLocalTransfer.iff_trans (selected_iff w r V)
      (SyntaxTypeLocalTransfer.disj_congr
        (SmallModeArgumentsNilApplication.application_iff hZ k hk w mode depth parameter input output r V hw hm hc hv)
        (OriginalArgumentsConsApplication.application_iff hZ w mode depth parameter input output r V hw hc hv)))

theorem at_row {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k : Nat) (hk : k < 4)
    (w mode depth parameter input output r : Fin m) (hw : Derives Γ (omega w))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral k mode))
    (hc : Derives Γ (OriginalTransformRowSyntax.row 2 w mode depth parameter input output r)) :
    Derives Γ ((HornLookupConditionSyntax.condition w r).iff (outcomes w mode depth parameter input output)) := by
  let B := HornUniversalTraceSyntax.value w.castSucc (Fin.last m)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) (HornUniversalTraceValue.exists_value hZ w)
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hm1 : Derives Δ (SyntaxNumeralSyntax.numeral k mode.castSucc) := of_eq (SyntaxNumeralSyntax.numeral_rename _ _ Fin.castSucc) (under hm B)
  have hc1 : Derives Δ (OriginalTransformRowSyntax.row 2 w.castSucc mode.castSucc depth.castSucc parameter.castSucc input.castSucc output.castSucc r.castSucc) := of_eq (OriginalTransformRowSyntax.row_rename 2 _ _ _ _ _ _ _ Fin.castSucc) (under hc B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := at_row_value (ZFContext.under hZ B) k hk _ _ _ _ _ _ _ _ hw1 hm1 hc1 hB
  simpa only [Formula.raise, Formula.iff, Formula.rename, HornLookupConditionSyntax.condition_rename, outcomes_rename] using ho

end PPAC.Migration.Internal.SmallModeArgumentsTrace
