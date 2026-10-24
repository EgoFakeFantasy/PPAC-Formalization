import PPAC.Migration.Internal.SmallModeFormulaConstantApplication
import PPAC.Migration.Internal.OriginalFormulaTraceEquation

/-! 原全部十一分支outcomes在每个固定mode<4的整条闭trace方程，使用原子Run查询及原深度递增。 -/
namespace PPAC.Migration.Internal.SmallModeFormulaTrace
open Source SourceAlgebra SourceLogic OmegaSyntax OriginalFormulaCaseSyntax
open OriginalFormulaTraceEquation (outcomes outcomes_rename)
open SyntaxRenameQuerySyntax (of_eq)

theorem at_row_value {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (modeIndex : Nat) (hSmall : modeIndex < 4)
    (w mode depth parameter input output r V : Fin m) (hw : Derives Γ (omega w))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral modeIndex mode))
    (hc : Derives Γ (OriginalTransformRowSyntax.row 3 w mode depth parameter input output r))
    (hv : Derives Γ (HornUniversalTraceSyntax.value w V)) :
    Derives Γ ((HornLookupConditionSyntax.condition w r).iff (outcomes w mode depth parameter input output)) := by
  apply SyntaxTypeLocalTransfer.iff_trans (OriginalFormulaDispatch.trace_iff_selected hZ w r V (HornRowFields.five mode depth parameter input output) hw hc hv)
  change Derives Γ ((HornStepSyntax.step OriginalFormulaClasses.selected w r V).iff (outcomes w mode depth parameter input output))
  exact SyntaxTypeLocalTransfer.disj_congr (SmallModeFormulaConstantApplication.constant_iff hZ modeIndex hSmall 0 (by simp [OriginalFormulaClasses.selected]) w mode depth parameter input output r V hw hm hc hv) (SyntaxTypeLocalTransfer.disj_congr (SmallModeFormulaConstantApplication.constant_iff hZ modeIndex hSmall 1 (by simp [OriginalFormulaClasses.selected]) w mode depth parameter input output r V hw hm hc hv) (SyntaxTypeLocalTransfer.disj_congr (OriginalFormulaArityApplications.application_iff hZ w mode depth parameter input output r V hw hc hv) (SyntaxTypeLocalTransfer.disj_congr (OriginalFormulaArityApplications.binary_iff hZ 3 1 (by simp [OriginalFormulaClasses.selected]) w mode depth parameter input output r V hw hc hv) (SyntaxTypeLocalTransfer.disj_congr (OriginalFormulaArityApplications.nonbinder_iff hZ 4 (by simp [OriginalFormulaClasses.selected]) w mode depth parameter input output r V hw hc hv) (SyntaxTypeLocalTransfer.disj_congr (OriginalFormulaArityApplications.binary_iff hZ 5 3 (by simp [OriginalFormulaClasses.selected]) w mode depth parameter input output r V hw hc hv) (SyntaxTypeLocalTransfer.disj_congr (OriginalFormulaArityApplications.binary_iff hZ 6 3 (by simp [OriginalFormulaClasses.selected]) w mode depth parameter input output r V hw hc hv) (SyntaxTypeLocalTransfer.disj_congr (OriginalFormulaArityApplications.binary_iff hZ 7 3 (by simp [OriginalFormulaClasses.selected]) w mode depth parameter input output r V hw hc hv) (SyntaxTypeLocalTransfer.disj_congr (OriginalFormulaArityApplications.binary_iff hZ 8 3 (by simp [OriginalFormulaClasses.selected]) w mode depth parameter input output r V hw hc hv) (SyntaxTypeLocalTransfer.disj_congr (OriginalFormulaBinderApplication.application_iff hZ 9 (by simp [OriginalFormulaClasses.selected]) w mode depth parameter input output r V hw hc hv) (SyntaxTypeLocalTransfer.disj_congr (OriginalFormulaBinderApplication.application_iff hZ 10 (by simp [OriginalFormulaClasses.selected]) w mode depth parameter input output r V hw hc hv) (SyntaxTypeLocalTransfer.iff_refl .bot)))))))))))

theorem at_row {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (modeIndex : Nat) (hSmall : modeIndex < 4)
    (w mode depth parameter input output r : Fin m) (hw : Derives Γ (omega w))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral modeIndex mode))
    (hc : Derives Γ (OriginalTransformRowSyntax.row 3 w mode depth parameter input output r)) :
    Derives Γ ((HornLookupConditionSyntax.condition w r).iff (outcomes w mode depth parameter input output)) := by
  let B := HornUniversalTraceSyntax.value w.castSucc (Fin.last m)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) (HornUniversalTraceValue.exists_value hZ w)
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hm1 : Derives Δ (SyntaxNumeralSyntax.numeral modeIndex mode.castSucc) := of_eq (SyntaxNumeralSyntax.numeral_rename _ _ Fin.castSucc) (under hm B)
  have hc1 : Derives Δ (OriginalTransformRowSyntax.row 3 w.castSucc mode.castSucc depth.castSucc parameter.castSucc input.castSucc output.castSucc r.castSucc) := of_eq (OriginalTransformRowSyntax.row_rename 3 _ _ _ _ _ _ _ Fin.castSucc) (under hc B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := at_row_value (ZFContext.under hZ B) modeIndex hSmall _ _ _ _ _ _ _ _ hw1 hm1 hc1 hB
  simpa only [Formula.raise, Formula.iff, Formula.rename, HornLookupConditionSyntax.condition_rename, outcomes_rename] using ho

end PPAC.Migration.Internal.SmallModeFormulaTrace
