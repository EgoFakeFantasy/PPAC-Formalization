import PPAC.Migration.Internal.OriginalFormulaBinderApplication

/-! 原kind3全部十一分支的整体数值方程；组件由内部存在量词绑定。 -/
namespace PPAC.Migration.Internal.OriginalFormulaTraceEquation
open Source SourceAlgebra SourceLogic OmegaSyntax OriginalFormulaCaseSyntax
open SyntaxRenameQuerySyntax (of_eq)

def outcomes {m} (w mode depth parameter input output : Fin m) : Formula m :=
  (OriginalFormulaLocalData.constant 0 w input output).disj ((OriginalFormulaLocalData.constant 1 w input output).disj ((applicationCase w mode depth parameter input output).disj ((binaryCase 3 1 w mode depth parameter input output).disj ((unaryCase 4 w mode depth parameter input output).disj ((binaryCase 5 3 w mode depth parameter input output).disj ((binaryCase 6 3 w mode depth parameter input output).disj ((binaryCase 7 3 w mode depth parameter input output).disj ((binaryCase 8 3 w mode depth parameter input output).disj ((binderCase 9 w mode depth parameter input output).disj ((binderCase 10 w mode depth parameter input output).disj (Formula.bot)))))))))))

theorem outcomes_rename {m j} (w mode depth parameter input output : Fin m) (ρ : Fin m → Fin j) :
    (outcomes w mode depth parameter input output).rename ρ = outcomes (ρ w) (ρ mode) (ρ depth) (ρ parameter) (ρ input) (ρ output) := by
  simp only [outcomes, Formula.rename, OriginalFormulaLocalData.constant_rename, applicationCase_rename, binaryCase_rename, unaryCase_rename, binderCase_rename]

theorem at_row_value {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (three : Bool)
    (w mode depth parameter input output r V : Fin m) (hw : Derives Γ (omega w))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode))
    (hc : Derives Γ (OriginalTransformRowSyntax.row 3 w mode depth parameter input output r))
    (hv : Derives Γ (HornUniversalTraceSyntax.value w V)) :
    Derives Γ ((HornLookupConditionSyntax.condition w r).iff (outcomes w mode depth parameter input output)) := by
  apply SyntaxTypeLocalTransfer.iff_trans (OriginalFormulaDispatch.trace_iff_selected hZ w r V (HornRowFields.five mode depth parameter input output) hw hc hv)
  change Derives Γ ((HornStepSyntax.step OriginalFormulaClasses.selected w r V).iff (outcomes w mode depth parameter input output))
  exact SyntaxTypeLocalTransfer.disj_congr (OriginalFormulaArityApplications.constant_iff hZ three 0 (by simp [OriginalFormulaClasses.selected]) w mode depth parameter input output r V hw hm hc hv) (SyntaxTypeLocalTransfer.disj_congr (OriginalFormulaArityApplications.constant_iff hZ three 1 (by simp [OriginalFormulaClasses.selected]) w mode depth parameter input output r V hw hm hc hv) (SyntaxTypeLocalTransfer.disj_congr (OriginalFormulaArityApplications.application_iff hZ w mode depth parameter input output r V hw hc hv) (SyntaxTypeLocalTransfer.disj_congr (OriginalFormulaArityApplications.binary_iff hZ 3 1 (by simp [OriginalFormulaClasses.selected]) w mode depth parameter input output r V hw hc hv) (SyntaxTypeLocalTransfer.disj_congr (OriginalFormulaArityApplications.nonbinder_iff hZ 4 (by simp [OriginalFormulaClasses.selected]) w mode depth parameter input output r V hw hc hv) (SyntaxTypeLocalTransfer.disj_congr (OriginalFormulaArityApplications.binary_iff hZ 5 3 (by simp [OriginalFormulaClasses.selected]) w mode depth parameter input output r V hw hc hv) (SyntaxTypeLocalTransfer.disj_congr (OriginalFormulaArityApplications.binary_iff hZ 6 3 (by simp [OriginalFormulaClasses.selected]) w mode depth parameter input output r V hw hc hv) (SyntaxTypeLocalTransfer.disj_congr (OriginalFormulaArityApplications.binary_iff hZ 7 3 (by simp [OriginalFormulaClasses.selected]) w mode depth parameter input output r V hw hc hv) (SyntaxTypeLocalTransfer.disj_congr (OriginalFormulaArityApplications.binary_iff hZ 8 3 (by simp [OriginalFormulaClasses.selected]) w mode depth parameter input output r V hw hc hv) (SyntaxTypeLocalTransfer.disj_congr (OriginalFormulaBinderApplication.application_iff hZ 9 (by simp [OriginalFormulaClasses.selected]) w mode depth parameter input output r V hw hc hv) (SyntaxTypeLocalTransfer.disj_congr (OriginalFormulaBinderApplication.application_iff hZ 10 (by simp [OriginalFormulaClasses.selected]) w mode depth parameter input output r V hw hc hv) (SyntaxTypeLocalTransfer.iff_refl .bot)))))))))))

theorem at_row {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (three : Bool)
    (w mode depth parameter input output r : Fin m) (hw : Derives Γ (omega w))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode))
    (hc : Derives Γ (OriginalTransformRowSyntax.row 3 w mode depth parameter input output r)) :
    Derives Γ ((HornLookupConditionSyntax.condition w r).iff (outcomes w mode depth parameter input output)) := by
  let B := HornUniversalTraceSyntax.value w.castSucc (Fin.last m)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) (HornUniversalTraceValue.exists_value hZ w)
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hm1 : Derives Δ (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode.castSucc) := of_eq (SyntaxNumeralSyntax.numeral_rename _ _ Fin.castSucc) (under hm B)
  have hc1 : Derives Δ (OriginalTransformRowSyntax.row 3 w.castSucc mode.castSucc depth.castSucc parameter.castSucc input.castSucc output.castSucc r.castSucc) := of_eq (OriginalTransformRowSyntax.row_rename 3 _ _ _ _ _ _ _ Fin.castSucc) (under hc B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := at_row_value (ZFContext.under hZ B) three _ _ _ _ _ _ _ _ hw1 hm1 hc1 hB
  simpa only [Formula.raise, Formula.iff, Formula.rename, HornLookupConditionSyntax.condition_rename, outcomes_rename] using ho

end PPAC.Migration.Internal.OriginalFormulaTraceEquation
