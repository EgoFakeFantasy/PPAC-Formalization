import PPAC.Migration.Internal.OriginalArgumentsConsApplication

/-! 原kind2完整轨迹的精确nil/cons方程；实际arity赋值已消去，保留所有内部候选。 -/
namespace PPAC.Migration.Internal.OriginalArgumentsTraceEquation
open Source SourceAlgebra SourceLogic OmegaSyntax OriginalArgumentCaseSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectSyntaxTransform (nilArguments consArguments)

theorem selected_iff {m} {Γ : Context m} (w r V : Fin m) :
    Derives Γ ((HornStepSyntax.step OriginalArgumentsClasses.selected w r V).iff
      ((HornApplicationSyntax.application nilArguments w r V).disj (HornApplicationSyntax.application consArguments w r V))) := by
  apply Derives.conjI
  · apply Derives.impI
    apply Derives.disjE (.hyp (Or.inl rfl))
    · exact .disjL (.hyp (Or.inl rfl))
    · apply Derives.disjE (.hyp (Or.inl rfl))
      · exact .disjR (.hyp (Or.inl rfl))
      · exact .botE (.hyp (Or.inl rfl))
  · apply Derives.impI
    apply Derives.disjE (.hyp (Or.inl rfl))
    · exact .disjL (.hyp (Or.inl rfl))
    · exact .disjR (.disjL (.hyp (Or.inl rfl)))

theorem at_row_value {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (three : Bool)
    (w mode depth parameter input output r V : Fin m) (hw : Derives Γ (omega w))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode))
    (hc : Derives Γ (OriginalTransformRowSyntax.row 2 w mode depth parameter input output r))
    (hv : Derives Γ (HornUniversalTraceSyntax.value w V)) :
    Derives Γ ((HornLookupConditionSyntax.condition w r).iff (outcomes w mode depth parameter input output)) :=
  SyntaxTypeLocalTransfer.iff_trans
    (OriginalArgumentsDispatch.trace_iff_selected hZ w r V (HornRowFields.five mode depth parameter input output) hw hc hv)
    (SyntaxTypeLocalTransfer.iff_trans (selected_iff w r V)
      (SyntaxTypeLocalTransfer.disj_congr
        (OriginalArgumentsNilApplication.application_iff hZ three w mode depth parameter input output r V hw hm hc hv)
        (OriginalArgumentsConsApplication.application_iff hZ w mode depth parameter input output r V hw hc hv)))

theorem at_row {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (three : Bool)
    (w mode depth parameter input output r : Fin m) (hw : Derives Γ (omega w))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode))
    (hc : Derives Γ (OriginalTransformRowSyntax.row 2 w mode depth parameter input output r)) :
    Derives Γ ((HornLookupConditionSyntax.condition w r).iff (outcomes w mode depth parameter input output)) := by
  let B := HornUniversalTraceSyntax.value w.castSucc (Fin.last m)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) (HornUniversalTraceValue.exists_value hZ w)
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hm1 : Derives Δ (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode.castSucc) := of_eq (SyntaxNumeralSyntax.numeral_rename _ _ Fin.castSucc) (under hm B)
  have hc1 : Derives Δ (OriginalTransformRowSyntax.row 2 w.castSucc mode.castSucc depth.castSucc parameter.castSucc input.castSucc output.castSucc r.castSucc) := of_eq (OriginalTransformRowSyntax.row_rename 2 _ _ _ _ _ _ _ Fin.castSucc) (under hc B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := at_row_value (ZFContext.under hZ B) three _ _ _ _ _ _ _ _ hw1 hm1 hc1 hB
  simpa only [Formula.raise, Formula.iff, Formula.rename, HornLookupConditionSyntax.condition_rename, outcomes_rename] using ho

end PPAC.Migration.Internal.OriginalArgumentsTraceEquation
