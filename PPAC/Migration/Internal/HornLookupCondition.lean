import PPAC.Migration.Internal.HornLookupConditionSyntax

/-! 完整原规则表编译轨迹与原表码查找的全内部正反推导。 -/
namespace PPAC.Migration.Internal.HornLookupCondition
open Source SourceAlgebra SourceLogic OmegaSyntax HornLookupRowSyntax HornLookupConditionSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem sound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n i y r : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (row w n i y r)) (hc : Derives Γ (condition w r)) :
    Derives Γ (LookupTableExecutionSyntax.executed w n i y) := by
  let B := witness w.castSucc r.castSucc (Fin.last m)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hc
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hr1 : Derives Δ (row w.castSucc n.castSucc i.castSucc y.castSucc r.castSucc) := of_eq (row_rename _ _ _ _ _ Fin.castSucc) (under hr B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := HornLookupSoundInduction.sound (ZFContext.under hZ B) w.castSucc (Fin.last m) n.castSucc i.castSucc y.castSucc r.castSucc hw1 (.conjR (.conjR hB)) hr1 (.conjL (.conjR hB))
  exact of_eq (LookupTableExecutionSyntax.executed_rename w n i y Fin.castSucc).symm ho

theorem complete {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n i y r : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (row w n i y r))
    (he : Derives Γ (LookupTableExecutionSyntax.executed w n i y)) : Derives Γ (condition w r) := by
  have hex := HornLookupTraceValue.exists_value hZ w
  let V := HornLookupTraceValueSyntax.value w.castSucc (Fin.last m)
  let Δ := Context.add V (Context.image Formula.raise Γ)
  apply Derives.exE (p := V) hex
  have hZ1 := ZFContext.under hZ V
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw V)
  have hr1 : Derives Δ (row w.castSucc n.castSucc i.castSucc y.castSucc r.castSucc) := of_eq (row_rename _ _ _ _ _ Fin.castSucc) (under hr V)
  have he1 : Derives Δ (LookupTableExecutionSyntax.executed w.castSucc n.castSucc i.castSucc y.castSucc) := of_eq (LookupTableExecutionSyntax.executed_rename _ _ _ _ Fin.castSucc) (under he V)
  have hV : Derives Δ V := .hyp (Or.inl rfl)
  have hs := HornLookupTraceValue.subset w.castSucc (Fin.last m) hV
  have hm := HornLookupTraceValue.successful_member hZ1 w.castSucc (Fin.last m) n.castSucc i.castSucc y.castSucc r.castSucc hw1 hV hr1 he1
  have hClosed := HornLookupTraceClosed.closed hZ1 w.castSucc (Fin.last m) hw1 hV
  have ho := intro_condition _ _ _ (.conjI hs (.conjI hm hClosed))
  exact of_eq (condition_rename w r Fin.castSucc).symm ho

theorem execution_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n i y r : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (row w n i y r)) :
    Derives Γ ((condition w r).iff (LookupTableExecutionSyntax.executed w n i y)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact sound (ZFContext.add hZ _) w n i y r (add hw _) (add hr _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact complete (ZFContext.add hZ _) w n i y r (add hw _) (add hr _) (.hyp (Or.inl rfl))

theorem rejected_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n i y r : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (row w n i y r)) :
    Derives Γ ((condition w r).neg.iff (LookupTableExecutionSyntax.executed w n i y).neg) :=
  FormulaTransformCongruence.imp_congr (execution_iff hZ w n i y r hw hr) (SyntaxTypeLocalTransfer.iff_refl .bot)

end PPAC.Migration.Internal.HornLookupCondition
