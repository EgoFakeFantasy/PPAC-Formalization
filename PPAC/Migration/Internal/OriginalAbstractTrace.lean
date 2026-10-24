import PPAC.Migration.Internal.OriginalAbstractPositive
import PPAC.Migration.Internal.HornUniversalTraceClosed

/-! 任意内部mode1变量查询与原对应两规则的完整有界存在式等价；全根集合见证实际构造后消去。 -/
namespace PPAC.Migration.Internal.OriginalAbstractTrace
open Source SourceAlgebra SourceLogic OmegaSyntax
open OriginalAbstractClasses
open SyntaxRenameQuerySyntax (of_eq)

def variableStep {m} (bound : Bool) (w r : Fin m) : Formula m := HornStepSyntax.step (variableSelected bound) w r w

theorem variable_step_trace_irrelevant {m} (bound : Bool) (w r R S : Fin m) :
    HornStepSyntax.step (variableSelected bound) w r R = HornStepSyntax.step (variableSelected bound) w r S := by
  cases bound <;> rfl

theorem variableStep_rename {m l} (bound : Bool) (w r : Fin m) (ρ : Fin m → Fin l) :
    (variableStep bound w r).rename ρ = variableStep bound (ρ w) (ρ r) :=
  HornStepSyntax.step_rename (variableSelected bound) w r w ρ

theorem variable_condition_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool)
    (w r idx : Fin m) (xs : Fin 5 → Fin m) (hw : Derives Γ (omega w))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 5 1 w xs r)) (hm : Derives Γ (SyntaxNumeralSyntax.numeral 1 (xs 0)))
    (hv : Derives Γ (SyntaxVariableSyntax.code bound w idx (xs 3))) :
    Derives Γ ((HornLookupConditionSyntax.condition w r).iff (variableStep bound w r)) := by
  let B := HornUniversalTraceSyntax.value w.castSucc (Fin.last m)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) (HornUniversalTraceValue.exists_value hZ w)
  have hZ1 := ZFContext.under hZ B
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hc1 := of_eq (SyntaxNodeSyntax.constructor_rename 5 1 w xs r Fin.castSucc) (under hc B)
  have hm1 := of_eq (SyntaxNumeralSyntax.numeral_rename 1 (xs 0) Fin.castSucc) (under hm B)
  have hv1 := of_eq (SyntaxVariableSyntax.code_rename bound w idx (xs 3) Fin.castSucc) (under hv B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hr := SyntaxNodeInjective.constructor_range hZ1 5 1 _ _ _ hw1 hc1
  have he := SyntaxTypeLocalTransfer.iff_trans (HornUniversalTraceClosed.unfold_iff hZ1 _ _ _ hB hr)
    (OriginalAbstractDispatch.variable_dispatch_iff hZ1 bound _ _ _ _ _ hw1 hc1 hm1 hv1)
  rw [variable_step_trace_irrelevant bound w.castSucc r.castSucc (Fin.last m) w.castSucc] at he
  change Derives Δ ((HornLookupConditionSyntax.condition w.castSucc r.castSucc).iff (variableStep bound w.castSucc r.castSucc)) at he
  exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, HornLookupConditionSyntax.condition_rename, variableStep_rename]) he

end PPAC.Migration.Internal.OriginalAbstractTrace
