import PPAC.Migration.Internal.FormulaCodeCaseLogic
import PPAC.Migration.Internal.InstantiateVariableComplete
import PPAC.Migration.Internal.OriginalInstantiateTrace

/-! 原mode2全部内部变量候选输出的数值双条件；实际原赋值及后继见证均消去。 -/
namespace PPAC.Migration.Internal.InstantiateVariableNumeric
open Source SourceAlgebra SourceLogic OmegaSyntax InstantiateVariableValueSyntax

theorem bound_sound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r idx : Fin m)
    (xs : Fin 5 → Fin m) (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxNodeSyntax.constructor 5 1 w xs r))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral 2 (xs 0))) (hv : Derives Γ (SyntaxVariableSyntax.code true w idx (xs 3)))
    (ht : Derives Γ (HornLookupConditionSyntax.condition w r)) : Derives Γ (boundValue w (xs 1) (xs 2) idx (xs 3) (xs 4)) := by
  have hs := Derives.impE (.conjL (OriginalInstantiateTrace.variable_condition_iff hZ true w r idx xs hw hc hm hv)) ht
  apply HornStepSyntax.step_elim (OriginalInstantiateClasses.variableSelected true) w r w _ hs
  intro rule hr
  simp only [OriginalInstantiateClasses.variableSelected, ite_true, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · apply Derives.impI
    exact InstantiateVariableSound.application_bound_preserved (ZFContext.add hZ _) w r w idx xs (add hw _) (add hc _) (add hv _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact InstantiateVariableSound.application_bound_point (ZFContext.add hZ _) w r w idx xs (add hw _) (add hc _) (add hv _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact InstantiateVariableSound.application_bound_predecessor (ZFContext.add hZ _) w r w idx xs (add hw _) (add hc _) (add hv _) (.hyp (Or.inl rfl))

theorem free_sound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r idx : Fin m)
    (xs : Fin 5 → Fin m) (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxNodeSyntax.constructor 5 1 w xs r))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral 2 (xs 0))) (hv : Derives Γ (SyntaxVariableSyntax.code false w idx (xs 3)))
    (ht : Derives Γ (HornLookupConditionSyntax.condition w r)) : Derives Γ (.equal (xs 4) (xs 3)) := by
  have hs := Derives.impE (.conjL (OriginalInstantiateTrace.variable_condition_iff hZ false w r idx xs hw hc hm hv)) ht
  apply HornStepSyntax.step_elim (OriginalInstantiateClasses.variableSelected false) w r w _ hs
  intro rule hr
  simp only [OriginalInstantiateClasses.variableSelected, Bool.false_eq_true, ite_false, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl
  apply Derives.impI
  exact InstantiateVariableSound.application_free_identity (ZFContext.add hZ _) w r w idx xs (add hw _) (add hc _) (add hv _) (.hyp (Or.inl rfl))

theorem bound_complete {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r idx : Fin m)
    (xs : Fin 5 → Fin m) (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxNodeSyntax.constructor 5 1 w xs r))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral 2 (xs 0))) (hv : Derives Γ (SyntaxVariableSyntax.code true w idx (xs 3)))
    (ht : Derives Γ (boundValue w (xs 1) (xs 2) idx (xs 3) (xs 4))) : Derives Γ (HornLookupConditionSyntax.condition w r) := by
  have h0 : Derives Γ (((Formula.mem idx (xs 1)).conj (.equal (xs 4) (xs 3))).imp (HornLookupConditionSyntax.condition w r)) := by
    apply Derives.impI
    let E := (Formula.mem idx (xs 1)).conj (.equal (xs 4) (xs 3))
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    exact InstantiateVariableComplete.bound_preserved (ZFContext.add hZ E) w r idx xs (add hw E) (add hc E) (add hm E) (add hv E) (.conjL hE) (.conjR hE)
  have h1 : Derives Γ (((Formula.equal idx (xs 1)).conj (.equal (xs 4) (xs 2))).imp (HornLookupConditionSyntax.condition w r)) := by
    apply Derives.impI
    let E := (Formula.equal idx (xs 1)).conj (.equal (xs 4) (xs 2))
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    exact InstantiateVariableComplete.bound_point (ZFContext.add hZ E) w r idx xs (add hw E) (add hc E) (add hm E) (add hv E) (.conjL hE) (.conjR hE)
  have h2 : Derives Γ ((boundTail w (xs 1) idx (xs 4)).imp (HornLookupConditionSyntax.condition w r)) := by
    apply Derives.impI
    let E := boundTail w (xs 1) idx (xs 4)
    exact InstantiateVariableComplete.from_tail (ZFContext.add hZ E) w r idx xs (add hw E) (add hc E) (add hm E) (add hv E) (.hyp (Or.inl rfl))
  exact .impE (FormulaCodeCaseLogic.disj_imp h0 (FormulaCodeCaseLogic.disj_imp h1 h2)) ht

theorem free_complete {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r idx : Fin m)
    (xs : Fin 5 → Fin m) (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxNodeSyntax.constructor 5 1 w xs r))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral 2 (xs 0))) (hv : Derives Γ (SyntaxVariableSyntax.code false w idx (xs 3)))
    (ht : Derives Γ (.equal (xs 4) (xs 3))) : Derives Γ (HornLookupConditionSyntax.condition w r) :=
  InstantiateVariableComplete.free_identity hZ w r idx xs hw hc hm hv ht

theorem bound_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r idx : Fin m)
    (xs : Fin 5 → Fin m) (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxNodeSyntax.constructor 5 1 w xs r))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral 2 (xs 0))) (hv : Derives Γ (SyntaxVariableSyntax.code true w idx (xs 3))) :
    Derives Γ ((HornLookupConditionSyntax.condition w r).iff (boundValue w (xs 1) (xs 2) idx (xs 3) (xs 4))) := by
  apply Derives.conjI
  · apply Derives.impI
    exact bound_sound (ZFContext.add hZ _) w r idx xs (add hw _) (add hc _) (add hm _) (add hv _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact bound_complete (ZFContext.add hZ _) w r idx xs (add hw _) (add hc _) (add hm _) (add hv _) (.hyp (Or.inl rfl))

theorem free_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r idx : Fin m)
    (xs : Fin 5 → Fin m) (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxNodeSyntax.constructor 5 1 w xs r))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral 2 (xs 0))) (hv : Derives Γ (SyntaxVariableSyntax.code false w idx (xs 3))) :
    Derives Γ ((HornLookupConditionSyntax.condition w r).iff (Formula.equal (xs 4) (xs 3))) := by
  apply Derives.conjI
  · apply Derives.impI
    exact free_sound (ZFContext.add hZ _) w r idx xs (add hw _) (add hc _) (add hm _) (add hv _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact free_complete (ZFContext.add hZ _) w r idx xs (add hw _) (add hc _) (add hm _) (add hv _) (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.InstantiateVariableNumeric
