import PPAC.Migration.Internal.AbstractVariableComplete

/-! 原mode1全部内部变量候选输出的完整数值双条件；原应用赋值及后继见证已对象消去。 -/
namespace PPAC.Migration.Internal.AbstractVariableNumeric
open Source SourceAlgebra SourceLogic OmegaSyntax AbstractVariableValueSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem bound_sound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r idx : Fin m)
    (xs : Fin 5 → Fin m) (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxNodeSyntax.constructor 5 1 w xs r))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral 1 (xs 0))) (hv : Derives Γ (SyntaxVariableSyntax.code true w idx (xs 3)))
    (ht : Derives Γ (HornLookupConditionSyntax.condition w r)) : Derives Γ (boundValue w (xs 1) idx (xs 3) (xs 4)) := by
  have hs := Derives.impE (.conjL (OriginalAbstractTrace.variable_condition_iff hZ true w r idx xs hw hc hm hv)) ht
  apply HornStepSyntax.step_elim (OriginalAbstractClasses.variableSelected true) w r w _ hs
  intro rule hr
  simp only [OriginalAbstractClasses.variableSelected, ite_true, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · apply Derives.impI
    exact AbstractVariableSound.application_bound_preserved (ZFContext.add hZ _) w r w idx xs (add hw _) (add hc _) (add hv _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact AbstractVariableSound.application_bound_shifted (ZFContext.add hZ _) w r w idx xs (add hw _) (add hc _) (add hv _) (.hyp (Or.inl rfl))

theorem free_sound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r idx : Fin m)
    (xs : Fin 5 → Fin m) (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxNodeSyntax.constructor 5 1 w xs r))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral 1 (xs 0))) (hv : Derives Γ (SyntaxVariableSyntax.code false w idx (xs 3)))
    (ht : Derives Γ (HornLookupConditionSyntax.condition w r)) : Derives Γ (freeValue w (xs 1) idx (xs 4)) := by
  have hs := Derives.impE (.conjL (OriginalAbstractTrace.variable_condition_iff hZ false w r idx xs hw hc hm hv)) ht
  apply HornStepSyntax.step_elim (OriginalAbstractClasses.variableSelected false) w r w _ hs
  intro rule hr
  simp only [OriginalAbstractClasses.variableSelected, Bool.false_eq_true, ite_false, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · apply Derives.impI
    exact AbstractVariableSound.application_free_head (ZFContext.add hZ _) w r w idx xs (add hw _) (add hc _) (add hv _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact AbstractVariableSound.application_free_tail (ZFContext.add hZ _) w r w idx xs (add hw _) (add hc _) (add hv _) (.hyp (Or.inl rfl))

theorem bound_complete {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r idx : Fin m)
    (xs : Fin 5 → Fin m) (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxNodeSyntax.constructor 5 1 w xs r))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral 1 (xs 0))) (hv : Derives Γ (SyntaxVariableSyntax.code true w idx (xs 3)))
    (ho : Derives Γ (boundValue w (xs 1) idx (xs 3) (xs 4))) : Derives Γ (HornLookupConditionSyntax.condition w r) := by
  apply Derives.disjE ho
  · let E := (Formula.mem idx (xs 1)).conj (.equal (xs 4) (xs 3))
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    exact AbstractVariableComplete.bound_preserved (ZFContext.add hZ E) w r idx xs
      (add hw E) (add hc E) (add hm E) (add hv E) (.conjL hE) (.conjR hE)
  · let E := boundShifted w (xs 1) idx (xs 4)
    let B := (successor (Fin.last m) idx.castSucc).conj ((Formula.mem (xs 1).castSucc (Fin.last m)).conj
      (SyntaxVariableSyntax.code true w.castSucc (Fin.last m) (xs 4).castSucc))
    let Δ := Context.add B (Context.image Formula.raise (Context.add E Γ))
    apply Derives.exE (p := B) (.hyp (Or.inl rfl))
    have hw1 := of_eq (omega_rename w Fin.castSucc) (under (add hw E) B)
    have hc1 := of_eq (SyntaxNodeSyntax.constructor_rename 5 1 w xs r Fin.castSucc) (under (add hc E) B)
    have hm1 := of_eq (SyntaxNumeralSyntax.numeral_rename 1 (xs 0) Fin.castSucc) (under (add hm E) B)
    have hv1 := of_eq (SyntaxVariableSyntax.code_rename true w idx (xs 3) Fin.castSucc) (under (add hv E) B)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have ht := AbstractVariableComplete.bound_shifted (ZFContext.under (ZFContext.add hZ E) B)
      _ _ _ _ _ hw1 hc1 hm1 hv1 (.conjL hB) (.conjL (.conjR hB)) (.conjR (.conjR hB))
    exact of_eq (HornLookupConditionSyntax.condition_rename w r Fin.castSucc).symm ht

theorem free_complete {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r idx : Fin m)
    (xs : Fin 5 → Fin m) (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxNodeSyntax.constructor 5 1 w xs r))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral 1 (xs 0))) (hv : Derives Γ (SyntaxVariableSyntax.code false w idx (xs 3)))
    (ho : Derives Γ (freeValue w (xs 1) idx (xs 4))) : Derives Γ (HornLookupConditionSyntax.condition w r) := by
  apply Derives.disjE ho
  · let E := (empty idx).conj (SyntaxVariableSyntax.code true w (xs 1) (xs 4))
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    exact AbstractVariableComplete.free_head (ZFContext.add hZ E) w r idx xs
      (add hw E) (add hc E) (add hm E) (add hv E) (.conjL hE) (.conjR hE)
  · let E := freeTail w idx (xs 4)
    let B := (successor idx.castSucc (Fin.last m)).conj (SyntaxVariableSyntax.code false w.castSucc (Fin.last m) (xs 4).castSucc)
    let Δ := Context.add B (Context.image Formula.raise (Context.add E Γ))
    apply Derives.exE (p := B) (.hyp (Or.inl rfl))
    have hw1 := of_eq (omega_rename w Fin.castSucc) (under (add hw E) B)
    have hc1 := of_eq (SyntaxNodeSyntax.constructor_rename 5 1 w xs r Fin.castSucc) (under (add hc E) B)
    have hm1 := of_eq (SyntaxNumeralSyntax.numeral_rename 1 (xs 0) Fin.castSucc) (under (add hm E) B)
    have hv1 := of_eq (SyntaxVariableSyntax.code_rename false w idx (xs 3) Fin.castSucc) (under (add hv E) B)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have ht := AbstractVariableComplete.free_tail (ZFContext.under (ZFContext.add hZ E) B)
      _ _ _ _ _ hw1 hc1 hm1 hv1 (.conjL hB) (.conjR hB)
    exact of_eq (HornLookupConditionSyntax.condition_rename w r Fin.castSucc).symm ht

theorem bound_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r idx : Fin m)
    (xs : Fin 5 → Fin m) (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxNodeSyntax.constructor 5 1 w xs r))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral 1 (xs 0))) (hv : Derives Γ (SyntaxVariableSyntax.code true w idx (xs 3))) :
    Derives Γ ((HornLookupConditionSyntax.condition w r).iff (boundValue w (xs 1) idx (xs 3) (xs 4))) := by
  apply Derives.conjI
  · apply Derives.impI
    exact bound_sound (ZFContext.add hZ _) w r idx xs (add hw _) (add hc _) (add hm _) (add hv _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact bound_complete (ZFContext.add hZ _) w r idx xs (add hw _) (add hc _) (add hm _) (add hv _) (.hyp (Or.inl rfl))

theorem free_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r idx : Fin m)
    (xs : Fin 5 → Fin m) (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxNodeSyntax.constructor 5 1 w xs r))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral 1 (xs 0))) (hv : Derives Γ (SyntaxVariableSyntax.code false w idx (xs 3))) :
    Derives Γ ((HornLookupConditionSyntax.condition w r).iff (freeValue w (xs 1) idx (xs 4))) := by
  apply Derives.conjI
  · apply Derives.impI
    exact free_sound (ZFContext.add hZ _) w r idx xs (add hw _) (add hc _) (add hm _) (add hv _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact free_complete (ZFContext.add hZ _) w r idx xs (add hw _) (add hc _) (add hm _) (add hv _) (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.AbstractVariableNumeric
