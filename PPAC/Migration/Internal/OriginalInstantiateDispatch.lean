import PPAC.Migration.Internal.OriginalInstantiateClasses
import PPAC.Migration.Internal.OriginalModeDispatch
import PPAC.Migration.Internal.OriginalVariableDispatch

/-! 全内部mode2行按原表精确分派；绑定三分支与自由恒等分支。 -/
namespace PPAC.Migration.Internal.OriginalInstantiateDispatch
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax HornApplicationSyntax HornBinderSyntax
open OriginalInstantiateClasses
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectHorn (Rule)

theorem mode_rejected {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (rule : Rule) (hx : wrongMode rule)
    (w r R : Fin m) (xs : Fin 5 → Fin m) (hw : Derives Γ (omega w))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 5 1 w xs r)) (hm : Derives Γ (SyntaxNumeralSyntax.numeral 2 (xs 0)))
    (ha : Derives Γ (application rule w r R)) : Derives Γ .bot := by
  rcases hx with ⟨tag, es, hne, hfirst, hhead⟩
  let B := body rule w r R
  let Δ := Context.add B (raisedContext rule.arity Γ)
  apply HornApplicationRules.eliminate_application rule w r R .bot ha
  have hZ1 := HornBinderRules.zf_body rule.arity hZ B
  have hw1 : Derives Δ (omega (old rule.arity w)) := of_eq (omega_rename w (old rule.arity)) (HornBinderRules.under_body rule.arity hw B)
  have hc1 : Derives Δ (SyntaxNodeSyntax.constructor 5 1 (old rule.arity w) (fun i => old rule.arity (xs i)) (old rule.arity r)) := of_eq
    (SyntaxNodeSyntax.constructor_rename 5 1 w xs r (old rule.arity)) (HornBinderRules.under_body rule.arity hc B)
  have hm1 : Derives Δ (SyntaxNumeralSyntax.numeral 2 (old rule.arity (xs 0))) := of_eq
    (SyntaxNumeralSyntax.numeral_rename _ _ (old rule.arity)) (HornBinderRules.under_body rule.arity hm B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hg := Derives.conjL (Derives.conjR (Derives.conjR hB))
  rw [hhead] at hg
  have hf := HornRowFields.field_graph hZ1 1 es _ _ _ _ 0 hw1 (.conjL hB) hg hc1
  rw [hfirst] at hf
  exact .impE (SyntaxNumerals.different hZ1 tag 2 hne _ _ hf hm1) (.eqRefl _)

theorem to_selected {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w r R : Fin m) (xs : Fin 5 → Fin m) (hw : Derives Γ (omega w))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 5 1 w xs r)) (hm : Derives Γ (SyntaxNumeralSyntax.numeral 2 (xs 0)))
    (he : Derives Γ (HornStepSyntax.originalStep w r R)) : Derives Γ (HornStepSyntax.step selected w r R) := by
  apply HornStepSyntax.step_elim YesMetaZFC.Automation.ObjectSyntaxTransform.rules w r R _ he
  intro rule hr
  apply Derives.impI
  rcases classified rule hr with hout | hmode | hkeep
  · exact .botE (OriginalModeDispatch.outside_rejected (ZFContext.add hZ _) rule hout w r R xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
  · exact .botE (mode_rejected (ZFContext.add hZ _) rule hmode w r R xs (add hw _) (add hc _) (add hm _) (.hyp (Or.inl rfl)))
  · exact HornStepSyntax.rule_intro selected rule hkeep w r R (.hyp (Or.inl rfl))

theorem from_selected {m} {Γ : Context m} (w r R : Fin m)
    (he : Derives Γ (HornStepSyntax.step selected w r R)) : Derives Γ (HornStepSyntax.originalStep w r R) := by
  apply HornStepSyntax.step_elim selected w r R _ he
  intro rule hr
  apply Derives.impI
  exact HornStepSyntax.rule_intro _ rule (selected_mem rule hr) w r R (.hyp (Or.inl rfl))

theorem dispatch_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w r R : Fin m) (xs : Fin 5 → Fin m) (hw : Derives Γ (omega w))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 5 1 w xs r)) (hm : Derives Γ (SyntaxNumeralSyntax.numeral 2 (xs 0))) :
    Derives Γ ((HornStepSyntax.originalStep w r R).iff (HornStepSyntax.step selected w r R)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact to_selected (ZFContext.add hZ _) w r R xs (add hw _) (add hc _) (add hm _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact from_selected w r R (.hyp (Or.inl rfl))

theorem variable_to_selected {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool)
    (w r R idx : Fin m) (xs : Fin 5 → Fin m) (hw : Derives Γ (omega w))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 5 1 w xs r)) (hm : Derives Γ (SyntaxNumeralSyntax.numeral 2 (xs 0)))
    (hv : Derives Γ (SyntaxVariableSyntax.code bound w idx (xs 3)))
    (he : Derives Γ (HornStepSyntax.originalStep w r R)) : Derives Γ (HornStepSyntax.step (variableSelected bound) w r R) := by
  have hs := to_selected hZ w r R xs hw hc hm he
  apply HornStepSyntax.step_elim selected w r R _ hs
  intro rule hr
  apply Derives.impI
  rcases variable_classified bound rule hr with hkeep | hwrong
  · exact HornStepSyntax.rule_intro (variableSelected bound) rule hkeep w r R (.hyp (Or.inl rfl))
  · exact .botE (OriginalVariableDispatch.input_rejected (ZFContext.add hZ _) bound rule hwrong w r R idx xs
      (add hw _) (add hc _) (add hv _) (.hyp (Or.inl rfl)))

theorem variable_from_selected {m} {Γ : Context m} (bound : Bool) (w r R : Fin m)
    (he : Derives Γ (HornStepSyntax.step (variableSelected bound) w r R)) : Derives Γ (HornStepSyntax.originalStep w r R) := by
  apply HornStepSyntax.step_elim (variableSelected bound) w r R _ he
  intro rule hr
  apply Derives.impI
  exact HornStepSyntax.rule_intro _ rule (variable_mem bound rule hr) w r R (.hyp (Or.inl rfl))

theorem variable_dispatch_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool)
    (w r R idx : Fin m) (xs : Fin 5 → Fin m) (hw : Derives Γ (omega w))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 5 1 w xs r)) (hm : Derives Γ (SyntaxNumeralSyntax.numeral 2 (xs 0)))
    (hv : Derives Γ (SyntaxVariableSyntax.code bound w idx (xs 3))) :
    Derives Γ ((HornStepSyntax.originalStep w r R).iff (HornStepSyntax.step (variableSelected bound) w r R)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact variable_to_selected (ZFContext.add hZ _) bound w r R idx xs (add hw _) (add hc _) (add hm _) (add hv _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact variable_from_selected bound w r R (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.OriginalInstantiateDispatch
