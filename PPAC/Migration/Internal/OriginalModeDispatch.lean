import PPAC.Migration.Internal.OriginalScalarClasses

/-! 真实kind1五字段行上，原完整表按内部mode0/3精确分派到三条原规则。 -/
namespace PPAC.Migration.Internal.OriginalModeDispatch
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax HornApplicationSyntax HornBinderSyntax
open OriginalScalarClasses
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectHorn (Rule)

theorem outside_rejected {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (rule : Rule) (hx : outside rule)
    (w r R : Fin m) (xs : Fin 5 → Fin m) (hw : Derives Γ (omega w))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 5 1 w xs r))
    (ha : Derives Γ (application rule w r R)) : Derives Γ .bot := by
  rcases hx with ⟨tag, p, hne, hhead⟩
  let B := body rule w r R
  let Δ := Context.add B (raisedContext rule.arity Γ)
  apply HornApplicationRules.eliminate_application rule w r R .bot ha
  have hZ1 := HornBinderRules.zf_body rule.arity hZ B
  have hw1 : Derives Δ (omega (old rule.arity w)) := of_eq (omega_rename w (old rule.arity)) (HornBinderRules.under_body rule.arity hw B)
  have hc1 : Derives Δ (SyntaxNodeSyntax.constructor 5 1 (old rule.arity w) (fun i => old rule.arity (xs i)) (old rule.arity r)) := of_eq
    (SyntaxNodeSyntax.constructor_rename 5 1 w xs r (old rule.arity)) (HornBinderRules.under_body rule.arity hc B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hg := Derives.conjL (Derives.conjR (Derives.conjR hB))
  rw [hhead] at hg
  exact HornNodeDisjoint.node_contradiction hZ1 tag 1 5 hne p _ _ _ _ hw1 (.conjL hB) hg hc1

theorem mode_rejected {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (three : Bool) (rule : Rule) (hx : wrongMode three rule)
    (w r R : Fin m) (xs : Fin 5 → Fin m) (hw : Derives Γ (omega w))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 5 1 w xs r)) (hm : Derives Γ (SyntaxNumeralSyntax.numeral (mode three) (xs 0)))
    (ha : Derives Γ (application rule w r R)) : Derives Γ .bot := by
  rcases hx with ⟨tag, es, hne, hfirst, hhead⟩
  let B := body rule w r R
  let Δ := Context.add B (raisedContext rule.arity Γ)
  apply HornApplicationRules.eliminate_application rule w r R .bot ha
  have hZ1 := HornBinderRules.zf_body rule.arity hZ B
  have hw1 : Derives Δ (omega (old rule.arity w)) := of_eq (omega_rename w (old rule.arity)) (HornBinderRules.under_body rule.arity hw B)
  have hc1 : Derives Δ (SyntaxNodeSyntax.constructor 5 1 (old rule.arity w) (fun i => old rule.arity (xs i)) (old rule.arity r)) := of_eq
    (SyntaxNodeSyntax.constructor_rename 5 1 w xs r (old rule.arity)) (HornBinderRules.under_body rule.arity hc B)
  have hm1 : Derives Δ (SyntaxNumeralSyntax.numeral (mode three) (old rule.arity (xs 0))) := of_eq
    (SyntaxNumeralSyntax.numeral_rename _ _ (old rule.arity)) (HornBinderRules.under_body rule.arity hm B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hg := Derives.conjL (Derives.conjR (Derives.conjR hB))
  rw [hhead] at hg
  have hf := HornRowFields.field_graph hZ1 1 es _ _ _ _ 0 hw1 (.conjL hB) hg hc1
  rw [hfirst] at hf
  exact .impE (SyntaxNumerals.different hZ1 tag (mode three) hne _ _ hf hm1) (.eqRefl _)

theorem to_selected {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (three : Bool)
    (w r R : Fin m) (xs : Fin 5 → Fin m) (hw : Derives Γ (omega w))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 5 1 w xs r)) (hm : Derives Γ (SyntaxNumeralSyntax.numeral (mode three) (xs 0)))
    (he : Derives Γ (HornStepSyntax.originalStep w r R)) : Derives Γ (HornStepSyntax.step (selected three) w r R) := by
  apply HornStepSyntax.step_elim YesMetaZFC.Automation.ObjectSyntaxTransform.rules w r R _ he
  intro rule hr
  apply Derives.impI
  rcases classified three rule hr with hout | hmode | hkeep
  · exact .botE (outside_rejected (ZFContext.add hZ _) rule hout w r R xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
  · exact .botE (mode_rejected (ZFContext.add hZ _) three rule hmode w r R xs (add hw _) (add hc _) (add hm _) (.hyp (Or.inl rfl)))
  · exact HornStepSyntax.rule_intro (selected three) rule hkeep w r R (.hyp (Or.inl rfl))

theorem from_selected {m} {Γ : Context m} (three : Bool) (w r R : Fin m)
    (he : Derives Γ (HornStepSyntax.step (selected three) w r R)) : Derives Γ (HornStepSyntax.originalStep w r R) := by
  apply HornStepSyntax.step_elim (selected three) w r R _ he
  intro rule hr
  apply Derives.impI
  exact HornStepSyntax.rule_intro _ rule (selected_mem three rule hr) w r R (.hyp (Or.inl rfl))

theorem dispatch_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (three : Bool)
    (w r R : Fin m) (xs : Fin 5 → Fin m) (hw : Derives Γ (omega w))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 5 1 w xs r)) (hm : Derives Γ (SyntaxNumeralSyntax.numeral (mode three) (xs 0))) :
    Derives Γ ((HornStepSyntax.originalStep w r R).iff (HornStepSyntax.step (selected three) w r R)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact to_selected (ZFContext.add hZ _) three w r R xs (add hw _) (add hc _) (add hm _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact from_selected three w r R (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.OriginalModeDispatch
