import PPAC.Migration.Internal.OriginalArgumentsClasses
import PPAC.Migration.Internal.HornUniversalTraceClosed

/-! 原kind2参数行上完整原表精确分派到nil/cons，并在实际通用轨迹集合处展开。 -/
namespace PPAC.Migration.Internal.OriginalArgumentsDispatch
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax HornApplicationSyntax HornBinderSyntax
open OriginalArgumentsClasses
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectHorn (Rule)

theorem outside_rejected {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (rule : Rule) (hx : outside rule)
    (w r R : Fin m) (xs : Fin 5 → Fin m) (hw : Derives Γ (omega w))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 5 2 w xs r))
    (ha : Derives Γ (application rule w r R)) : Derives Γ .bot := by
  rcases hx with ⟨tag, p, hne, hhead⟩
  let B := body rule w r R
  let Δ := Context.add B (raisedContext rule.arity Γ)
  apply HornApplicationRules.eliminate_application rule w r R .bot ha
  have hZ1 := HornBinderRules.zf_body rule.arity hZ B
  have hw1 : Derives Δ (omega (old rule.arity w)) := of_eq (omega_rename w (old rule.arity)) (HornBinderRules.under_body rule.arity hw B)
  have hc1 : Derives Δ (SyntaxNodeSyntax.constructor 5 2 (old rule.arity w) (fun i => old rule.arity (xs i)) (old rule.arity r)) := of_eq
    (SyntaxNodeSyntax.constructor_rename 5 2 w xs r (old rule.arity)) (HornBinderRules.under_body rule.arity hc B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hg := Derives.conjL (Derives.conjR (Derives.conjR hB))
  rw [hhead] at hg
  exact HornNodeDisjoint.node_contradiction hZ1 tag 2 5 hne p _ _ _ _ hw1 (.conjL hB) hg hc1

theorem to_selected {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w r R : Fin m) (xs : Fin 5 → Fin m) (hw : Derives Γ (omega w))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 5 2 w xs r))
    (he : Derives Γ (HornStepSyntax.originalStep w r R)) : Derives Γ (HornStepSyntax.step selected w r R) := by
  apply HornStepSyntax.step_elim YesMetaZFC.Automation.ObjectSyntaxTransform.rules w r R _ he
  intro rule hr
  apply Derives.impI
  rcases classified rule hr with hout | hkeep
  · exact .botE (outside_rejected (ZFContext.add hZ _) rule hout w r R xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
  · exact HornStepSyntax.rule_intro selected rule hkeep w r R (.hyp (Or.inl rfl))

theorem from_selected {m} {Γ : Context m} (w r R : Fin m)
    (he : Derives Γ (HornStepSyntax.step selected w r R)) : Derives Γ (HornStepSyntax.originalStep w r R) := by
  apply HornStepSyntax.step_elim selected w r R _ he
  intro rule hr
  apply Derives.impI
  exact HornStepSyntax.rule_intro _ rule (selected_mem rule hr) w r R (.hyp (Or.inl rfl))

theorem dispatch_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w r R : Fin m) (xs : Fin 5 → Fin m) (hw : Derives Γ (omega w))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 5 2 w xs r)) :
    Derives Γ ((HornStepSyntax.originalStep w r R).iff (HornStepSyntax.step selected w r R)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact to_selected (ZFContext.add hZ _) w r R xs (add hw _) (add hc _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact from_selected w r R (.hyp (Or.inl rfl))

theorem trace_iff_selected {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w r V : Fin m) (xs : Fin 5 → Fin m) (hw : Derives Γ (omega w))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 5 2 w xs r))
    (hv : Derives Γ (HornUniversalTraceSyntax.value w V)) :
    Derives Γ ((HornLookupConditionSyntax.condition w r).iff (HornStepSyntax.step selected w r V)) :=
  SyntaxTypeLocalTransfer.iff_trans
    (HornUniversalTraceClosed.unfold_iff hZ w V r hv (SyntaxNodeInjective.constructor_range hZ 5 2 w xs r hw hc))
    (dispatch_iff hZ w r V xs hw hc)

end PPAC.Migration.Internal.OriginalArgumentsDispatch
