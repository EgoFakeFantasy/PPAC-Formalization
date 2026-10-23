import PPAC.Migration.Internal.OriginalModeDispatch
import PPAC.Migration.Internal.HornSearchRules

/-! 原完整表在任意内部mode0/3变量输入上精确选中唯一原规则。 -/
namespace PPAC.Migration.Internal.OriginalVariableDispatch
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax HornApplicationSyntax HornBinderSyntax
open OriginalScalarClasses
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectHorn (Expr Rule)

theorem variable_expr_rejected {m n} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool)
    (tag : Nat) (p : Expr n) (hne : tag ≠ SyntaxVariableSyntax.tag bound)
    (w idx y : Fin m) (env : Fin n → Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (environmentNat n w env))
    (hg : Derives Γ (graph (.succ (.pair (.literal tag) p)) w env y))
    (hv : Derives Γ (SyntaxVariableSyntax.code bound w idx y)) : Derives Γ .bot := by
  let B := SyntaxVariableSyntax.codeBody bound w idx y
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply SyntaxVariableSyntax.eliminate_code bound w idx y .bot hv
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hn1 : Derives Δ (environmentNat n w.castSucc (fun i => (env i).castSucc)) := of_eq (environmentNat_rename n w env Fin.castSucc) (under hn B)
  have hg1 : Derives Δ (graph (.succ (.pair (.literal tag) p)) w.castSucc (fun i => (env i).castSucc) y.castSucc) := of_eq (graph_rename _ w y env Fin.castSucc) (under hg B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  exact HornNodeDisjoint.node_contradiction (ZFContext.under hZ B) tag (SyntaxVariableSyntax.tag bound) 1 hne p _ _ _ _ hw1 hn1 hg1 (.conjR hB)

theorem input_rejected {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool) (rule : Rule) (hx : wrongInput bound rule)
    (w r R idx : Fin m) (xs : Fin 5 → Fin m) (hw : Derives Γ (omega w))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 5 1 w xs r))
    (hv : Derives Γ (SyntaxVariableSyntax.code bound w idx (xs 3)))
    (ha : Derives Γ (application rule w r R)) : Derives Γ .bot := by
  rcases hx with ⟨tag, p, es, hne, hinput, hhead⟩
  let B := body rule w r R
  let Δ := Context.add B (raisedContext rule.arity Γ)
  apply HornApplicationRules.eliminate_application rule w r R .bot ha
  have hZ1 := HornBinderRules.zf_body rule.arity hZ B
  have hw1 : Derives Δ (omega (old rule.arity w)) := of_eq (omega_rename w (old rule.arity)) (HornBinderRules.under_body rule.arity hw B)
  have hc1 : Derives Δ (SyntaxNodeSyntax.constructor 5 1 (old rule.arity w) (fun i => old rule.arity (xs i)) (old rule.arity r)) := of_eq
    (SyntaxNodeSyntax.constructor_rename 5 1 w xs r (old rule.arity)) (HornBinderRules.under_body rule.arity hc B)
  have hv1 : Derives Δ (SyntaxVariableSyntax.code bound (old rule.arity w) (old rule.arity idx) (old rule.arity (xs 3))) := of_eq
    (SyntaxVariableSyntax.code_rename bound w idx (xs 3) (old rule.arity)) (HornBinderRules.under_body rule.arity hv B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hg := Derives.conjL (Derives.conjR (Derives.conjR hB))
  rw [hhead] at hg
  have hf := HornRowFields.field_graph hZ1 1 es _ _ _ _ 3 hw1 (.conjL hB) hg hc1
  rw [hinput] at hf
  exact variable_expr_rejected hZ1 bound tag p hne _ _ _ _ hw1 (.conjL hB) hf hv1

theorem to_chosen {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (three bound : Bool)
    (w r R idx : Fin m) (xs : Fin 5 → Fin m) (hw : Derives Γ (omega w))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 5 1 w xs r)) (hm : Derives Γ (SyntaxNumeralSyntax.numeral (mode three) (xs 0)))
    (hv : Derives Γ (SyntaxVariableSyntax.code bound w idx (xs 3)))
    (he : Derives Γ (HornStepSyntax.originalStep w r R)) : Derives Γ (application (chosen three bound) w r R) := by
  have hs := OriginalModeDispatch.to_selected hZ three w r R xs hw hc hm he
  apply HornStepSyntax.step_elim (selected three) w r R _ hs
  intro rule hr
  apply Derives.impI
  rcases selected_classified three bound rule hr with heq | hwrong
  · subst rule
    exact .hyp (Or.inl rfl)
  · exact .botE (input_rejected (ZFContext.add hZ _) bound rule hwrong w r R idx xs (add hw _) (add hc _) (add hv _) (.hyp (Or.inl rfl)))

theorem chosen_intro {m} {Γ : Context m} (three bound : Bool) (w r R : Fin m)
    (he : Derives Γ (application (chosen three bound) w r R)) : Derives Γ (HornStepSyntax.originalStep w r R) :=
  HornStepSyntax.rule_intro _ _ (chosen_mem three bound) w r R he

theorem dispatch_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (three bound : Bool)
    (w r R idx : Fin m) (xs : Fin 5 → Fin m) (hw : Derives Γ (omega w))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 5 1 w xs r)) (hm : Derives Γ (SyntaxNumeralSyntax.numeral (mode three) (xs 0)))
    (hv : Derives Γ (SyntaxVariableSyntax.code bound w idx (xs 3))) :
    Derives Γ ((HornStepSyntax.originalStep w r R).iff (application (chosen three bound) w r R)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact to_chosen (ZFContext.add hZ _) three bound w r R idx xs (add hw _) (add hc _) (add hm _) (add hv _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact chosen_intro three bound w r R (.hyp (Or.inl rfl))

theorem search_dispatch_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (three bound : Bool)
    (w r R idx : Fin m) (xs : Fin 5 → Fin m) (hw : Derives Γ (omega w))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 5 1 w xs r)) (hm : Derives Γ (SyntaxNumeralSyntax.numeral (mode three) (xs 0)))
    (hv : Derives Γ (SyntaxVariableSyntax.code bound w idx (xs 3))) :
    Derives Γ ((HornSearchSyntax.originalSearchStep w r R).iff (application (chosen three bound) w r R)) := by
  have hn := SyntaxNodeInjective.constructor_range hZ 5 1 w xs r hw hc
  have he := HornSearchRules.step_iff_search hZ YesMetaZFC.Automation.ObjectSyntaxTransform.rules w r R hw hn
  exact SyntaxTypeLocalTransfer.iff_trans (.conjI (.conjR he) (.conjL he)) (dispatch_iff hZ three bound w r R idx xs hw hc hm hv)

theorem rejected_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (three bound : Bool)
    (w r R idx : Fin m) (xs : Fin 5 → Fin m) (hw : Derives Γ (omega w))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 5 1 w xs r)) (hm : Derives Γ (SyntaxNumeralSyntax.numeral (mode three) (xs 0)))
    (hv : Derives Γ (SyntaxVariableSyntax.code bound w idx (xs 3))) :
    Derives Γ ((HornStepSyntax.originalStep w r R).neg.iff (application (chosen three bound) w r R).neg) :=
  FormulaTransformCongruence.imp_congr (dispatch_iff hZ three bound w r R idx xs hw hc hm hv) (SyntaxTypeLocalTransfer.iff_refl .bot)

theorem closed_member_application {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (three bound : Bool)
    (w r R idx : Fin m) (xs : Fin 5 → Fin m) (hw : Derives Γ (omega w))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 5 1 w xs r)) (hm : Derives Γ (SyntaxNumeralSyntax.numeral (mode three) (xs 0)))
    (hv : Derives Γ (SyntaxVariableSyntax.code bound w idx (xs 3)))
    (hclosed : Derives Γ (HornLookupSoundSyntax.closed w R)) (hmember : Derives Γ (.mem r R)) :
    Derives Γ (application (chosen three bound) w r R) :=
  to_chosen hZ three bound w r R idx xs hw hc hm hv (HornLookupSoundSyntax.closed_at w R r hclosed hmember)

end PPAC.Migration.Internal.OriginalVariableDispatch
