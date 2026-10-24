import PPAC.Migration.Internal.ProjectionNodeFields
import PPAC.Migration.Internal.HornNodeDisjoint

/-! 原七投影规则按真实外壳标签分派；消去全部实际有界赋值块。 -/
namespace PPAC.Migration.Internal.ProjectionRuleDispatch
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax HornApplicationSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectHorn (Expr Rule)
open YesMetaZFC.Automation

theorem application_contradiction {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (rule : Rule)
    (tag target : Nat) (payload : Expr rule.arity) (he : rule.head = .succ (.pair (.literal tag) payload)) (hne : tag ≠ target)
    (k : Nat) (w row trace : Fin m) (xs : Fin k → Fin m) (hw : Derives Γ (omega w))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor k target w xs row))
    (ha : Derives Γ (application rule w row trace)) : Derives Γ .bot := by
  let B := body rule w row trace
  let Δ := Context.add B (raisedContext rule.arity Γ)
  apply HornApplicationRules.eliminate_application rule w row trace .bot ha
  have hZ1 := HornBinderRules.zf_body rule.arity hZ B
  have hw1 : Derives Δ (omega (old rule.arity w)) := of_eq (omega_rename w (old rule.arity)) (HornBinderRules.under_body rule.arity hw B)
  have hc1 : Derives Δ (SyntaxNodeSyntax.constructor k target (old rule.arity w) (fun i => old rule.arity (xs i)) (old rule.arity row)) := of_eq
    (SyntaxNodeSyntax.constructor_rename k target w xs row (old rule.arity)) (HornBinderRules.under_body rule.arity hc B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hg : Derives Δ (graph rule.head (old rule.arity w) (slot rule.arity) (old rule.arity row)) := .conjL (.conjR (.conjR hB))
  rw [he] at hg
  exact HornNodeDisjoint.node_contradiction hZ1 tag target k hne payload _ _ _ _ hw1 (.conjL hB) hg hc1

def tagRules : List Rule := [ObjectProjection.tagZero, ObjectProjection.tagPositive]

theorem tag_step {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k : Nat)
    (w row trace : Fin m) (xs : Fin k → Fin m) (hw : Derives Γ (omega w))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor k 0 w xs row))
    (hs : Derives Γ (HornStepSyntax.step ObjectProjection.rules w row trace)) :
    Derives Γ (HornStepSyntax.step tagRules w row trace) := by
  apply HornStepSyntax.step_elim ObjectProjection.rules w row trace _ hs
  intro rule hr
  apply Derives.impI
  simp only [ObjectProjection.rules, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact HornStepSyntax.rule_intro tagRules ObjectProjection.tagZero (by simp [tagRules]) w row trace (.hyp (Or.inl rfl))
  · exact HornStepSyntax.rule_intro tagRules ObjectProjection.tagPositive (by simp [tagRules]) w row trace (.hyp (Or.inl rfl))
  · exact .botE (application_contradiction (ZFContext.add hZ _) ObjectProjection.getZero 1 0 _ rfl (by decide) k w row trace xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
  · exact .botE (application_contradiction (ZFContext.add hZ _) ObjectProjection.getHead 1 0 _ rfl (by decide) k w row trace xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
  · exact .botE (application_contradiction (ZFContext.add hZ _) ObjectProjection.getTail 1 0 _ rfl (by decide) k w row trace xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
  · exact .botE (application_contradiction (ZFContext.add hZ _) ObjectProjection.fieldZero 2 0 _ rfl (by decide) k w row trace xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
  · exact .botE (application_contradiction (ZFContext.add hZ _) ObjectProjection.fieldPositive 2 0 _ rfl (by decide) k w row trace xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))

def getRules : List Rule := [ObjectProjection.getZero, ObjectProjection.getHead, ObjectProjection.getTail]

theorem get_step {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k : Nat)
    (w row trace : Fin m) (xs : Fin k → Fin m) (hw : Derives Γ (omega w))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor k 1 w xs row))
    (hs : Derives Γ (HornStepSyntax.step ObjectProjection.rules w row trace)) :
    Derives Γ (HornStepSyntax.step getRules w row trace) := by
  apply HornStepSyntax.step_elim ObjectProjection.rules w row trace _ hs
  intro rule hr
  apply Derives.impI
  simp only [ObjectProjection.rules, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact .botE (application_contradiction (ZFContext.add hZ _) ObjectProjection.tagZero 0 1 _ rfl (by decide) k w row trace xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
  · exact .botE (application_contradiction (ZFContext.add hZ _) ObjectProjection.tagPositive 0 1 _ rfl (by decide) k w row trace xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
  · exact HornStepSyntax.rule_intro getRules ObjectProjection.getZero (by simp [getRules]) w row trace (.hyp (Or.inl rfl))
  · exact HornStepSyntax.rule_intro getRules ObjectProjection.getHead (by simp [getRules]) w row trace (.hyp (Or.inl rfl))
  · exact HornStepSyntax.rule_intro getRules ObjectProjection.getTail (by simp [getRules]) w row trace (.hyp (Or.inl rfl))
  · exact .botE (application_contradiction (ZFContext.add hZ _) ObjectProjection.fieldZero 2 1 _ rfl (by decide) k w row trace xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
  · exact .botE (application_contradiction (ZFContext.add hZ _) ObjectProjection.fieldPositive 2 1 _ rfl (by decide) k w row trace xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))

def fieldRules : List Rule := [ObjectProjection.fieldZero, ObjectProjection.fieldPositive]

theorem field_step {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k : Nat)
    (w row trace : Fin m) (xs : Fin k → Fin m) (hw : Derives Γ (omega w))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor k 2 w xs row))
    (hs : Derives Γ (HornStepSyntax.step ObjectProjection.rules w row trace)) :
    Derives Γ (HornStepSyntax.step fieldRules w row trace) := by
  apply HornStepSyntax.step_elim ObjectProjection.rules w row trace _ hs
  intro rule hr
  apply Derives.impI
  simp only [ObjectProjection.rules, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact .botE (application_contradiction (ZFContext.add hZ _) ObjectProjection.tagZero 0 2 _ rfl (by decide) k w row trace xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
  · exact .botE (application_contradiction (ZFContext.add hZ _) ObjectProjection.tagPositive 0 2 _ rfl (by decide) k w row trace xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
  · exact .botE (application_contradiction (ZFContext.add hZ _) ObjectProjection.getZero 1 2 _ rfl (by decide) k w row trace xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
  · exact .botE (application_contradiction (ZFContext.add hZ _) ObjectProjection.getHead 1 2 _ rfl (by decide) k w row trace xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
  · exact .botE (application_contradiction (ZFContext.add hZ _) ObjectProjection.getTail 1 2 _ rfl (by decide) k w row trace xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
  · exact HornStepSyntax.rule_intro fieldRules ObjectProjection.fieldZero (by simp [fieldRules]) w row trace (.hyp (Or.inl rfl))
  · exact HornStepSyntax.rule_intro fieldRules ObjectProjection.fieldPositive (by simp [fieldRules]) w row trace (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.ProjectionRuleDispatch
