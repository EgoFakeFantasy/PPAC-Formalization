import PPAC.Migration.Internal.OriginalAbstractDispatch
import PPAC.Migration.Internal.OriginalScalarPositive

/-! 原mode1四条变量规则的真实守卫与原完整表闭轨迹引入；真实head给出全部赋值界。 -/
namespace PPAC.Migration.Internal.OriginalAbstractPositive
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax HornRuleSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectHorn (Rule)
open YesMetaZFC.Automation.ObjectSyntaxTransform

theorem guarded_leaf_step {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (rule : Rule)
    (hm : rule ∈ rules) (hp : rule.premises = []) (hi : ∀ i : Fin rule.arity, i ∈ rule.head.variables)
    (w r R : Fin m) (env : Fin rule.arity → Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (environmentNat rule.arity w env)) (hh : Derives Γ (graph rule.head w env r))
    (hg : Derives Γ (guards rule.guards w env)) : Derives Γ (HornStepSyntax.originalStep w r R) := by
  have hmtrx : Derives Γ (matrix rule w r R env) := by
    simp only [HornRuleSyntax.matrix, hp, HornRuleSyntax.premises]
    exact .conjI hh (.conjI hg truth_proved)
  exact HornStepSyntax.rule_intro rules rule hm w r R
    (HornApplicationRules.intro_application rule w r R env hn
      (OriginalScalarPositive.head_bound hZ rule hi w r env hw hn hh) hmtrx)

theorem guarded_leaf_condition {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (rule : Rule)
    (hm : rule ∈ rules) (hp : rule.premises = []) (hi : ∀ i : Fin rule.arity, i ∈ rule.head.variables)
    (w r : Fin m) (env : Fin rule.arity → Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (environmentNat rule.arity w env)) (hh : Derives Γ (graph rule.head w env r))
    (hg : Derives Γ (guards rule.guards w env)) : Derives Γ (HornLookupConditionSyntax.condition w r) := by
  apply OriginalScalarPositive.from_canonical hZ w r hw (HornExprRange.range hZ _ w r env hw hn hh)
  let V := HornLookupTraceValueSyntax.value w.castSucc (Fin.last m)
  let Δ := Context.add V (Context.image Formula.raise Γ)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw V)
  have hn1 := of_eq (environmentNat_rename rule.arity w env Fin.castSucc) (under hn V)
  have hh1 := of_eq (graph_rename rule.head w r env Fin.castSucc) (under hh V)
  have hg1 := of_eq (guards_rename rule.guards w env Fin.castSucc) (under hg V)
  exact guarded_leaf_step (ZFContext.under hZ V) rule hm hp hi _ _ _ _ hw1 hn1 hh1 hg1

theorem bound_identity_guard_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) (env : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 3 w env)) :
    Derives Γ ((guards (boundIdentity 1 true).guards w env).iff (.mem (env 2) (env 0))) := by
  have hv (j : Fin 3) : Derives Γ (graph (.var j) w env (env j)) := .conjI (environmentNat_at w env hn j) (.eqRefl _)
  have hg := HornRuleValue.guard_at hZ (.var 2) (.var 0) w (env 2) (env 0) env hw hn (hv 2) (hv 0)
  apply Derives.conjI
  · apply Derives.impI
    exact .impE (add (.conjL hg) _) (.conjL (.hyp (Or.inl rfl)))
  · apply Derives.impI
    exact .conjI (.impE (add (.conjR hg) _) (.hyp (Or.inl rfl))) truth_proved

theorem bound_abstract_guard_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w s : Fin m) (env : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 3 w env)) (hs : Derives Γ (successor s (env 2))) :
    Derives Γ ((guards boundAbstract.guards w env).iff (.mem (env 0) s)) := by
  have hv (j : Fin 3) : Derives Γ (graph (.var j) w env (env j)) := .conjI (environmentNat_at w env hn j) (.eqRefl _)
  have hg := HornRuleValue.guard_at hZ (.var 0) (.succ (.var 2)) w (env 0) s env hw hn (hv 0)
    (intro_succ (.var 2) w s (env 2) env (hv 2) hs)
  apply Derives.conjI
  · apply Derives.impI
    exact .impE (add (.conjL hg) _) (.conjL (.hyp (Or.inl rfl)))
  · apply Derives.impI
    exact .conjI (.impE (add (.conjR hg) _) (.hyp (Or.inl rfl))) truth_proved

theorem bound_preserved {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r : Fin m) (env : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 3 w env))
    (hh : Derives Γ (graph (boundIdentity 1 true).head w env r)) (hlt : Derives Γ (.mem (env 2) (env 0))) :
    Derives Γ (HornLookupConditionSyntax.condition w r) :=
  guarded_leaf_condition hZ (boundIdentity 1 true) (by simp [rules]) rfl (by decide) w r env hw hn hh
    (.impE (.conjR (bound_identity_guard_iff hZ w env hw hn)) hlt)

theorem bound_shifted {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s : Fin m) (env : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 3 w env))
    (hh : Derives Γ (graph boundAbstract.head w env r)) (hs : Derives Γ (successor s (env 2)))
    (hlt : Derives Γ (.mem (env 0) s)) : Derives Γ (HornLookupConditionSyntax.condition w r) :=
  guarded_leaf_condition hZ boundAbstract (by simp [rules]) rfl (by decide) w r env hw hn hh
    (.impE (.conjR (bound_abstract_guard_iff hZ w s env hw hn hs)) hlt)

theorem free_head {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r : Fin m) (env : Fin 2 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 2 w env))
    (hh : Derives Γ (graph freeAbstractHead.head w env r)) : Derives Γ (HornLookupConditionSyntax.condition w r) :=
  OriginalScalarPositive.leaf_condition hZ freeAbstractHead (by simp [rules]) rfl rfl (by decide) w r env hw hn hh

theorem free_tail {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r : Fin m) (env : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 3 w env))
    (hh : Derives Γ (graph freeAbstractTail.head w env r)) : Derives Γ (HornLookupConditionSyntax.condition w r) :=
  OriginalScalarPositive.leaf_condition hZ freeAbstractTail (by simp [rules]) rfl rfl (by decide) w r env hw hn hh

end PPAC.Migration.Internal.OriginalAbstractPositive
