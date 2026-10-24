import PPAC.Migration.Internal.OriginalInstantiateDispatch
import PPAC.Migration.Internal.OriginalAbstractPositive

/-! 待编译：原mode2四条变量规则的守卫与真实完整表闭轨迹引入。 -/
namespace PPAC.Migration.Internal.OriginalInstantiatePositive
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax HornRuleSyntax
open YesMetaZFC.Automation.ObjectSyntaxTransform

theorem bound_identity_guard_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) (env : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 3 w env)) :
    Derives Γ ((guards (boundIdentity 2 true).guards w env).iff (.mem (env 2) (env 0))) := by
  have hv (j : Fin 3) : Derives Γ (graph (.var j) w env (env j)) := .conjI (environmentNat_at w env hn j) (.eqRefl _)
  have hg := HornRuleValue.guard_at hZ (.var 2) (.var 0) w (env 2) (env 0) env hw hn (hv 2) (hv 0)
  apply Derives.conjI
  · apply Derives.impI
    exact .impE (add (.conjL hg) _) (.conjL (.hyp (Or.inl rfl)))
  · apply Derives.impI
    exact .conjI (.impE (add (.conjR hg) _) (.hyp (Or.inl rfl))) truth_proved

theorem bound_predecessor_guard_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w s : Fin m) (env : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 3 w env)) (hs : Derives Γ (successor s (env 2))) :
    Derives Γ ((guards boundPredecessor.guards w env).iff (.mem (env 0) s)) := by
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
    (hh : Derives Γ (graph (boundIdentity 2 true).head w env r)) (hlt : Derives Γ (.mem (env 2) (env 0))) :
    Derives Γ (HornLookupConditionSyntax.condition w r) :=
  OriginalAbstractPositive.guarded_leaf_condition hZ (boundIdentity 2 true) (by simp [rules]) rfl (by decide) w r env hw hn hh
    (.impE (.conjR (bound_identity_guard_iff hZ w env hw hn)) hlt)

theorem bound_predecessor {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s : Fin m) (env : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 3 w env))
    (hh : Derives Γ (graph boundPredecessor.head w env r)) (hs : Derives Γ (successor s (env 2)))
    (hlt : Derives Γ (.mem (env 0) s)) : Derives Γ (HornLookupConditionSyntax.condition w r) :=
  OriginalAbstractPositive.guarded_leaf_condition hZ boundPredecessor (by simp [rules]) rfl (by decide) w r env hw hn hh
    (.impE (.conjR (bound_predecessor_guard_iff hZ w s env hw hn hs)) hlt)

theorem bound_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r : Fin m) (env : Fin 2 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 2 w env))
    (hh : Derives Γ (graph boundPoint.head w env r)) : Derives Γ (HornLookupConditionSyntax.condition w r) :=
  OriginalScalarPositive.leaf_condition hZ boundPoint (by simp [rules]) rfl rfl (by decide) w r env hw hn hh

theorem free_identity {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r : Fin m) (env : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 3 w env))
    (hh : Derives Γ (graph freeIdentity.head w env r)) : Derives Γ (HornLookupConditionSyntax.condition w r) :=
  OriginalScalarPositive.leaf_condition hZ freeIdentity (by simp [rules]) rfl rfl (by decide) w r env hw hn hh

end PPAC.Migration.Internal.OriginalInstantiatePositive
