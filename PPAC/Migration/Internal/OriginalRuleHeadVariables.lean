import PPAC.Migration.Internal.HornUniversalTraceRules

/-! 对原完整28表逐条核检查：每个原存在赋值变量出现在原head，故原搜索界可实际推出。 -/
namespace PPAC.Migration.Internal.OriginalRuleHeadVariables
open Source SourceAlgebra SourceLogic OmegaSyntax
open YesMetaZFC.Automation.ObjectHorn (Rule)
open YesMetaZFC.Automation.ObjectSyntaxTransform

theorem head_variables (rule : Rule) (hr : rule ∈ rules) :
    ∀ i : Fin rule.arity, i ∈ rule.head.variables := by
  simp only [rules, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

theorem apply_original_rule {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (rule : Rule) (hr : rule ∈ rules)
    (w r : Fin m) (env : Fin rule.arity → Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (HornExprSyntax.environmentNat rule.arity w env))
    (ht : Derives Γ (HornUniversalTraceRules.tracedMatrix rule w r env)) : Derives Γ (HornLookupConditionSyntax.condition w r) :=
  HornUniversalTraceRules.apply_rule hZ rule hr (head_variables rule hr) w r env hw hn ht

end PPAC.Migration.Internal.OriginalRuleHeadVariables
