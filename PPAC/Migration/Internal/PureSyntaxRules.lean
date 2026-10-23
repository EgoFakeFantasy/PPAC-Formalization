import PPAC.Migration.Internal.OriginalRuleTags
import YesMetaZFC.Automation.ObjectFormulaSyntax

/-! 原规则描述在纯等词／成员签名上的精确专用表：两种变量、两种参数列及全部十一公式构造。 -/
namespace PPAC.Migration.Internal.PureSyntaxRules
open YesMetaZFC.Automation.ObjectHorn (Rule)
open YesMetaZFC.Automation

def remaining : List Rule :=
  [ObjectTermSyntax.nilRule, ObjectTermSyntax.consRule,
    ObjectFormulaSyntax.constantRule 0, ObjectFormulaSyntax.constantRule 1,
    ObjectFormulaSyntax.relationRule .membership, ObjectFormulaSyntax.equalityRule,
    ObjectFormulaSyntax.unaryRule 4 false, ObjectFormulaSyntax.binaryRule 5,
    ObjectFormulaSyntax.binaryRule 6, ObjectFormulaSyntax.binaryRule 7,
    ObjectFormulaSyntax.binaryRule 8, ObjectFormulaSyntax.unaryRule 9 true,
    ObjectFormulaSyntax.unaryRule 10 true]

def rules : List Rule := ObjectTermSyntax.variableRule false :: ObjectTermSyntax.variableRule true :: remaining

theorem rule_count : rules.length = 15 := rfl

theorem remaining_classified : remaining.all (fun r => OriginalRuleTags.nonzeroOuter r.head) = true := by decide

theorem remaining_nonzero (rule : Rule) (hr : rule ∈ remaining) : OriginalRuleTags.nonzeroOuter rule.head = true :=
  List.all_eq_true.mp remaining_classified rule hr

theorem head_variables (rule : Rule) (hr : rule ∈ rules) : ∀ i : Fin rule.arity, i ∈ rule.head.variables := by
  simp only [rules, remaining, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

end PPAC.Migration.Internal.PureSyntaxRules
