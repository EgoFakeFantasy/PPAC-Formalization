import PPAC.Migration.Internal.HornStepSyntax

/-! 对实际固定全表核检查标签分类；不执行宿主数值查表，不更换原规则。 -/
namespace PPAC.Migration.Internal.OriginalRuleTags
open YesMetaZFC.Automation.ObjectHorn (Expr Rule)

def nonzeroOuter {n} : Expr n → Bool
  | .succ (.pair (.literal tag) _) => tag != 0
  | _ => false

def remaining : List Rule := YesMetaZFC.Automation.ObjectSyntaxTransform.rules.drop 2

theorem actual_split : YesMetaZFC.Automation.ObjectSyntaxTransform.rules =
    YesMetaZFC.Automation.ObjectSyntaxTransform.lookupHead :: YesMetaZFC.Automation.ObjectSyntaxTransform.lookupTail :: remaining := rfl

theorem remaining_classified : remaining.all (fun rule => nonzeroOuter rule.head) = true := by decide

theorem remaining_nonzero (rule : Rule) (hr : rule ∈ remaining) : nonzeroOuter rule.head = true :=
  List.all_eq_true.mp remaining_classified rule hr

theorem outer_shape {n} (e : Expr n) (he : nonzeroOuter e = true) :
    ∃ tag payload, tag ≠ 0 ∧ e = Expr.succ (.pair (.literal tag) payload) := by
  cases e with
  | literal _ | var _ | pair _ _ => cases he
  | succ e =>
    cases e with
    | literal _ | var _ | succ _ => cases he
    | pair a payload =>
      cases a with
      | var _ | succ _ | pair _ _ => cases he
      | literal tag => exact ⟨tag, payload, by simpa only [nonzeroOuter, bne_iff_ne] using he, rfl⟩

end PPAC.Migration.Internal.OriginalRuleTags
