import PPAC.Migration.Internal.HornRowFields

/-! 原28规则逐项核检查的有限语法分类；运行时模式值仍由对象数码守卫。 -/
namespace PPAC.Migration.Internal.OriginalScalarClasses
open YesMetaZFC.Automation.ObjectHorn (Expr Rule)
open YesMetaZFC.Automation.ObjectSyntaxTransform

def mode (three : Bool) : Nat := if three then 3 else 0

def freeRule (three : Bool) : Rule := if three then freeReplace else freeWeaken

def selected (three : Bool) : List Rule := [boundIdentity (mode three), freeRule three, application 1]

def payload {n} : Expr n → Expr n
  | .succ (.pair _ p) => p
  | _ => .literal 0

def outside (rule : Rule) : Prop :=
  ∃ tag p, tag ≠ 1 ∧ rule.head = Expr.succ (.pair (.literal tag) p)

def wrongMode (three : Bool) (rule : Rule) : Prop :=
  ∃ tag, ∃ es : Fin 5 → Expr rule.arity, tag ≠ mode three ∧ es 0 = .literal tag ∧
    rule.head = Expr.node (.literal 1) (List.ofFn es)

theorem classified (three : Bool) (rule : Rule) (hr : rule ∈ rules) :
    outside rule ∨ wrongMode three rule ∨ rule ∈ selected three := by
  cases three with
  | false =>
    simp only [rules, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, payload (lookupHead).head, by decide, rfl⟩
    · exact Or.inl ⟨0, payload (lookupTail).head, by decide, rfl⟩
    · exact Or.inr (Or.inr (by simp [selected, mode, freeRule]))
    · exact Or.inr (Or.inl ⟨3, (HornRowFields.five (.literal 3) (.var 0) (.var 1) (varCode false (.var 2)) (varCode false (.var 2))), by decide, rfl, rfl⟩)
    · exact Or.inr (Or.inl ⟨1, (HornRowFields.five (.literal 1) (.var 0) (.var 1) (varCode false (.var 2)) (varCode false (.var 2))), by decide, rfl, rfl⟩)
    · exact Or.inr (Or.inl ⟨1, (HornRowFields.five (.literal 1) (.var 0) (.var 1) (varCode false (.var 2)) (varCode false (.succ (.var 2)))), by decide, rfl, rfl⟩)
    · exact Or.inr (Or.inl ⟨2, (HornRowFields.five (.literal 2) (.var 0) (.var 1) (varCode false (.var 2)) (varCode false (.var 2))), by decide, rfl, rfl⟩)
    · exact Or.inr (Or.inl ⟨2, (HornRowFields.five (.literal 2) (.var 0) (.var 1) (varCode false (.var 0)) (.var 1)), by decide, rfl, rfl⟩)
    · exact Or.inr (Or.inl ⟨2, (HornRowFields.five (.literal 2) (.var 0) (.var 1) (varCode false (.succ (.var 2))) (varCode false (.var 2))), by decide, rfl, rfl⟩)
    · exact Or.inr (Or.inr (by simp [selected, mode, freeRule]))
    · exact Or.inr (Or.inl ⟨1, (HornRowFields.five (.literal 1) (.var 0) (.var 1) (varCode true (.literal 0)) (varCode false (.var 0))), by decide, rfl, rfl⟩)
    · exact Or.inr (Or.inl ⟨1, (HornRowFields.five (.literal 1) (.var 0) (.var 1) (varCode true (.succ (.var 2))) (varCode true (.var 2))), by decide, rfl, rfl⟩)
    · exact Or.inr (Or.inl ⟨2, (HornRowFields.five (.literal 2) (.var 0) (.var 1) (varCode true (.var 2)) (varCode true (.var 2))), by decide, rfl, rfl⟩)
    · exact Or.inr (Or.inl ⟨3, (HornRowFields.five (.literal 3) (.var 0) (.var 1) (varCode true (.var 2)) (.var 3)), by decide, rfl, rfl⟩)
    · exact Or.inr (Or.inr (by simp [selected, mode, freeRule]))
    · exact Or.inl ⟨2, payload (nilArguments).head, by decide, rfl⟩
    · exact Or.inl ⟨2, payload (consArguments).head, by decide, rfl⟩
    · exact Or.inl ⟨3, payload (constant 0).head, by decide, rfl⟩
    · exact Or.inl ⟨3, payload (constant 1).head, by decide, rfl⟩
    · exact Or.inl ⟨3, payload (application 3).head, by decide, rfl⟩
    · exact Or.inl ⟨3, payload (binary 3 1).head, by decide, rfl⟩
    · exact Or.inl ⟨3, payload (unary 4 false).head, by decide, rfl⟩
    · exact Or.inl ⟨3, payload (binary 5 3).head, by decide, rfl⟩
    · exact Or.inl ⟨3, payload (binary 6 3).head, by decide, rfl⟩
    · exact Or.inl ⟨3, payload (binary 7 3).head, by decide, rfl⟩
    · exact Or.inl ⟨3, payload (binary 8 3).head, by decide, rfl⟩
    · exact Or.inl ⟨3, payload (unary 9 true).head, by decide, rfl⟩
    · exact Or.inl ⟨3, payload (unary 10 true).head, by decide, rfl⟩
  | true =>
    simp only [rules, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, payload (lookupHead).head, by decide, rfl⟩
    · exact Or.inl ⟨0, payload (lookupTail).head, by decide, rfl⟩
    · exact Or.inr (Or.inl ⟨0, (HornRowFields.five (.literal 0) (.var 0) (.var 1) (varCode false (.var 2)) (varCode false (.var 2))), by decide, rfl, rfl⟩)
    · exact Or.inr (Or.inr (by simp [selected, mode, freeRule]))
    · exact Or.inr (Or.inl ⟨1, (HornRowFields.five (.literal 1) (.var 0) (.var 1) (varCode false (.var 2)) (varCode false (.var 2))), by decide, rfl, rfl⟩)
    · exact Or.inr (Or.inl ⟨1, (HornRowFields.five (.literal 1) (.var 0) (.var 1) (varCode false (.var 2)) (varCode false (.succ (.var 2)))), by decide, rfl, rfl⟩)
    · exact Or.inr (Or.inl ⟨2, (HornRowFields.five (.literal 2) (.var 0) (.var 1) (varCode false (.var 2)) (varCode false (.var 2))), by decide, rfl, rfl⟩)
    · exact Or.inr (Or.inl ⟨2, (HornRowFields.five (.literal 2) (.var 0) (.var 1) (varCode false (.var 0)) (.var 1)), by decide, rfl, rfl⟩)
    · exact Or.inr (Or.inl ⟨2, (HornRowFields.five (.literal 2) (.var 0) (.var 1) (varCode false (.succ (.var 2))) (varCode false (.var 2))), by decide, rfl, rfl⟩)
    · exact Or.inr (Or.inl ⟨0, (HornRowFields.five (.literal 0) (.var 0) (.var 1) (varCode true (.var 2)) (varCode true (.succ (.var 2)))), by decide, rfl, rfl⟩)
    · exact Or.inr (Or.inl ⟨1, (HornRowFields.five (.literal 1) (.var 0) (.var 1) (varCode true (.literal 0)) (varCode false (.var 0))), by decide, rfl, rfl⟩)
    · exact Or.inr (Or.inl ⟨1, (HornRowFields.five (.literal 1) (.var 0) (.var 1) (varCode true (.succ (.var 2))) (varCode true (.var 2))), by decide, rfl, rfl⟩)
    · exact Or.inr (Or.inl ⟨2, (HornRowFields.five (.literal 2) (.var 0) (.var 1) (varCode true (.var 2)) (varCode true (.var 2))), by decide, rfl, rfl⟩)
    · exact Or.inr (Or.inr (by simp [selected, mode, freeRule]))
    · exact Or.inr (Or.inr (by simp [selected, mode, freeRule]))
    · exact Or.inl ⟨2, payload (nilArguments).head, by decide, rfl⟩
    · exact Or.inl ⟨2, payload (consArguments).head, by decide, rfl⟩
    · exact Or.inl ⟨3, payload (constant 0).head, by decide, rfl⟩
    · exact Or.inl ⟨3, payload (constant 1).head, by decide, rfl⟩
    · exact Or.inl ⟨3, payload (application 3).head, by decide, rfl⟩
    · exact Or.inl ⟨3, payload (binary 3 1).head, by decide, rfl⟩
    · exact Or.inl ⟨3, payload (unary 4 false).head, by decide, rfl⟩
    · exact Or.inl ⟨3, payload (binary 5 3).head, by decide, rfl⟩
    · exact Or.inl ⟨3, payload (binary 6 3).head, by decide, rfl⟩
    · exact Or.inl ⟨3, payload (binary 7 3).head, by decide, rfl⟩
    · exact Or.inl ⟨3, payload (binary 8 3).head, by decide, rfl⟩
    · exact Or.inl ⟨3, payload (unary 9 true).head, by decide, rfl⟩
    · exact Or.inl ⟨3, payload (unary 10 true).head, by decide, rfl⟩

theorem selected_mem (three : Bool) (rule : Rule) (hr : rule ∈ selected three) : rule ∈ rules := by
  cases three <;> simp only [selected, mode, freeRule, Bool.false_eq_true, ite_false, ite_true, List.mem_cons, List.not_mem_nil, or_false] at hr <;>
    rcases hr with rfl | rfl | rfl <;> simp [rules]

def chosen (three bound : Bool) : Rule := if bound then boundIdentity (mode three) else freeRule three

def wrongInput (bound : Bool) (rule : Rule) : Prop :=
  ∃ tag p, ∃ es : Fin 5 → Expr rule.arity, tag ≠ SyntaxVariableSyntax.tag bound ∧
    es 3 = Expr.succ (.pair (.literal tag) p) ∧ rule.head = Expr.node (.literal 1) (List.ofFn es)

theorem selected_classified (three bound : Bool) (rule : Rule) (hr : rule ∈ selected three) :
    rule = chosen three bound ∨ wrongInput bound rule := by
  cases three with
  | false =>
    cases bound with
    | false =>
      change rule ∈ [boundIdentity 0, freeWeaken, application 1] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact Or.inr ⟨0, payload (varCode false (.var 2)), (HornRowFields.five (.literal 0) (.var 0) (.var 1) (varCode false (.var 2)) (varCode false (.var 2))), by decide, rfl, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨2, payload (rawNode 2 (cons (.node (.var 3) []) (.var 4))), (HornRowFields.five (.var 0) (.var 1) (.var 2) (rawNode 2 (cons (.node (.var 3) []) (.var 4))) (rawNode 2 (cons (.node (.var 3) []) (.var 5)))), by decide, rfl, rfl⟩
    | true =>
      change rule ∈ [boundIdentity 0, freeWeaken, application 1] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr ⟨1, payload (varCode true (.var 2)), (HornRowFields.five (.literal 0) (.var 0) (.var 1) (varCode true (.var 2)) (varCode true (.succ (.var 2)))), by decide, rfl, rfl⟩
      · exact Or.inr ⟨2, payload (rawNode 2 (cons (.node (.var 3) []) (.var 4))), (HornRowFields.five (.var 0) (.var 1) (.var 2) (rawNode 2 (cons (.node (.var 3) []) (.var 4))) (rawNode 2 (cons (.node (.var 3) []) (.var 5)))), by decide, rfl, rfl⟩
  | true =>
    cases bound with
    | false =>
      change rule ∈ [boundIdentity 3, freeReplace, application 1] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact Or.inr ⟨0, payload (varCode false (.var 2)), (HornRowFields.five (.literal 3) (.var 0) (.var 1) (varCode false (.var 2)) (varCode false (.var 2))), by decide, rfl, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨2, payload (rawNode 2 (cons (.node (.var 3) []) (.var 4))), (HornRowFields.five (.var 0) (.var 1) (.var 2) (rawNode 2 (cons (.node (.var 3) []) (.var 4))) (rawNode 2 (cons (.node (.var 3) []) (.var 5)))), by decide, rfl, rfl⟩
    | true =>
      change rule ∈ [boundIdentity 3, freeReplace, application 1] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr ⟨1, payload (varCode true (.var 2)), (HornRowFields.five (.literal 3) (.var 0) (.var 1) (varCode true (.var 2)) (.var 3)), by decide, rfl, rfl⟩
      · exact Or.inr ⟨2, payload (rawNode 2 (cons (.node (.var 3) []) (.var 4))), (HornRowFields.five (.var 0) (.var 1) (.var 2) (rawNode 2 (cons (.node (.var 3) []) (.var 4))) (rawNode 2 (cons (.node (.var 3) []) (.var 5)))), by decide, rfl, rfl⟩

theorem chosen_mem (three bound : Bool) : chosen three bound ∈ rules := by
  cases three <;> cases bound <;> simp [chosen, mode, freeRule, rules]

end PPAC.Migration.Internal.OriginalScalarClasses
