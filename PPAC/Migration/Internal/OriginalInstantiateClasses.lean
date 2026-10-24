import PPAC.Migration.Internal.OriginalScalarClasses

/-! 待编译：原mode2五条项规则的确切分类，保留完整原28规则表。 -/
namespace PPAC.Migration.Internal.OriginalInstantiateClasses
open YesMetaZFC.Automation.ObjectHorn (Expr Rule)
open YesMetaZFC.Automation.ObjectSyntaxTransform
open OriginalScalarClasses (outside payload wrongInput)

def selected : List Rule := [boundIdentity 2 true, boundPoint, boundPredecessor, freeIdentity, application 1]

def wrongMode (rule : Rule) : Prop :=
  ∃ tag, ∃ es : Fin 5 → Expr rule.arity, tag ≠ 2 ∧ es 0 = .literal tag ∧
    rule.head = Expr.node (.literal 1) (List.ofFn es)

theorem classified (rule : Rule) (hr : rule ∈ rules) :
    outside rule ∨ wrongMode rule ∨ rule ∈ selected := by
  simp only [rules, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl ⟨0, payload (lookupHead).head, by decide, rfl⟩
  · exact Or.inl ⟨0, payload (lookupTail).head, by decide, rfl⟩
  · exact Or.inr (Or.inl ⟨0, (HornRowFields.five (.literal 0) (.var 0) (.var 1) (varCode false (.var 2)) (varCode false (.var 2))), by decide, rfl, rfl⟩)
  · exact Or.inr (Or.inl ⟨3, (HornRowFields.five (.literal 3) (.var 0) (.var 1) (varCode false (.var 2)) (varCode false (.var 2))), by decide, rfl, rfl⟩)
  · exact Or.inr (Or.inl ⟨1, (HornRowFields.five (.literal 1) (.var 0) (.var 1) (varCode false (.var 2)) (varCode false (.var 2))), by decide, rfl, rfl⟩)
  · exact Or.inr (Or.inl ⟨1, (HornRowFields.five (.literal 1) (.var 0) (.var 1) (varCode false (.var 2)) (varCode false (.succ (.var 2)))), by decide, rfl, rfl⟩)
  · exact Or.inr (Or.inr (by simp [selected]))
  · exact Or.inr (Or.inr (by simp [selected]))
  · exact Or.inr (Or.inr (by simp [selected]))
  · exact Or.inr (Or.inl ⟨0, (HornRowFields.five (.literal 0) (.var 0) (.var 1) (varCode true (.var 2)) (varCode true (.succ (.var 2)))), by decide, rfl, rfl⟩)
  · exact Or.inr (Or.inl ⟨1, (HornRowFields.five (.literal 1) (.var 0) (.var 1) (varCode true (.literal 0)) (varCode false (.var 0))), by decide, rfl, rfl⟩)
  · exact Or.inr (Or.inl ⟨1, (HornRowFields.five (.literal 1) (.var 0) (.var 1) (varCode true (.succ (.var 2))) (varCode true (.var 2))), by decide, rfl, rfl⟩)
  · exact Or.inr (Or.inr (by simp [selected]))
  · exact Or.inr (Or.inl ⟨3, (HornRowFields.five (.literal 3) (.var 0) (.var 1) (varCode true (.var 2)) (.var 3)), by decide, rfl, rfl⟩)
  · exact Or.inr (Or.inr (by simp [selected]))
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

theorem selected_mem (rule : Rule) (hr : rule ∈ selected) : rule ∈ rules := by
  simp only [selected, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [rules]

def variableSelected (bound : Bool) : List Rule :=
  if bound then [boundIdentity 2 true, boundPoint, boundPredecessor] else [freeIdentity]

theorem variable_mem (bound : Bool) (rule : Rule) (hr : rule ∈ variableSelected bound) : rule ∈ rules := by
  cases bound with
  | false =>
    simp only [variableSelected, Bool.false_eq_true, ite_false, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    simp [rules]
  | true =>
    simp only [variableSelected, ite_true, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp [rules]

theorem variable_classified (bound : Bool) (rule : Rule) (hr : rule ∈ selected) :
    rule ∈ variableSelected bound ∨ wrongInput bound rule := by
  cases bound with
  | false =>
    simp only [selected, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact Or.inr ⟨0, payload (varCode false (.var 2)), (HornRowFields.five (.literal 2) (.var 0) (.var 1) (varCode false (.var 2)) (varCode false (.var 2))), by decide, rfl, rfl⟩
    · exact Or.inr ⟨0, payload (varCode false (.var 0)), (HornRowFields.five (.literal 2) (.var 0) (.var 1) (varCode false (.var 0)) (.var 1)), by decide, rfl, rfl⟩
    · exact Or.inr ⟨0, payload (varCode false (.succ (.var 2))), (HornRowFields.five (.literal 2) (.var 0) (.var 1) (varCode false (.succ (.var 2))) (varCode false (.var 2))), by decide, rfl, rfl⟩
    · exact Or.inl (by simp [variableSelected])
    · exact Or.inr ⟨2, payload (rawNode 2 (cons (.node (.var 3) []) (.var 4))), (HornRowFields.five (.var 0) (.var 1) (.var 2) (rawNode 2 (cons (.node (.var 3) []) (.var 4))) (rawNode 2 (cons (.node (.var 3) []) (.var 5)))), by decide, rfl, rfl⟩
  | true =>
    simp only [selected, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl (by simp [variableSelected])
    · exact Or.inl (by simp [variableSelected])
    · exact Or.inl (by simp [variableSelected])
    · exact Or.inr ⟨1, payload (varCode true (.var 2)), (HornRowFields.five (.literal 2) (.var 0) (.var 1) (varCode true (.var 2)) (varCode true (.var 2))), by decide, rfl, rfl⟩
    · exact Or.inr ⟨2, payload (rawNode 2 (cons (.node (.var 3) []) (.var 4))), (HornRowFields.five (.var 0) (.var 1) (.var 2) (rawNode 2 (cons (.node (.var 3) []) (.var 4))) (rawNode 2 (cons (.node (.var 3) []) (.var 5)))), by decide, rfl, rfl⟩

end PPAC.Migration.Internal.OriginalInstantiateClasses
