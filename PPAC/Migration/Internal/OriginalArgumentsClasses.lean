import PPAC.Migration.Internal.OriginalModeDispatch

/-! 原完整28规则表的kind2参数列表分类；未删改原表。 -/
namespace PPAC.Migration.Internal.OriginalArgumentsClasses
open YesMetaZFC.Automation.ObjectHorn (Expr Rule)
open YesMetaZFC.Automation.ObjectSyntaxTransform

def selected : List Rule := [nilArguments, consArguments]

def outside (rule : Rule) : Prop :=
  ∃ tag p, tag ≠ 2 ∧ rule.head = Expr.succ (.pair (.literal tag) p)

theorem classified (rule : Rule) (hr : rule ∈ rules) : outside rule ∨ rule ∈ selected := by
  simp only [rules, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl ⟨0, OriginalScalarClasses.payload (lookupHead).head, by decide, rfl⟩
  · exact Or.inl ⟨0, OriginalScalarClasses.payload (lookupTail).head, by decide, rfl⟩
  · exact Or.inl ⟨1, OriginalScalarClasses.payload (boundIdentity 0).head, by decide, rfl⟩
  · exact Or.inl ⟨1, OriginalScalarClasses.payload (boundIdentity 3).head, by decide, rfl⟩
  · exact Or.inl ⟨1, OriginalScalarClasses.payload (boundIdentity 1 true).head, by decide, rfl⟩
  · exact Or.inl ⟨1, OriginalScalarClasses.payload (boundAbstract).head, by decide, rfl⟩
  · exact Or.inl ⟨1, OriginalScalarClasses.payload (boundIdentity 2 true).head, by decide, rfl⟩
  · exact Or.inl ⟨1, OriginalScalarClasses.payload (boundPoint).head, by decide, rfl⟩
  · exact Or.inl ⟨1, OriginalScalarClasses.payload (boundPredecessor).head, by decide, rfl⟩
  · exact Or.inl ⟨1, OriginalScalarClasses.payload (freeWeaken).head, by decide, rfl⟩
  · exact Or.inl ⟨1, OriginalScalarClasses.payload (freeAbstractHead).head, by decide, rfl⟩
  · exact Or.inl ⟨1, OriginalScalarClasses.payload (freeAbstractTail).head, by decide, rfl⟩
  · exact Or.inl ⟨1, OriginalScalarClasses.payload (freeIdentity).head, by decide, rfl⟩
  · exact Or.inl ⟨1, OriginalScalarClasses.payload (freeReplace).head, by decide, rfl⟩
  · exact Or.inl ⟨1, OriginalScalarClasses.payload (application 1).head, by decide, rfl⟩
  · exact Or.inr (by simp [selected])
  · exact Or.inr (by simp [selected])
  · exact Or.inl ⟨3, OriginalScalarClasses.payload (constant 0).head, by decide, rfl⟩
  · exact Or.inl ⟨3, OriginalScalarClasses.payload (constant 1).head, by decide, rfl⟩
  · exact Or.inl ⟨3, OriginalScalarClasses.payload (application 3).head, by decide, rfl⟩
  · exact Or.inl ⟨3, OriginalScalarClasses.payload (binary 3 1).head, by decide, rfl⟩
  · exact Or.inl ⟨3, OriginalScalarClasses.payload (unary 4 false).head, by decide, rfl⟩
  · exact Or.inl ⟨3, OriginalScalarClasses.payload (binary 5 3).head, by decide, rfl⟩
  · exact Or.inl ⟨3, OriginalScalarClasses.payload (binary 6 3).head, by decide, rfl⟩
  · exact Or.inl ⟨3, OriginalScalarClasses.payload (binary 7 3).head, by decide, rfl⟩
  · exact Or.inl ⟨3, OriginalScalarClasses.payload (binary 8 3).head, by decide, rfl⟩
  · exact Or.inl ⟨3, OriginalScalarClasses.payload (unary 9 true).head, by decide, rfl⟩
  · exact Or.inl ⟨3, OriginalScalarClasses.payload (unary 10 true).head, by decide, rfl⟩

theorem selected_mem (rule : Rule) (hr : rule ∈ selected) : rule ∈ rules := by
  simp only [selected, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> simp [rules]

end PPAC.Migration.Internal.OriginalArgumentsClasses
