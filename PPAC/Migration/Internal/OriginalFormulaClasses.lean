import PPAC.Migration.Internal.ObjectOriginalArgumentFields

/-! 原完整28规则表中全部十一kind3公式规则的精确分类；原表保持不变。 -/
namespace PPAC.Migration.Internal.OriginalFormulaClasses
open YesMetaZFC.Automation.ObjectHorn (Expr Rule)
open YesMetaZFC.Automation.ObjectSyntaxTransform

def selected : List Rule := [constant 0, constant 1, application 3, binary 3 1, unary 4 false,
  binary 5 3, binary 6 3, binary 7 3, binary 8 3, unary 9 true, unary 10 true]

def outside (rule : Rule) : Prop :=
  ∃ tag p, tag ≠ 3 ∧ rule.head = Expr.succ (.pair (.literal tag) p)

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
  · exact Or.inl ⟨2, OriginalScalarClasses.payload (nilArguments).head, by decide, rfl⟩
  · exact Or.inl ⟨2, OriginalScalarClasses.payload (consArguments).head, by decide, rfl⟩
  · exact Or.inr (by simp [selected])
  · exact Or.inr (by simp [selected])
  · exact Or.inr (by simp [selected])
  · exact Or.inr (by simp [selected])
  · exact Or.inr (by simp [selected])
  · exact Or.inr (by simp [selected])
  · exact Or.inr (by simp [selected])
  · exact Or.inr (by simp [selected])
  · exact Or.inr (by simp [selected])
  · exact Or.inr (by simp [selected])
  · exact Or.inr (by simp [selected])

theorem selected_mem (rule : Rule) (hr : rule ∈ selected) : rule ∈ rules := by
  simp only [selected, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [rules]

end PPAC.Migration.Internal.OriginalFormulaClasses
