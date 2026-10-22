import PPAC.Migration.Internal.SyntaxRenameEndpointSubst

/-! 每个原固定标签分支向完整 Cases 的原析取引入。 -/
namespace PPAC.Migration.Internal.SyntaxRenameBranchIntro
open Source SourceAlgebra SourceLogic

theorem intro_cases {m} {Γ : Context m} (kind : Fin 11) (w R S r s a b c d n q : Fin m)
    (hb : Derives Γ (SyntaxRenameTagCases.tagBranch kind w R S r s a b c d n q)) : Derives Γ (SyntaxRenameRecursiveSyntax.cases w R S r s a b c d n q) := by
  have hk : kind = (0 : Fin 11) ∨ kind = 1 ∨ kind = 2 ∨ kind = 3 ∨ kind = 4 ∨ kind = 5 ∨ kind = 6 ∨ kind = 7 ∨ kind = 8 ∨ kind = 9 ∨ kind = 10 := by omega
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact .disjL (.disjL hb)
  · exact .disjL (.disjR hb)
  · exact .disjR (.disjL hb)
  · exact .disjR (.disjR (.disjL hb))
  · exact .disjR (.disjR (.disjR (.disjL hb)))
  · exact .disjR (.disjR (.disjR (.disjR (.disjL hb))))
  · exact .disjR (.disjR (.disjR (.disjR (.disjR (.disjL hb)))))
  · exact .disjR (.disjR (.disjR (.disjR (.disjR (.disjR (.disjL hb))))))
  · exact .disjR (.disjR (.disjR (.disjR (.disjR (.disjR (.disjR (.disjL hb)))))))
  · exact .disjR (.disjR (.disjR (.disjR (.disjR (.disjR (.disjR (.disjR (.disjL hb))))))))
  · exact .disjR (.disjR (.disjR (.disjR (.disjR (.disjR (.disjR (.disjR (.disjR (hb)))))))))
end PPAC.Migration.Internal.SyntaxRenameBranchIntro
