import PPAC.Migration.Internal.OriginalTermProgramPoint

/-! 纯签名项的两个真实内部变量分支消去；不以外部原生项或模型语义替代对象推导。 -/
namespace PPAC.Migration.Internal.OriginalTermScopeElimination
open Source SourceAlgebra SourceLogic

theorem eliminate {m} {Γ : Context m} (w a b n : Fin m) (goal : Formula m)
    (ht : Derives Γ (SyntaxTermSyntax.term w a b n))
    (hc : ∀ bound : Bool, Derives (Context.add (SyntaxTermSyntax.branchWitness bound w (SyntaxTermSyntax.limit bound a b) n) (Context.image Formula.raise Γ)) goal.raise) :
    Derives Γ goal := by
  apply Derives.disjE (.conjR ht)
  · apply SyntaxTermSyntax.eliminate_branch true w a n goal (.hyp (Or.inl rfl))
    apply Derives.weaken _ (hc true)
    rintro p (hb | ⟨q, hq, he⟩)
    · exact Or.inl hb
    · exact Or.inr ⟨q, Or.inr hq, he⟩
  · apply SyntaxTermSyntax.eliminate_branch false w b n goal (.hyp (Or.inl rfl))
    apply Derives.weaken _ (hc false)
    rintro p (hb | ⟨q, hq, he⟩)
    · exact Or.inl hb
    · exact Or.inr ⟨q, Or.inr hq, he⟩

end PPAC.Migration.Internal.OriginalTermScopeElimination
