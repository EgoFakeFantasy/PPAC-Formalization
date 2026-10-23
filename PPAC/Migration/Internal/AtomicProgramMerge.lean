import PPAC.Migration.Internal.OriginalTypedAtomicCases

/-! 原对象析取规则组合四类原子；反向输入守卫由受检程序本身恢复。 -/
namespace PPAC.Migration.Internal.AtomicProgramMerge
open Source SourceAlgebra SourceLogic

theorem branch_reverse {m} {Γ : Context m} {p s r : Formula m}
    (h : Derives Γ (s.imp (p.iff r))) (hs : Derives Γ (r.imp s)) : Derives Γ (r.imp p) := by
  apply Derives.impI
  have hr : Derives (Context.add r Γ) r := .hyp (Or.inl rfl)
  exact .impE (.conjR (.impE (add h r) (.impE (add hs r) hr))) hr

theorem merge {m} {Γ : Context m} (p : Formula m) (w R S a b c d n q : Fin m)
    (h0 : Derives Γ ((SyntaxAtomSyntax.nullary false w a b n).imp (p.iff (FormulaTransformAtomSyntax.nullary false w a b c d n q))))
    (h1 : Derives Γ ((SyntaxAtomSyntax.nullary true w a b n).imp (p.iff (FormulaTransformAtomSyntax.nullary true w a b c d n q))))
    (h2 : Derives Γ ((SyntaxAtomSyntax.membership w a b n).imp (p.iff (FormulaTransformAtomSyntax.membership w R S a b c d n q))))
    (h3 : Derives Γ ((SyntaxAtomSyntax.equality w a b n).imp (p.iff (FormulaTransformAtomSyntax.equality w R S a b c d n q))))
    (hA : Derives Γ (SyntaxAtomSyntax.atomic w a b n)) :
    Derives Γ (p.iff (FormulaAtomicProgramSyntax.run w R S a b c d n q)) := by
  apply Derives.conjI
  · apply Derives.impI
    have hp : Derives (Context.add p Γ) p := .hyp (Or.inl rfl)
    apply Derives.disjE (add hA p)
    · apply Derives.disjE (.hyp (Or.inl rfl))
      · exact .disjL (.disjL (.impE (.conjL (.impE (add (add (add h0 p) _) _) (.hyp (Or.inl rfl)))) (add (add hp _) _)))
      · exact .disjL (.disjR (.impE (.conjL (.impE (add (add (add h1 p) _) _) (.hyp (Or.inl rfl)))) (add (add hp _) _)))
    · apply Derives.disjE (.hyp (Or.inl rfl))
      · exact .disjR (.disjL (.impE (.conjL (.impE (add (add (add h2 p) _) _) (.hyp (Or.inl rfl)))) (add (add hp _) _)))
      · exact .disjR (.disjR (.impE (.conjL (.impE (add (add (add h3 p) _) _) (.hyp (Or.inl rfl)))) (add (add hp _) _)))
  · exact OriginalAtomicRunDispatch.disj_imp
      (OriginalAtomicRunDispatch.disj_imp (branch_reverse h0 (.impI (.conjL (.hyp (Or.inl rfl)))))
        (branch_reverse h1 (.impI (.conjL (.hyp (Or.inl rfl))))))
      (OriginalAtomicRunDispatch.disj_imp
        (branch_reverse h2 (.impI (FormulaAtomicProgramSyntax.membership_source w R S a b c d n q (.hyp (Or.inl rfl)))))
        (branch_reverse h3 (.impI (FormulaAtomicProgramSyntax.equality_source w R S a b c d n q (.hyp (Or.inl rfl))))))

end PPAC.Migration.Internal.AtomicProgramMerge
