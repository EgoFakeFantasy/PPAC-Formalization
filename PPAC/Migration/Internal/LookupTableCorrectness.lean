import PPAC.Migration.Internal.LookupTableCorrectnessInduction

/-! 所有内部候选的执行对应。显式保留表码、索引自然数守卫。 -/
namespace PPAC.Migration.Internal.LookupTableCorrectness
open Source SourceAlgebra SourceLogic OmegaSyntax

theorem execution_iff_checked {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n i y : Fin m)
    (hw : Derives Γ (omega w)) :
    Derives Γ ((LookupTableExecutionSyntax.executed w n i y).iff (StrictLookupSyntax.checked w n i y)) := by
  apply SourcePropositional.by_cases (Formula.mem n w)
  · let N := Formula.mem n w
    have hn : Derives (Context.add N Γ) N := .hyp (Or.inl rfl)
    apply SourcePropositional.by_cases (Formula.mem i w)
    · let I := Formula.mem i w
      have hi : Derives (Context.add I (Context.add N Γ)) I := .hyp (Or.inl rfl)
      have hh := LookupTableCorrectnessInduction.execution_iff_at_natural (ZFContext.add (ZFContext.add hZ N) I) w n i y (add (add hw N) I) (add hn I) hi
      apply Derives.conjI
      · apply Derives.impI
        exact .conjI (.conjI (add (add hn I) _) (add hi _)) (.impE (add (.conjL hh) _) (.hyp (Or.inl rfl)))
      · apply Derives.impI
        exact .impE (add (.conjR hh) _) (.conjR (.hyp (Or.inl rfl)))
    · apply Derives.conjI
      · apply Derives.impI
        exact .botE (.impE (.hyp (Or.inr (Or.inl rfl))) (.conjL (LookupTableJudgment.parameters_legal w n i y (.hyp (Or.inl rfl)))))
      · apply Derives.impI
        exact .botE (.impE (.hyp (Or.inr (Or.inl rfl))) (.conjR (.conjL (.hyp (Or.inl rfl)))))
  · apply Derives.conjI
    · apply Derives.impI
      exact .botE (.impE (.hyp (Or.inr (Or.inl rfl))) (.conjL (.hyp (Or.inl rfl))))
    · apply Derives.impI
      exact .botE (.impE (.hyp (Or.inr (Or.inl rfl))) (.conjL (.conjL (.hyp (Or.inl rfl)))))

end PPAC.Migration.Internal.LookupTableCorrectness
