import PPAC.Migration.Internal.FormulaCodeTreeValidityCases

/-! 十一原构造组合后的全上下文树有效性进步步；尚不把归纳假设当作最终前提。 -/
namespace PPAC.Migration.Internal.FormulaCodeTreeValidityPoint
open Source SourceAlgebra SourceLogic OmegaSyntax FormulaCodeSyntax FormulaCodeRecursiveSyntax FormulaCodeTreeValiditySyntax
open StructuralTreeValiditySyntax (valid valid_rename)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem at_context {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n b f : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (earlier w n)) (hc : Derives Γ (formulaCode w n b f)) :
    Derives Γ (valid w n) := by
  have hr := FormulaCodeRecursive.recursive_iff hZ w n b f hw
  have hh : Derives Γ ((allCases w n b f).imp (valid w n)) := by
    apply FormulaCodeCaseLogic.all_imp w n b f (valid w n)
    · apply Derives.impI
      exact SyntaxAtomTreeValidity.atomic (ZFContext.add hZ _) w b f n (add hw _) (.hyp (Or.inl rfl))
    · apply Derives.impI
      exact FormulaCodeTreeValidityCases.single (ZFContext.add hZ _) 4 false w n b f (add hw _) (add hi _) (.hyp (Or.inl rfl))
    · apply Derives.impI
      exact FormulaCodeTreeValidityCases.binary (ZFContext.add hZ _) 0 w n b f (add hw _) (add hi _) (.hyp (Or.inl rfl))
    · apply Derives.impI
      exact FormulaCodeTreeValidityCases.binary (ZFContext.add hZ _) 1 w n b f (add hw _) (add hi _) (.hyp (Or.inl rfl))
    · apply Derives.impI
      exact FormulaCodeTreeValidityCases.binary (ZFContext.add hZ _) 2 w n b f (add hw _) (add hi _) (.hyp (Or.inl rfl))
    · apply Derives.impI
      exact FormulaCodeTreeValidityCases.binary (ZFContext.add hZ _) 3 w n b f (add hw _) (add hi _) (.hyp (Or.inl rfl))
    · apply Derives.impI
      exact FormulaCodeTreeValidityCases.single (ZFContext.add hZ _) 9 true w n b f (add hw _) (add hi _) (.hyp (Or.inl rfl))
    · apply Derives.impI
      exact FormulaCodeTreeValidityCases.single (ZFContext.add hZ _) 10 true w n b f (add hw _) (add hi _) (.hyp (Or.inl rfl))
  exact .impE hh (.conjR (.impE (.conjL hr) hc))

theorem property_from_earlier {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (earlier w n)) : Derives Γ (property w n) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let C := formulaCode w.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
  let Δ := Context.add C (Context.image Formula.raise (Context.image Formula.raise Γ))
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by
    simpa only [Formula.raise, omega_rename] using OrderedPairElimination.under_two hw C
  have hi2 : Derives Δ (earlier w.castSucc.castSucc n.castSucc.castSucc) := by
    simpa only [Formula.raise, earlier_rename] using OrderedPairElimination.under_two hi C
  exact at_context (ZFContext.under_two hZ C) w.castSucc.castSucc n.castSucc.castSucc
    (Fin.last m).castSucc (Fin.last (m+1)) hw2 hi2 (.hyp (Or.inl rfl))
end PPAC.Migration.Internal.FormulaCodeTreeValidityPoint
