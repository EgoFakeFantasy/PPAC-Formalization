import PPAC.Migration.Internal.IndexFormulaRenameLogical

/-! 原重命名的全部11种公式分支传入实际混合替换递归。 -/
namespace PPAC.Migration.Internal.IndexFormulaRenameCases
open Source SourceAlgebra SourceLogic OmegaSyntax IndexFormulaRenameBridgeSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem cases_forward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w I J R S a b c d r s n q : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (IndexTermImageCodeSyntax.environment w I J R S a b c d))
    (hi : Derives Γ (earlier w n))
    (hr : Derives Γ (SyntaxMapCodeSyntax.encoded w r a c I)) (hs : Derives Γ (SyntaxMapCodeSyntax.encoded w s b d J))
    (hc : Derives Γ (SyntaxRenameRecursiveSyntax.cases w I J r s a b c d n q)) :
    Derives Γ (SyntaxMixedFormulaRecursiveSyntax.cases w R S a b c d n q) := by
  apply Derives.disjE hc
  ·
    apply Derives.disjE (.hyp (Or.inl rfl))
    ·
      exact (.disjL (.disjL (.hyp (Or.inl rfl))))
    ·
      exact (.disjL (.disjR (.hyp (Or.inl rfl))))
  ·
    apply Derives.disjE (.hyp (Or.inl rfl))
    ·
      exact (.disjR (.disjL (.impE (.conjL (IndexFormulaRenameAtoms.membership_iff (ZFContext.add (ZFContext.add hZ _) _) w I J R S a b c d r s n q (add (add hw _) _) (add (add he _) _) (add (add hr _) _) (add (add hs _) _))) (.hyp (Or.inl rfl)))))
    ·
      apply Derives.disjE (.hyp (Or.inl rfl))
      ·
        exact (.disjR (.disjR (.disjL (.impE (.conjL (IndexFormulaRenameAtoms.equality_iff (ZFContext.add (ZFContext.add (ZFContext.add hZ _) _) _) w I J R S a b c d r s n q (add (add (add hw _) _) _) (add (add (add he _) _) _) (add (add (add hr _) _) _) (add (add (add hs _) _) _))) (.hyp (Or.inl rfl))))))
      ·
        apply Derives.disjE (.hyp (Or.inl rfl))
        ·
          exact (.disjR (.disjR (.disjR (.disjL (IndexFormulaRenameLogical.single_forward (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add hZ _) _) _) _) 4 false w I J R S a b c d n q (add (add (add (add hw _) _) _) _) (add (add (add (add he _) _) _) _) (add (add (add (add hi _) _) _) _) (.hyp (Or.inl rfl)))))))
        ·
          apply Derives.disjE (.hyp (Or.inl rfl))
          ·
            exact (.disjR (.disjR (.disjR (.disjR (.disjL (IndexFormulaRenameLogical.binary_forward 0 w I J R S a b c d n q (add (add (add (add (add he _) _) _) _) _) (add (add (add (add (add hi _) _) _) _) _) (.hyp (Or.inl rfl))))))))
          ·
            apply Derives.disjE (.hyp (Or.inl rfl))
            ·
              exact (.disjR (.disjR (.disjR (.disjR (.disjR (.disjL (IndexFormulaRenameLogical.binary_forward 1 w I J R S a b c d n q (add (add (add (add (add (add he _) _) _) _) _) _) (add (add (add (add (add (add hi _) _) _) _) _) _) (.hyp (Or.inl rfl)))))))))
            ·
              apply Derives.disjE (.hyp (Or.inl rfl))
              ·
                exact (.disjR (.disjR (.disjR (.disjR (.disjR (.disjR (.disjL (IndexFormulaRenameLogical.binary_forward 2 w I J R S a b c d n q (add (add (add (add (add (add (add he _) _) _) _) _) _) _) (add (add (add (add (add (add (add hi _) _) _) _) _) _) _) (.hyp (Or.inl rfl))))))))))
              ·
                apply Derives.disjE (.hyp (Or.inl rfl))
                ·
                  exact (.disjR (.disjR (.disjR (.disjR (.disjR (.disjR (.disjR (.disjL (IndexFormulaRenameLogical.binary_forward 3 w I J R S a b c d n q (add (add (add (add (add (add (add (add he _) _) _) _) _) _) _) _) (add (add (add (add (add (add (add (add hi _) _) _) _) _) _) _) _) (.hyp (Or.inl rfl)))))))))))
                ·
                  apply Derives.disjE (.hyp (Or.inl rfl))
                  ·
                    exact (.disjR (.disjR (.disjR (.disjR (.disjR (.disjR (.disjR (.disjR (.disjL (IndexFormulaRenameLogical.single_forward (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add hZ _) _) _) _) _) _) _) _) _) 9 true w I J R S a b c d n q (add (add (add (add (add (add (add (add (add hw _) _) _) _) _) _) _) _) _) (add (add (add (add (add (add (add (add (add he _) _) _) _) _) _) _) _) _) (add (add (add (add (add (add (add (add (add hi _) _) _) _) _) _) _) _) _) (.hyp (Or.inl rfl))))))))))))
                  ·
                    exact (.disjR (.disjR (.disjR (.disjR (.disjR (.disjR (.disjR (.disjR (.disjR (IndexFormulaRenameLogical.single_forward (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add hZ _) _) _) _) _) _) _) _) _) 10 true w I J R S a b c d n q (add (add (add (add (add (add (add (add (add hw _) _) _) _) _) _) _) _) _) (add (add (add (add (add (add (add (add (add he _) _) _) _) _) _) _) _) _) (add (add (add (add (add (add (add (add (add hi _) _) _) _) _) _) _) _) _) (.hyp (Or.inl rfl))))))))))))

end PPAC.Migration.Internal.IndexFormulaRenameCases
