import PPAC.Migration.Internal.SyntaxTypeCaseTransfer

/-! 只用原源规则组合对象双条件；完整11分支的历史读取迁移。 -/
namespace PPAC.Migration.Internal.SyntaxTypeLocalTransfer
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxTypeRecursionSyntax SyntaxFormulaLocalSyntax SyntaxTypeRecursiveSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem iff_refl {m} {Γ : Context m} (p : Formula m) : Derives Γ (p.iff p) :=
  .conjI (.impI (.hyp (Or.inl rfl))) (.impI (.hyp (Or.inl rfl)))

theorem iff_trans {m} {Γ : Context m} {p q r : Formula m}
    (hp : Derives Γ (p.iff q)) (hq : Derives Γ (q.iff r)) : Derives Γ (p.iff r) := by
  apply Derives.conjI
  · apply Derives.impI
    exact .impE (add (.conjL hq) _) (.impE (add (.conjL hp) _) (.hyp (Or.inl rfl)))
  · apply Derives.impI
    exact .impE (add (.conjR hp) _) (.impE (add (.conjR hq) _) (.hyp (Or.inl rfl)))

theorem disj_congr {m} {Γ : Context m} {p p' q q' : Formula m}
    (hp : Derives Γ (p.iff p')) (hq : Derives Γ (q.iff q')) : Derives Γ ((p.disj q).iff (p'.disj q')) := by
  apply Derives.conjI
  · apply Derives.impI
    apply Derives.disjE (.hyp (Or.inl rfl))
    · exact .disjL (.impE (add (add (.conjL hp) _) _) (.hyp (Or.inl rfl)))
    · exact .disjR (.impE (add (add (.conjL hq) _) _) (.hyp (Or.inl rfl)))
  · apply Derives.impI
    apply Derives.disjE (.hyp (Or.inl rfl))
    · exact .disjL (.impE (add (add (.conjR hp) _) _) (.hyp (Or.inl rfl)))
    · exact .disjR (.impE (add (add (.conjR hq) _) _) (.hyp (Or.inl rfl)))

theorem all_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w c b f h n : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w)) (hg : Derives Γ (graph w c h n)) :
    Derives Γ ((localType w b f h n).iff (allCases w c n b f)) := by
  exact disj_congr (iff_refl (SyntaxAtomSyntax.atomic w b f n))
    (disj_congr (SyntaxTypeCaseTransfer.single_iff hZ 4 false w c b f h n hw hn hg)
      (disj_congr (SyntaxTypeCaseTransfer.binary_iff hZ 0 w c b f h n hw hn hg)
        (disj_congr (SyntaxTypeCaseTransfer.binary_iff hZ 1 w c b f h n hw hn hg)
          (disj_congr (SyntaxTypeCaseTransfer.binary_iff hZ 2 w c b f h n hw hn hg)
            (disj_congr (SyntaxTypeCaseTransfer.binary_iff hZ 3 w c b f h n hw hn hg)
              (disj_congr (SyntaxTypeCaseTransfer.single_iff hZ 9 true w c b f h n hw hn hg)
                (SyntaxTypeCaseTransfer.single_iff hZ 10 true w c b f h n hw hn hg)))))))
end PPAC.Migration.Internal.SyntaxTypeLocalTransfer
