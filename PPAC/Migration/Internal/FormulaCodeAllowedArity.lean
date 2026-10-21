import PPAC.Migration.Internal.FormulaCodeAllowedArityCases

/-! 全内部接受码的完整标签/实际字段数分类；所有非匹配Shape正式拒绝。 -/
namespace PPAC.Migration.Internal.FormulaCodeAllowedArity
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxNodeSyntax SyntaxTermSyntax SyntaxAtomSyntax
open FormulaCodeSyntax FormulaCodeRecursiveSyntax FormulaCodeAllowedAritySyntax
open StructuralTreeOperatorSyntax (shape shape_rename)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem membership {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f n t p l g : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxAtomSyntax.membership w b f n))
    (hs : Derives Γ (shape w n t p l g)) : Derives Γ (allowed 11 t l) := by
  let C := memberBody w b f n
  let Δ := Context.add C (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Γ))))
  apply SyntaxAtomLogic.eliminate_member w b f n _ hc
  have hwK : Derives Δ (omega w.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, omega_rename] using SyntaxAtomLogic.under_three hw C
  have hsK : Derives Δ (shape w.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc t.castSucc.castSucc.castSucc p.castSucc.castSucc.castSucc l.castSucc.castSucc.castSucc g.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, shape_rename] using SyntaxAtomLogic.under_three hs C
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have hout := FormulaCodeAllowedArityCases.constructor (SyntaxAtomLogic.zf_under_three hZ C) 3 2 (by decide) (by decide) _
    (three (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2))) _ _ _ _ _ hwK (.conjR hC) hsK
  simpa only [Formula.raise, allowed_rename] using hout

theorem equality {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f n t p l g : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxAtomSyntax.equality w b f n))
    (hs : Derives Γ (shape w n t p l g)) : Derives Γ (allowed 11 t l) := by
  let C := equalBody w b f n
  let Δ := Context.add C (Context.image Formula.raise (Context.image Formula.raise (Γ)))
  apply SyntaxAtomLogic.eliminate_equality w b f n _ hc
  have hwK : Derives Δ (omega w.castSucc.castSucc) := by
    simpa only [Formula.raise, omega_rename] using OrderedPairElimination.under_two hw C
  have hsK : Derives Δ (shape w.castSucc.castSucc n.castSucc.castSucc t.castSucc.castSucc p.castSucc.castSucc l.castSucc.castSucc g.castSucc.castSucc) := by
    simpa only [Formula.raise, shape_rename] using OrderedPairElimination.under_two hs C
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have hout := FormulaCodeAllowedArityCases.constructor (ZFContext.under_two hZ C) 2 3 (by decide) (by decide) _
    (two (Fin.last m).castSucc (Fin.last (m+1))) _ _ _ _ _ hwK (.conjR hC) hsK
  simpa only [Formula.raise, allowed_rename] using hout

theorem atomic {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f n t p l g : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxAtomSyntax.atomic w b f n))
    (hs : Derives Γ (shape w n t p l g)) : Derives Γ (allowed 11 t l) := by
  apply Derives.disjE hc
  · apply Derives.disjE (.hyp (Or.inl rfl))
    · exact FormulaCodeAllowedArityCases.constructor (ZFContext.add (ZFContext.add hZ _) _) 0 0 (by decide) (by decide)
        w Fin.elim0 n t p l g (add (add hw _) _) (.conjR (.hyp (Or.inl rfl))) (add (add hs _) _)
    · exact FormulaCodeAllowedArityCases.constructor (ZFContext.add (ZFContext.add hZ _) _) 0 1 (by decide) (by decide)
        w Fin.elim0 n t p l g (add (add hw _) _) (.conjR (.hyp (Or.inl rfl))) (add (add hs _) _)
  · apply Derives.disjE (.hyp (Or.inl rfl))
    · exact membership (ZFContext.add (ZFContext.add hZ _) _) w b f n t p l g (add (add hw _) _)
        (.hyp (Or.inl rfl)) (add (add hs _) _)
    · exact equality (ZFContext.add (ZFContext.add hZ _) _) w b f n t p l g (add (add hw _) _)
        (.hyp (Or.inl rfl)) (add (add hs _) _)

theorem accepted {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n b f t p l g : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (formulaCode w n b f))
    (hs : Derives Γ (shape w n t p l g)) : Derives Γ (allowed 11 t l) := by
  have hr := FormulaCodeRecursive.recursive_iff hZ w n b f hw
  have hh : Derives Γ ((allCases w n b f).imp (allowed 11 t l)) := by
    apply FormulaCodeCaseLogic.all_imp w n b f (allowed 11 t l)
    · apply Derives.impI
      exact atomic (ZFContext.add hZ _) w b f n t p l g (add hw _) (.hyp (Or.inl rfl)) (add hs _)
    · apply Derives.impI
      exact FormulaCodeAllowedArityCases.single (ZFContext.add hZ _) 4 false (by decide) (by decide)
        w b f n t p l g (add hw _) (.hyp (Or.inl rfl)) (add hs _)
    · apply Derives.impI
      exact FormulaCodeAllowedArityCases.binary (ZFContext.add hZ _) 0
        w b f n t p l g (add hw _) (.hyp (Or.inl rfl)) (add hs _)
    · apply Derives.impI
      exact FormulaCodeAllowedArityCases.binary (ZFContext.add hZ _) 1
        w b f n t p l g (add hw _) (.hyp (Or.inl rfl)) (add hs _)
    · apply Derives.impI
      exact FormulaCodeAllowedArityCases.binary (ZFContext.add hZ _) 2
        w b f n t p l g (add hw _) (.hyp (Or.inl rfl)) (add hs _)
    · apply Derives.impI
      exact FormulaCodeAllowedArityCases.binary (ZFContext.add hZ _) 3
        w b f n t p l g (add hw _) (.hyp (Or.inl rfl)) (add hs _)
    · apply Derives.impI
      exact FormulaCodeAllowedArityCases.single (ZFContext.add hZ _) 9 true (by decide) (by decide)
        w b f n t p l g (add hw _) (.hyp (Or.inl rfl)) (add hs _)
    · apply Derives.impI
      exact FormulaCodeAllowedArityCases.single (ZFContext.add hZ _) 10 true (by decide) (by decide)
        w b f n t p l g (add hw _) (.hyp (Or.inl rfl)) (add hs _)
  exact .impE hh (.conjR (.impE (.conjL hr) hc))

theorem reject {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n b f t p l g : Fin m)
    (hw : Derives Γ (omega w)) (hs : Derives Γ (shape w n t p l g))
    (hb : Derives Γ (allowed 11 t l).neg) : Derives Γ (formulaCode w n b f).neg := by
  apply Derives.impI
  exact .impE (add hb _) (accepted (ZFContext.add hZ _) w n b f t p l g (add hw _) (.hyp (Or.inl rfl)) (add hs _))
end PPAC.Migration.Internal.FormulaCodeAllowedArity
