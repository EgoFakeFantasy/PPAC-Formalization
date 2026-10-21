import PPAC.Migration.Internal.FormulaCodeTypedDataSyntax

/-! 原11分支到无Constructor参数的真实图类型分类；所有原字段见证均在对象层消去。 -/
namespace PPAC.Migration.Internal.FormulaCodeTypedDataCases
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxNodeSyntax SyntaxAtomSyntax
open FormulaCodeSyntax FormulaCodeRecursiveSyntax FormulaCodeTypedDataSyntax
open StructuralTreeOperatorSyntax (shape shape_rename)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem at_constructor {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k tag : Nat)
    (ht : tag < 11) (hk : k = FormulaCodeAllowedAritySyntax.expectedArity tag) (w : Fin m) (xs : Fin k → Fin m)
    (n t p l g b f : Fin m) (hw : Derives Γ (omega w)) (hc : Derives Γ (constructor k tag w xs n))
    (hs : Derives Γ (shape w n t p l g)) (hp : Derives Γ (rootCheck tag w g b f)) :
    Derives Γ (cases 11 w t l g b f) := by
  have ha := FormulaCodeFieldArity.constructor_tag hZ k tag w xs n t p l g hw hc hs
  have hl := FormulaCodeFieldArity.constructor_length hZ k tag w xs n t p l g hw hc hs
  apply intro_cases 11 tag ht w t l g b f ha _ hp
  simpa only [hk] using hl

theorem nullary {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (truth : Bool) (w n b f t p l g : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxAtomSyntax.nullary truth w b f n))
    (hs : Derives Γ (shape w n t p l g)) : Derives Γ (cases 11 w t l g b f) := by
  apply at_constructor hZ 0 (nullaryTag truth) (by cases truth <;> decide) (by cases truth <;> decide)
    w Fin.elim0 n t p l g b f hw (.conjR hc) hs
  cases truth <;> exact .conjL hc

theorem membership {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n b f t p l g : Fin m)
    (hw : Derives Γ (omega w)) (hf : Derives Γ (formulaCode w n b f)) (hs : Derives Γ (shape w n t p l g))
    (hc : Derives Γ (SyntaxAtomSyntax.membership w b f n)) : Derives Γ (cases 11 w t l g b f) := by
  let C := memberBody w b f n
  let Δ := Context.add C (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Γ))))
  apply SyntaxAtomLogic.eliminate_member w b f n _ hc
  have hZK := SyntaxAtomLogic.zf_under_three hZ C
  have hwK : Derives Δ (omega w.castSucc.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using SyntaxAtomLogic.under_three hw C
  have hfK : Derives Δ (formulaCode w.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, formulaCode_rename] using SyntaxAtomLogic.under_three hf C
  have hsK : Derives Δ (shape w.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc t.castSucc.castSucc.castSucc p.castSucc.castSucc.castSucc l.castSucc.castSucc.castSucc g.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, shape_rename] using SyntaxAtomLogic.under_three hs C
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have hh := FormulaCodeGraphTyping.membership hZK w.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2)) t.castSucc.castSucc.castSucc p.castSucc.castSucc.castSucc l.castSucc.castSucc.castSucc g.castSucc.castSucc.castSucc hwK (.conjR hC) hsK
  have hout := at_constructor hZK 3 2 (by decide) (by decide) _ (three (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2))) _ _ _ _ _ _ _
    hwK (.conjR hC) hsK (.impE (.conjL hh) hfK)
  simpa only [Formula.raise, cases_rename] using hout

theorem equality {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n b f t p l g : Fin m)
    (hw : Derives Γ (omega w)) (hf : Derives Γ (formulaCode w n b f)) (hs : Derives Γ (shape w n t p l g))
    (hc : Derives Γ (SyntaxAtomSyntax.equality w b f n)) : Derives Γ (cases 11 w t l g b f) := by
  let C := equalBody w b f n
  let Δ := Context.add C (Context.image Formula.raise (Context.image Formula.raise (Γ)))
  apply SyntaxAtomLogic.eliminate_equality w b f n _ hc
  have hZK := ZFContext.under_two hZ C
  have hwK : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using OrderedPairElimination.under_two hw C
  have hfK : Derives Δ (formulaCode w.castSucc.castSucc n.castSucc.castSucc b.castSucc.castSucc f.castSucc.castSucc) := by
    simpa only [Formula.raise, formulaCode_rename] using OrderedPairElimination.under_two hf C
  have hsK : Derives Δ (shape w.castSucc.castSucc n.castSucc.castSucc t.castSucc.castSucc p.castSucc.castSucc l.castSucc.castSucc g.castSucc.castSucc) := by
    simpa only [Formula.raise, shape_rename] using OrderedPairElimination.under_two hs C
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have hh := FormulaCodeGraphTyping.equality hZK w.castSucc.castSucc n.castSucc.castSucc b.castSucc.castSucc f.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) t.castSucc.castSucc p.castSucc.castSucc l.castSucc.castSucc g.castSucc.castSucc hwK (.conjR hC) hsK
  have hout := at_constructor hZK 2 3 (by decide) (by decide) _ (two (Fin.last m).castSucc (Fin.last (m+1))) _ _ _ _ _ _ _
    hwK (.conjR hC) hsK (.impE (.conjL hh) hfK)
  simpa only [Formula.raise, cases_rename] using hout

theorem atomic {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n b f t p l g : Fin m)
    (hw : Derives Γ (omega w)) (hf : Derives Γ (formulaCode w n b f)) (hs : Derives Γ (shape w n t p l g))
    (hc : Derives Γ (SyntaxAtomSyntax.atomic w b f n)) : Derives Γ (cases 11 w t l g b f) := by
  apply Derives.disjE hc
  · apply Derives.disjE (.hyp (Or.inl rfl))
    · exact nullary (ZFContext.add (ZFContext.add hZ _) _) false w n b f t p l g (add (add hw _) _) (.hyp (Or.inl rfl)) (add (add hs _) _)
    · exact nullary (ZFContext.add (ZFContext.add hZ _) _) true w n b f t p l g (add (add hw _) _) (.hyp (Or.inl rfl)) (add (add hs _) _)
  · apply Derives.disjE (.hyp (Or.inl rfl))
    · exact membership (ZFContext.add (ZFContext.add hZ _) _) w n b f t p l g (add (add hw _) _) (add (add hf _) _) (add (add hs _) _) (.hyp (Or.inl rfl))
    · exact equality (ZFContext.add (ZFContext.add hZ _) _) w n b f t p l g (add (add hw _) _) (add (add hf _) _) (add (add hs _) _) (.hyp (Or.inl rfl))

theorem negation {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n b f t p l g : Fin m)
    (hw : Derives Γ (omega w)) (hf : Derives Γ (formulaCode w n b f)) (hs : Derives Γ (shape w n t p l g))
    (hc : Derives Γ (singleCase 4 false w b f n)) : Derives Γ (cases 11 w t l g b f) := by
  let C := singleCaseBody 4 false w b f n
  let Δ := Context.add C (Context.image Formula.raise Γ)
  apply eliminate_single 4 false w b f n _ hc
  have hZ1 := ZFContext.under hZ C
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw C
  have hf1 : Derives Δ (formulaCode w.castSucc n.castSucc b.castSucc f.castSucc) := by
    simpa only [Formula.raise, formulaCode_rename] using under hf C
  have hs1 : Derives Δ (shape w.castSucc n.castSucc t.castSucc p.castSucc l.castSucc g.castSucc) := by
    simpa only [Formula.raise, shape_rename] using under hs C
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have hh := FormulaCodeGraphTyping.negation hZ1 w.castSucc n.castSucc b.castSucc f.castSucc (Fin.last m)
    t.castSucc p.castSucc l.castSucc g.castSucc hw1 (.conjL hC) hs1
  have hout := at_constructor hZ1 1 4 (by decide) (by decide) w.castSucc (fun _ => Fin.last m)
    n.castSucc t.castSucc p.castSucc l.castSucc g.castSucc b.castSucc f.castSucc hw1 (.conjL hC) hs1 (.impE (.conjL hh) hf1)
  simpa only [Formula.raise, cases_rename] using hout

theorem universal {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n b f t p l g : Fin m)
    (hw : Derives Γ (omega w)) (hf : Derives Γ (formulaCode w n b f)) (hs : Derives Γ (shape w n t p l g))
    (hc : Derives Γ (singleCase 9 true w b f n)) : Derives Γ (cases 11 w t l g b f) := by
  let C := singleCaseBody 9 true w b f n
  let Δ := Context.add C (Context.image Formula.raise Γ)
  apply eliminate_single 9 true w b f n _ hc
  have hZ1 := ZFContext.under hZ C
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw C
  have hf1 : Derives Δ (formulaCode w.castSucc n.castSucc b.castSucc f.castSucc) := by
    simpa only [Formula.raise, formulaCode_rename] using under hf C
  have hs1 : Derives Δ (shape w.castSucc n.castSucc t.castSucc p.castSucc l.castSucc g.castSucc) := by
    simpa only [Formula.raise, shape_rename] using under hs C
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have hh := FormulaCodeGraphTyping.quantifier hZ1 true w.castSucc n.castSucc b.castSucc f.castSucc (Fin.last m)
    t.castSucc p.castSucc l.castSucc g.castSucc hw1 (.conjL hC) hs1
  have hout := at_constructor hZ1 1 9 (by decide) (by decide) w.castSucc (fun _ => Fin.last m)
    n.castSucc t.castSucc p.castSucc l.castSucc g.castSucc b.castSucc f.castSucc hw1 (.conjL hC) hs1 (.impE (.conjL hh) hf1)
  simpa only [Formula.raise, cases_rename] using hout

theorem existential {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n b f t p l g : Fin m)
    (hw : Derives Γ (omega w)) (hf : Derives Γ (formulaCode w n b f)) (hs : Derives Γ (shape w n t p l g))
    (hc : Derives Γ (singleCase 10 true w b f n)) : Derives Γ (cases 11 w t l g b f) := by
  let C := singleCaseBody 10 true w b f n
  let Δ := Context.add C (Context.image Formula.raise Γ)
  apply eliminate_single 10 true w b f n _ hc
  have hZ1 := ZFContext.under hZ C
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw C
  have hf1 : Derives Δ (formulaCode w.castSucc n.castSucc b.castSucc f.castSucc) := by
    simpa only [Formula.raise, formulaCode_rename] using under hf C
  have hs1 : Derives Δ (shape w.castSucc n.castSucc t.castSucc p.castSucc l.castSucc g.castSucc) := by
    simpa only [Formula.raise, shape_rename] using under hs C
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have hh := FormulaCodeGraphTyping.quantifier hZ1 false w.castSucc n.castSucc b.castSucc f.castSucc (Fin.last m)
    t.castSucc p.castSucc l.castSucc g.castSucc hw1 (.conjL hC) hs1
  have hout := at_constructor hZ1 1 10 (by decide) (by decide) w.castSucc (fun _ => Fin.last m)
    n.castSucc t.castSucc p.castSucc l.castSucc g.castSucc b.castSucc f.castSucc hw1 (.conjL hC) hs1 (.impE (.conjL hh) hf1)
  simpa only [Formula.raise, cases_rename] using hout

theorem binary {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4) (w n b f t p l g : Fin m)
    (hw : Derives Γ (omega w)) (hf : Derives Γ (formulaCode w n b f)) (hs : Derives Γ (shape w n t p l g))
    (hc : Derives Γ (binaryCase kind w b f n)) : Derives Γ (cases 11 w t l g b f) := by
  let C := binaryCaseBody kind w b f n
  let Δ := Context.add C (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_binary kind w b f n _ hc
  have hZ2 := ZFContext.under_two hZ C
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using OrderedPairElimination.under_two hw C
  have hf2 : Derives Δ (formulaCode w.castSucc.castSucc n.castSucc.castSucc b.castSucc.castSucc f.castSucc.castSucc) := by
    simpa only [Formula.raise, formulaCode_rename] using OrderedPairElimination.under_two hf C
  have hs2 : Derives Δ (shape w.castSucc.castSucc n.castSucc.castSucc t.castSucc.castSucc p.castSucc.castSucc l.castSucc.castSucc g.castSucc.castSucc) := by
    simpa only [Formula.raise, shape_rename] using OrderedPairElimination.under_two hs C
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have hh := FormulaCodeGraphTyping.binary hZ2 kind w.castSucc.castSucc n.castSucc.castSucc b.castSucc.castSucc f.castSucc.castSucc
    (Fin.last m).castSucc (Fin.last (m+1)) t.castSucc.castSucc p.castSucc.castSucc l.castSucc.castSucc g.castSucc.castSucc hw2 (.conjL hC) hs2
  have hk : kind = 0 ∨ kind = 1 ∨ kind = 2 ∨ kind = 3 := by omega
  have hbound : SyntaxLogicalSyntax.binaryTag kind < 11 := by simp only [SyntaxLogicalSyntax.binaryTag]; omega
  have hcount : 2 = FormulaCodeAllowedAritySyntax.expectedArity (SyntaxLogicalSyntax.binaryTag kind) := by
    rcases hk with rfl | rfl | rfl | rfl <;> decide
  have htest : rootCheck (SyntaxLogicalSyntax.binaryTag kind) w.castSucc.castSucc g.castSucc.castSucc b.castSucc.castSucc f.castSucc.castSucc =
      FormulaCodeGraphTyping.binaryCheck w.castSucc.castSucc g.castSucc.castSucc b.castSucc.castSucc f.castSucc.castSucc := by
    rcases hk with rfl | rfl | rfl | rfl <;> rfl
  have hcheck : Derives Δ (rootCheck (SyntaxLogicalSyntax.binaryTag kind) w.castSucc.castSucc g.castSucc.castSucc b.castSucc.castSucc f.castSucc.castSucc) := by
    rw [htest]
    exact .impE (.conjL hh) hf2
  have hout := at_constructor hZ2 2 (SyntaxLogicalSyntax.binaryTag kind) hbound hcount _
    (two (Fin.last m).castSucc (Fin.last (m+1))) _ _ _ _ _ _ _ hw2 (.conjL hC) hs2 hcheck
  simpa only [Formula.raise, cases_rename] using hout
end PPAC.Migration.Internal.FormulaCodeTypedDataCases
