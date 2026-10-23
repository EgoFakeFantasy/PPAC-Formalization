import PPAC.Migration.Internal.PureSyntaxFormulaSound

/-! 全十一公式构造的真实查询构造及全上下文归纳步骤。 -/
namespace PPAC.Migration.Internal.PureSyntaxFormulaComplete
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PureSyntaxFormulaInductionSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem single_case_checked {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 3) (w b f n : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (allIH w n))
    (hs : Derives Γ (FormulaCodeRecursiveSyntax.singleCase (PureSyntaxUnarySyntax.tag kind) (PureSyntaxUnarySyntax.advance kind) w b f n)) :
    Derives Γ (PureSyntaxTrace.formula w b f n) := by
  let B := FormulaCodeRecursiveSyntax.singleCaseBody (PureSyntaxUnarySyntax.tag kind) (PureSyntaxUnarySyntax.advance kind) w b f n
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply FormulaCodeRecursiveSyntax.eliminate_single (PureSyntaxUnarySyntax.tag kind) (PureSyntaxUnarySyntax.advance kind) w b f n _ hs
  have hZ1 := ZFContext.under hZ B
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hi1 : Derives Δ (allIH w.castSucc n.castSucc) := of_eq (allIH_rename w n Fin.castSucc) (under hi B)
  have hc1 : Derives Δ (SyntaxTermSyntax.contexts w.castSucc b.castSucc f.castSucc) := of_eq (SyntaxTermSyntax.contexts_rename w b f Fin.castSucc) (under (.conjL hs) B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hout := PureSyntaxUnaryComplete.checked_from_step hZ1 kind w.castSucc b.castSucc f.castSucc (Fin.last m) n.castSucc hw1 hi1 hc1 (.conjR (.conjR hB)) (.conjL hB)
  exact of_eq (PureSyntaxTrace.formula_rename w b f n Fin.castSucc).symm hout

theorem binary_case_checked {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4) (w b f n : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (allIH w n))
    (ht : Derives Γ (FormulaCodeSyntax.formulaCode w n b f))
    (hs : Derives Γ (FormulaCodeRecursiveSyntax.binaryCase kind w b f n)) :
    Derives Γ (PureSyntaxTrace.formula w b f n) := by
  let B := FormulaCodeRecursiveSyntax.binaryCaseBody kind w b f n
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply FormulaCodeRecursiveSyntax.eliminate_binary kind w b f n _ hs
  have hZ2 := ZFContext.under_two hZ B
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (OrderedPairElimination.under_two hw B)
  have hi2 : Derives Δ (allIH w.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [Formula.raise, allIH_rename]) (OrderedPairElimination.under_two hi B)
  have ht2 : Derives Δ (FormulaCodeSyntax.formulaCode w.castSucc.castSucc n.castSucc.castSucc b.castSucc.castSucc f.castSucc.castSucc) := of_eq (by simp only [Formula.raise, FormulaCodeSyntax.formulaCode_rename]) (OrderedPairElimination.under_two ht B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hout := PureSyntaxBinaryComplete.typed_binary_checked hZ2 kind w.castSucc.castSucc b.castSucc.castSucc f.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) n.castSucc.castSucc hw2 hi2 ht2 (.conjL hB)
  exact of_eq (by simp only [Formula.raise, PureSyntaxTrace.formula_rename]) hout

theorem checked_complete {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f n : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (allIH w n))
    (ht : Derives Γ (FormulaCodeSyntax.formulaCode w n b f)) :
    Derives Γ (PureSyntaxTrace.formula w b f n) := by
  have hcases := Derives.conjR (Derives.impE (.conjL (FormulaCodeRecursive.recursive_iff hZ w n b f hw)) ht)
  apply Derives.disjE hcases
  · exact PureSyntaxAtomicComplete.checked_atomic (ZFContext.add hZ _) w b f n (add hw _) (.hyp (Or.inl rfl))
  · apply Derives.disjE (.hyp (Or.inl rfl))
    · exact single_case_checked (ZFContext.add (ZFContext.add hZ _) _) 0 w b f n (add (add hw _) _) (add (add hi _) _) (.hyp (Or.inl rfl))
    · apply Derives.disjE (.hyp (Or.inl rfl))
      · exact binary_case_checked (ZFContext.add (ZFContext.add (ZFContext.add hZ _) _) _) 0 w b f n (add (add (add hw _) _) _) (add (add (add hi _) _) _) (add (add (add ht _) _) _) (.hyp (Or.inl rfl))
      · apply Derives.disjE (.hyp (Or.inl rfl))
        · exact binary_case_checked (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add hZ _) _) _) _) 1 w b f n (add (add (add (add hw _) _) _) _) (add (add (add (add hi _) _) _) _) (add (add (add (add ht _) _) _) _) (.hyp (Or.inl rfl))
        · apply Derives.disjE (.hyp (Or.inl rfl))
          · exact binary_case_checked (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add hZ _) _) _) _) _) 2 w b f n (add (add (add (add (add hw _) _) _) _) _) (add (add (add (add (add hi _) _) _) _) _) (add (add (add (add (add ht _) _) _) _) _) (.hyp (Or.inl rfl))
          · apply Derives.disjE (.hyp (Or.inl rfl))
            · exact binary_case_checked (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add hZ _) _) _) _) _) _) 3 w b f n (add (add (add (add (add (add hw _) _) _) _) _) _) (add (add (add (add (add (add hi _) _) _) _) _) _) (add (add (add (add (add (add ht _) _) _) _) _) _) (.hyp (Or.inl rfl))
            · apply Derives.disjE (.hyp (Or.inl rfl))
              · exact single_case_checked (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add hZ _) _) _) _) _) _) _) 1 w b f n (add (add (add (add (add (add (add hw _) _) _) _) _) _) _) (add (add (add (add (add (add (add hi _) _) _) _) _) _) _) (.hyp (Or.inl rfl))
              · exact single_case_checked (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add hZ _) _) _) _) _) _) _) 2 w b f n (add (add (add (add (add (add (add hw _) _) _) _) _) _) _) (add (add (add (add (add (add (add hi _) _) _) _) _) _) _) (.hyp (Or.inl rfl))

theorem checked_iff_from_induction {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f n : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (allIH w n)) :
    Derives Γ ((PureSyntaxTrace.formula w b f n).iff (FormulaCodeSyntax.formulaCode w n b f)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact PureSyntaxFormulaSound.checked_sound (ZFContext.add hZ _) w b f n (add hw _) (add hi _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact checked_complete (ZFContext.add hZ _) w b f n (add hw _) (add hi _) (.hyp (Or.inl rfl))

theorem correct_from_induction {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (allIH w n)) : Derives Γ (correct w n) := by
  apply OriginalUniversalBlock.intro_many 2 (body w n)
  have hw1 := of_eq (omega_rename w (old 2)) (HornBinderRules.under_many 2 hw)
  have hi1 := of_eq (allIH_rename w n (old 2)) (HornBinderRules.under_many 2 hi)
  exact checked_iff_from_induction (HornBinderRules.zf_many 2 hZ) (old 2 w) (slot 2 0) (slot 2 1) (old 2 n) hw1 hi1

end PPAC.Migration.Internal.PureSyntaxFormulaComplete
