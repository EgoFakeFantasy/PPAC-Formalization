import PPAC.Migration.Internal.SyntaxRenameLogicalOutput

/-! 全11构造的对象输出归纳推进；源分类的全部字段存在前提均被正式消去。 -/
namespace PPAC.Migration.Internal.SyntaxRenameOutputPoint
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax SyntaxRenameOutputSyntax SyntaxRenameBinders
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem single_case_property {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (advance : Bool)
    (valid : (tag = 4 ∧ advance = false) ∨ (tag = 9 ∧ advance = true) ∨ (tag = 10 ∧ advance = true))
    (w n b f : Fin m) (hw : Derives Γ (omega w)) (he : Derives Γ (earlier w n))
    (hc : Derives Γ (FormulaCodeRecursiveSyntax.singleCase tag advance w b f n)) : Derives Γ (property w n) := by
  let B := FormulaCodeRecursiveSyntax.singleCaseBody tag advance w b f n
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply FormulaCodeRecursiveSyntax.eliminate_single tag advance w b f n _ hc
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have he1 : Derives Δ (earlier w.castSucc n.castSucc) := of_eq (earlier_rename w n Fin.castSucc) (under he B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := SyntaxRenameLogicalOutput.single_property_step (ZFContext.under hZ B) tag advance valid w.castSucc n.castSucc (Fin.last m) hw1 he1 (.conjL hB)
  exact of_eq (property_rename w n Fin.castSucc).symm ho

theorem binary_case_property {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4)
    (w n b f : Fin m) (hw : Derives Γ (omega w)) (he : Derives Γ (earlier w n))
    (hc : Derives Γ (FormulaCodeRecursiveSyntax.binaryCase kind w b f n)) : Derives Γ (property w n) := by
  let B := FormulaCodeRecursiveSyntax.binaryCaseBody kind w b f n
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply FormulaCodeRecursiveSyntax.eliminate_binary kind w b f n _ hc
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under_2 hw B)
  have he2 : Derives Δ (earlier w.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [Formula.raise, earlier_rename]) (under_2 he B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := SyntaxRenameLogicalOutput.binary_property_step (zf_under_2 hZ B) kind w.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hw2 he2 (.conjL hB)
  exact of_eq (by simp only [Formula.raise, property_rename]) ho

theorem property_of_code {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n b f : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (earlier w n))
    (hc : Derives Γ (FormulaCodeSyntax.formulaCode w n b f)) : Derives Γ (property w n) := by
  have hr := FormulaCodeRecursive.recursive_iff hZ w n b f hw
  have hh : Derives Γ ((FormulaCodeRecursiveSyntax.allCases w n b f).imp (property w n)) := by
    apply FormulaCodeCaseLogic.all_imp w n b f (property w n)
    · apply Derives.impI
      exact SyntaxRenameAtomicBase.property_of_atomic (ZFContext.add hZ _) w b f n (add hw _) (.hyp (Or.inl rfl))
    · apply Derives.impI
      exact single_case_property (ZFContext.add hZ _) 4 false (Or.inl ⟨rfl, rfl⟩) w n b f (add hw _) (add he _) (.hyp (Or.inl rfl))

    · apply Derives.impI
      exact binary_case_property (ZFContext.add hZ _) 0 w n b f (add hw _) (add he _) (.hyp (Or.inl rfl))
    · apply Derives.impI
      exact binary_case_property (ZFContext.add hZ _) 1 w n b f (add hw _) (add he _) (.hyp (Or.inl rfl))
    · apply Derives.impI
      exact binary_case_property (ZFContext.add hZ _) 2 w n b f (add hw _) (add he _) (.hyp (Or.inl rfl))
    · apply Derives.impI
      exact binary_case_property (ZFContext.add hZ _) 3 w n b f (add hw _) (add he _) (.hyp (Or.inl rfl))
    · apply Derives.impI
      exact single_case_property (ZFContext.add hZ _) 9 true (Or.inr (Or.inl ⟨rfl, rfl⟩)) w n b f (add hw _) (add he _) (.hyp (Or.inl rfl))
    · apply Derives.impI
      exact single_case_property (ZFContext.add hZ _) 10 true (Or.inr (Or.inr ⟨rfl, rfl⟩)) w n b f (add hw _) (add he _) (.hyp (Or.inl rfl))
  exact .impE hh (.conjR (.impE (.conjL hr) hc))

theorem property_from_earlier {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (earlier w n)) : Derives Γ (property w n) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let I := input w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc.castSucc (Fin.last (m+4)).castSucc (Fin.last (m+5)) n.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc
  let Δ := Context.add I (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Γ)))))))
  have hw6 : Derives Δ (omega w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under_6 hw I)
  have he6 : Derives Δ (earlier w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, earlier_rename]) (under_6 he I)
  have hI : Derives Δ I := .hyp (Or.inl rfl)
  have hp := property_of_code (zf_under_6 hZ I) w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc.castSucc hw6 he6 (.conjL hI)
  exact .impE (property_at w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc.castSucc (Fin.last (m+4)).castSucc (Fin.last (m+5)) hp) hI
end PPAC.Migration.Internal.SyntaxRenameOutputPoint
