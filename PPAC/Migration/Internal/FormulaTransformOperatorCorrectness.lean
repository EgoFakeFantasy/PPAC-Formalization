import PPAC.Migration.Internal.FormulaTransformCongruence

/-! 新编译状态集合算子与原算子逐候选等价；全部历史图均为内部对象。 -/
namespace PPAC.Migration.Internal.FormulaTransformOperatorCorrectness
open Source SourceAlgebra SourceLogic OmegaSyntax FormulaCodeCongruence SyntaxTypeLocalTransfer FormulaTransformCongruence
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem row_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n h p : Fin m)
    (hw : Derives Γ (omega w)) :
    Derives Γ ((FormulaTransformOperatorSyntax.row w n h p).iff (SyntaxMixedFormulaOperatorSyntax.row w n h p)) := by
  apply ex_congr
  apply ex_congr
  apply ex_congr
  apply ex_congr
  apply ex_congr
  apply ex_congr
  apply ex_congr
  have hZ1 := ZFContext.rename hZ Fin.castSucc
  have hw1 := Derives.rename Fin.castSucc hw
  have hZ2 := ZFContext.rename hZ1 Fin.castSucc
  have hw2 := Derives.rename Fin.castSucc hw1
  have hZ3 := ZFContext.rename hZ2 Fin.castSucc
  have hw3 := Derives.rename Fin.castSucc hw2
  have hZ4 := ZFContext.rename hZ3 Fin.castSucc
  have hw4 := Derives.rename Fin.castSucc hw3
  have hZ5 := ZFContext.rename hZ4 Fin.castSucc
  have hw5 := Derives.rename Fin.castSucc hw4
  have hZ6 := ZFContext.rename hZ5 Fin.castSucc
  have hw6 := Derives.rename Fin.castSucc hw5
  have hZ7 := ZFContext.rename hZ6 Fin.castSucc
  have hw7 := Derives.rename Fin.castSucc hw6
  exact conj_congr (iff_refl (SyntaxMixedFormulaStateSyntax.state w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc.castSucc.castSucc (Fin.last (m+4)).castSucc.castSucc (Fin.last (m+5)).castSucc (Fin.last (m+6)) p.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) (FormulaTransformStepCorrectness.step_iff hZ7 w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc.castSucc.castSucc (Fin.last (m+4)).castSucc.castSucc (Fin.last (m+5)).castSucc h.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+6)) (of_eq (by simp only [omega_rename]) hw7))

theorem value_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n h v : Fin m)
    (hw : Derives Γ (omega w)) :
    Derives Γ ((FormulaTransformOperatorSyntax.value w n h v).iff (SyntaxMixedFormulaOperatorSyntax.value w n h v)) := by
  apply all_congr
  have hw1 : Derives (Context.image Formula.raise Γ) (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (Derives.rename Fin.castSucc hw)
  have hr := row_iff (ZFContext.rename hZ Fin.castSucc) w.castSucc n.castSucc h.castSucc (Fin.last m) hw1
  have ho := iff_congr (iff_refl (Formula.mem (Fin.last m) v.castSucc))
    (conj_congr (iff_refl (Formula.mem (Fin.last m) w.castSucc)) hr)
  exact of_eq (by simp only [MinimalPredicates.satisfying, FormulaTransformOperatorSyntax.selection_at, SyntaxMixedFormulaOperatorSyntax.selection_at]; rfl) ho

end PPAC.Migration.Internal.FormulaTransformOperatorCorrectness
