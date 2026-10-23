import PPAC.Migration.Internal.FormulaTransformProgramSyntax

/-! 实际项程序调用与旧原子判断对应；全部内部码／元数据保持对象变量。 -/
namespace PPAC.Migration.Internal.FormulaTransformAtomCorrectness
open Source SourceAlgebra SourceLogic OmegaSyntax FormulaCodeCongruence SyntaxTypeLocalTransfer
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem membership_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S a b c d n q : Fin m)
    (hw : Derives Γ (omega w)) :
    Derives Γ ((FormulaTransformAtomSyntax.membership w R S a b c d n q).iff (SyntaxMixedFormulaAtomSyntax.membership w R S a b c d n q)) := by
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
  exact conj_congr (iff_refl (SyntaxAtomSyntax.zeroScalar w.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc.castSucc)) (conj_congr (iff_refl (SyntaxAtomSyntax.memberCode w.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc.castSucc)) (conj_congr (iff_refl (SyntaxAtomSyntax.memberCode w.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc (Fin.last (m+4)) q.castSucc.castSucc.castSucc.castSucc.castSucc)) (conj_congr (TermTransformProgramCorrectness.checked_iff hZ5 w.castSucc.castSucc.castSucc.castSucc.castSucc R.castSucc.castSucc.castSucc.castSucc.castSucc S.castSucc.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc (of_eq (by simp only [omega_rename]) hw5)) (TermTransformProgramCorrectness.checked_iff hZ5 w.castSucc.castSucc.castSucc.castSucc.castSucc R.castSucc.castSucc.castSucc.castSucc.castSucc S.castSucc.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc (Fin.last (m+4)) (of_eq (by simp only [omega_rename]) hw5)))))

theorem equality_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S a b c d n q : Fin m)
    (hw : Derives Γ (omega w)) :
    Derives Γ ((FormulaTransformAtomSyntax.equality w R S a b c d n q).iff (SyntaxMixedFormulaAtomSyntax.equality w R S a b c d n q)) := by
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
  exact conj_congr (iff_refl (SyntaxAtomSyntax.equalCode w.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc)) (conj_congr (iff_refl (SyntaxAtomSyntax.equalCode w.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+3)) q.castSucc.castSucc.castSucc.castSucc)) (conj_congr (TermTransformProgramCorrectness.checked_iff hZ4 w.castSucc.castSucc.castSucc.castSucc R.castSucc.castSucc.castSucc.castSucc S.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc (of_eq (by simp only [omega_rename]) hw4)) (TermTransformProgramCorrectness.checked_iff hZ4 w.castSucc.castSucc.castSucc.castSucc R.castSucc.castSucc.castSucc.castSucc S.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc (Fin.last (m+3)) (of_eq (by simp only [omega_rename]) hw4))))

end PPAC.Migration.Internal.FormulaTransformAtomCorrectness
