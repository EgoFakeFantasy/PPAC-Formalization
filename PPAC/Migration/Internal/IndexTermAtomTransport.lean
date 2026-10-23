import PPAC.Migration.Internal.IndexTermImageCodeFields

/-! 实际变量项像环境下，成员／等词指令与原索引重命名原子判断全内部对应。 -/
namespace PPAC.Migration.Internal.IndexTermAtomTransport
open Source SourceAlgebra SourceLogic OmegaSyntax IndexTermRenameTransportSyntax FormulaCodeCongruence SyntaxTypeLocalTransfer
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem membership_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s f g a b c d R S n q : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (realization w r s f g a b c d R S)) :
    Derives Γ ((FormulaTransformAtomSyntax.membership w R S a b c d n q).iff (SyntaxRenameAtomSyntax.membership w r s a b c d n q)) := by
  apply ex_congr
  apply ex_congr
  apply ex_congr
  apply ex_congr
  apply ex_congr
  have hZ1 := ZFContext.rename hZ Fin.castSucc
  have hw1 := Derives.rename Fin.castSucc hw
  have he1 := Derives.rename Fin.castSucc he
  have hZ2 := ZFContext.rename hZ1 Fin.castSucc
  have hw2 := Derives.rename Fin.castSucc hw1
  have he2 := Derives.rename Fin.castSucc he1
  have hZ3 := ZFContext.rename hZ2 Fin.castSucc
  have hw3 := Derives.rename Fin.castSucc hw2
  have he3 := Derives.rename Fin.castSucc he2
  have hZ4 := ZFContext.rename hZ3 Fin.castSucc
  have hw4 := Derives.rename Fin.castSucc hw3
  have he4 := Derives.rename Fin.castSucc he3
  have hZ5 := ZFContext.rename hZ4 Fin.castSucc
  have hw5 := Derives.rename Fin.castSucc hw4
  have he5 := Derives.rename Fin.castSucc he4
  exact conj_congr (iff_refl (SyntaxAtomSyntax.zeroScalar w.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc.castSucc)) (conj_congr (iff_refl (SyntaxAtomSyntax.memberCode w.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc.castSucc)) (conj_congr (iff_refl (SyntaxAtomSyntax.memberCode w.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc (Fin.last (m+4)) q.castSucc.castSucc.castSucc.castSucc.castSucc)) (conj_congr (IndexTermRenameTransport.program_iff hZ5 w.castSucc.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc.castSucc.castSucc g.castSucc.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc.castSucc R.castSucc.castSucc.castSucc.castSucc.castSucc S.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc (of_eq (by simp only [omega_rename]) hw5) (of_eq (by simp only [realization_rename]) he5)) (IndexTermRenameTransport.program_iff hZ5 w.castSucc.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc.castSucc.castSucc g.castSucc.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc.castSucc R.castSucc.castSucc.castSucc.castSucc.castSucc S.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc (Fin.last (m+4)) (of_eq (by simp only [omega_rename]) hw5) (of_eq (by simp only [realization_rename]) he5)))))

theorem equality_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s f g a b c d R S n q : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (realization w r s f g a b c d R S)) :
    Derives Γ ((FormulaTransformAtomSyntax.equality w R S a b c d n q).iff (SyntaxRenameAtomSyntax.equality w r s a b c d n q)) := by
  apply ex_congr
  apply ex_congr
  apply ex_congr
  apply ex_congr
  have hZ1 := ZFContext.rename hZ Fin.castSucc
  have hw1 := Derives.rename Fin.castSucc hw
  have he1 := Derives.rename Fin.castSucc he
  have hZ2 := ZFContext.rename hZ1 Fin.castSucc
  have hw2 := Derives.rename Fin.castSucc hw1
  have he2 := Derives.rename Fin.castSucc he1
  have hZ3 := ZFContext.rename hZ2 Fin.castSucc
  have hw3 := Derives.rename Fin.castSucc hw2
  have he3 := Derives.rename Fin.castSucc he2
  have hZ4 := ZFContext.rename hZ3 Fin.castSucc
  have hw4 := Derives.rename Fin.castSucc hw3
  have he4 := Derives.rename Fin.castSucc he3
  exact conj_congr (iff_refl (SyntaxAtomSyntax.equalCode w.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc)) (conj_congr (iff_refl (SyntaxAtomSyntax.equalCode w.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+3)) q.castSucc.castSucc.castSucc.castSucc)) (conj_congr (IndexTermRenameTransport.program_iff hZ4 w.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc.castSucc g.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc R.castSucc.castSucc.castSucc.castSucc S.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc (of_eq (by simp only [omega_rename]) hw4) (of_eq (by simp only [realization_rename]) he4)) (IndexTermRenameTransport.program_iff hZ4 w.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc.castSucc g.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc R.castSucc.castSucc.castSucc.castSucc S.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc (Fin.last (m+3)) (of_eq (by simp only [omega_rename]) hw4) (of_eq (by simp only [realization_rename]) he4))))

end PPAC.Migration.Internal.IndexTermAtomTransport
