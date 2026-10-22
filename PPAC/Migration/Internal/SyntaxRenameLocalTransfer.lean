import PPAC.Migration.Internal.SyntaxRenameCaseTransfer

/-! 全11类与两个实际解码图的局部矩阵双向消去历史参数。 -/
namespace PPAC.Migration.Internal.SyntaxRenameLocalTransfer
open Source SourceAlgebra SourceLogic OrdinalSyntax SyntaxRenameQuerySyntax FormulaCodeCongruence SyntaxTypeLocalTransfer
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem all_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S r s a b c d h n q : Fin m)
    (hn : Derives Γ (ordinal n)) (hg : Derives Γ (SyntaxRenameRecursionSyntax.graph w h n)) :
    Derives Γ ((SyntaxRenameLocalSyntax.cases w R S r s a b c d h n q).iff
      (SyntaxRenameRecursiveSyntax.cases w R S r s a b c d n q)) := by
  exact (disj_congr (iff_refl ((SyntaxRenameAtomSyntax.nullary false w a b c d n q).disj (SyntaxRenameAtomSyntax.nullary true w a b c d n q))) (disj_congr (iff_refl (SyntaxRenameAtomSyntax.membership w r s a b c d n q)) (disj_congr (iff_refl (SyntaxRenameAtomSyntax.equality w r s a b c d n q)) (disj_congr (SyntaxRenameCaseTransfer.single_iff hZ 4 false w h R S a b c d n q hn hg) (disj_congr (SyntaxRenameCaseTransfer.binary_iff hZ 0 w h R S a b c d n q hn hg) (disj_congr (SyntaxRenameCaseTransfer.binary_iff hZ 1 w h R S a b c d n q hn hg) (disj_congr (SyntaxRenameCaseTransfer.binary_iff hZ 2 w h R S a b c d n q hn hg) (disj_congr (SyntaxRenameCaseTransfer.binary_iff hZ 3 w h R S a b c d n q hn hg) (disj_congr (SyntaxRenameCaseTransfer.single_iff hZ 9 true w h R S a b c d n q hn hg) (SyntaxRenameCaseTransfer.single_iff hZ 10 true w h R S a b c d n q hn hg))))))))))

theorem local_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S a b c d h n q : Fin m)
    (hn : Derives Γ (ordinal n)) (hg : Derives Γ (SyntaxRenameRecursionSyntax.graph w h n)) :
    Derives Γ ((SyntaxRenameLocalSyntax.localRename w R S a b c d h n q).iff
      (SyntaxRenameRecursiveSyntax.localRename w R S a b c d n q)) := by
  apply ex_congr
  apply ex_congr
  let Δ : Context (m+2) := Context.image Formula.raise (Context.image Formula.raise (Γ))
  have hZ2 : ZFContext.Evidence Δ := ZFContext.rename (ZFContext.rename (hZ) Fin.castSucc) Fin.castSucc
  have hn2 : Derives Δ (ordinal n.castSucc.castSucc) := of_eq (by simp only [ordinal_rename]) (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (hn)))
  have hg2 : Derives Δ (SyntaxRenameRecursionSyntax.graph w.castSucc.castSucc h.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [SyntaxRenameRecursionSyntax.graph_rename]) (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (hg)))
  exact conj_congr (iff_refl (SyntaxMapCodeSyntax.encoded w.castSucc.castSucc (Fin.last m).castSucc a.castSucc.castSucc c.castSucc.castSucc R.castSucc.castSucc))
    (conj_congr (iff_refl (SyntaxMapCodeSyntax.encoded w.castSucc.castSucc (Fin.last (m+1)) b.castSucc.castSucc d.castSucc.castSucc S.castSucc.castSucc))
      (all_iff hZ2 w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc h.castSucc.castSucc n.castSucc.castSucc q.castSucc.castSucc hn2 hg2))

theorem content_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S a b c d h n q : Fin m)
    (hn : Derives Γ (ordinal n)) (hg : Derives Γ (SyntaxRenameRecursionSyntax.graph w h n)) :
    Derives Γ ((SyntaxRenameLocalSyntax.content w R S a b c d h n q).iff
      (SyntaxRenameRecursiveSyntax.content w R S a b c d n q)) :=
  conj_congr (iff_refl (FormulaCodeSyntax.formulaCode w n a b)) (local_iff hZ w R S a b c d h n q hn hg)
end PPAC.Migration.Internal.SyntaxRenameLocalTransfer
