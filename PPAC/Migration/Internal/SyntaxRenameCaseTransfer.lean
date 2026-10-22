import PPAC.Migration.Internal.SyntaxRenameFieldsTransfer

/-! 原存在量词同余保留全部实际字段见证，得到七种逻辑/量词分支的不带历史双条件。 -/
namespace PPAC.Migration.Internal.SyntaxRenameCaseTransfer
open Source SourceAlgebra SourceLogic OrdinalSyntax SyntaxRenameQuerySyntax FormulaCodeCongruence
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem single_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (advance : Bool)
    (w h r s a b c d n q : Fin m) (hn : Derives Γ (ordinal n))
    (hg : Derives Γ (SyntaxRenameRecursionSyntax.graph w h n)) :
    Derives Γ ((SyntaxRenameLogicalSyntax.single tag advance w h r s a b c d n q).iff
      (SyntaxRenameRecursiveSyntax.single tag advance w r s a b c d n q)) := by
  apply ex_congr
  apply ex_congr
  let Δ : Context (m+2) := Context.image Formula.raise (Context.image Formula.raise (Γ))
  have hZ2 : ZFContext.Evidence Δ := ZFContext.rename (ZFContext.rename (hZ) Fin.castSucc) Fin.castSucc
  have hn2 : Derives Δ (ordinal n.castSucc.castSucc) := of_eq (by simp only [ordinal_rename]) (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (hn)))
  have hg2 : Derives Δ (SyntaxRenameRecursionSyntax.graph w.castSucc.castSucc h.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [SyntaxRenameRecursionSyntax.graph_rename]) (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (hg)))
  exact SyntaxRenameFieldsTransfer.single_iff hZ2 tag advance w.castSucc.castSucc h.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc n.castSucc.castSucc q.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hn2 hg2

theorem binary_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4)
    (w h r s a b c d n q : Fin m) (hn : Derives Γ (ordinal n))
    (hg : Derives Γ (SyntaxRenameRecursionSyntax.graph w h n)) :
    Derives Γ ((SyntaxRenameLogicalSyntax.binary kind w h r s a b c d n q).iff
      (SyntaxRenameRecursiveSyntax.binary kind w r s a b c d n q)) := by
  apply ex_congr
  apply ex_congr
  apply ex_congr
  apply ex_congr
  let Δ : Context (m+4) := Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Γ))))
  have hZ4 : ZFContext.Evidence Δ := ZFContext.rename (ZFContext.rename (ZFContext.rename (ZFContext.rename (hZ) Fin.castSucc) Fin.castSucc) Fin.castSucc) Fin.castSucc
  have hn4 : Derives Δ (ordinal n.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [ordinal_rename]) (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (hn)))))
  have hg4 : Derives Δ (SyntaxRenameRecursionSyntax.graph w.castSucc.castSucc.castSucc.castSucc h.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [SyntaxRenameRecursionSyntax.graph_rename]) (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (hg)))))
  exact SyntaxRenameFieldsTransfer.binary_iff hZ4 kind w.castSucc.castSucc.castSucc.castSucc h.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+3)) hn4 hg4

end PPAC.Migration.Internal.SyntaxRenameCaseTransfer
