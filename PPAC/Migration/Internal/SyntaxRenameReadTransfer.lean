import PPAC.Migration.Internal.SyntaxRenameRecursiveSyntax

/-! 用原存在量词同余将所有实际后继和提升码见证的Read替换为RenameFormula。 -/
namespace PPAC.Migration.Internal.SyntaxRenameReadTransfer
open Source SourceAlgebra SourceLogic OrdinalSyntax SyntaxRenameQuerySyntax FormulaCodeCongruence
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem advanced_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h D x r s a b c d q : Fin m)
    (hD : Derives Γ (ordinal D)) (hx : Derives Γ (.mem x D))
    (hg : Derives Γ (SyntaxRenameRecursionSyntax.graph w h D)) :
    Derives Γ ((SyntaxRenameQuerySyntax.advanced w h x r s a b c d q).iff
      (SyntaxRenameRecursiveSyntax.advanced w x r s a b c d q)) := by
  apply ex_congr
  apply ex_congr
  apply ex_congr
  let Δ : Context (m+3) := Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Γ)))
  have hZ3 : ZFContext.Evidence Δ := ZFContext.rename (ZFContext.rename (ZFContext.rename (hZ) Fin.castSucc) Fin.castSucc) Fin.castSucc
  have hD3 : Derives Δ (ordinal D.castSucc.castSucc.castSucc) := of_eq (by simp only [ordinal_rename]) (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (hD))))
  have hx3 : Derives Δ (.mem x.castSucc.castSucc.castSucc D.castSucc.castSucc.castSucc) := Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (hx)))
  have hg3 : Derives Δ (SyntaxRenameRecursionSyntax.graph w.castSucc.castSucc.castSucc h.castSucc.castSucc.castSucc D.castSucc.castSucc.castSucc) := of_eq (by simp only [SyntaxRenameRecursionSyntax.graph_rename]) (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (hg))))
  exact conj_congr (SyntaxTypeLocalTransfer.iff_refl (SyntaxMapLiftSyntax.codedLift w.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2))))
    (SyntaxRenameJudgment.read_iff hZ3 w.castSucc.castSucc.castSucc h.castSucc.castSucc.castSucc D.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc (Fin.last (m+2)) s.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc b.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc d.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc hD3 hx3 hg3)

theorem check_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (advance : Bool) (w h D x r s a b c d q : Fin m)
    (hD : Derives Γ (ordinal D)) (hx : Derives Γ (.mem x D))
    (hg : Derives Γ (SyntaxRenameRecursionSyntax.graph w h D)) :
    Derives Γ ((SyntaxRenameLogicalSyntax.check advance w h x r s a b c d q).iff
      (SyntaxRenameRecursiveSyntax.check advance w x r s a b c d q)) := by
  cases advance with
  | false => exact SyntaxRenameJudgment.read_iff hZ w h D x r s a b c d q hD hx hg
  | true => exact advanced_iff hZ w h D x r s a b c d q hD hx hg
end PPAC.Migration.Internal.SyntaxRenameReadTransfer
