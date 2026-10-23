import PPAC.Migration.Internal.SyntaxMixedFormulaRecursiveSyntax

/-! 全部四个量词提升见证下的真实历史读取与对象混合公式子判断精确对应。 -/
namespace PPAC.Migration.Internal.SyntaxMixedFormulaReadTransfer
open Source SourceAlgebra SourceLogic OrdinalSyntax SyntaxMixedFormulaQuerySyntax FormulaCodeCongruence
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem advanced_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h D x r s a b c d q : Fin m)
    (hD : Derives Γ (ordinal D)) (hx : Derives Γ (.mem x D))
    (hg : Derives Γ (SyntaxMixedFormulaRecursionSyntax.graph w h D)) :
    Derives Γ ((SyntaxMixedFormulaQuerySyntax.advanced w h x r s a b c d q).iff
      (SyntaxMixedFormulaRecursiveSyntax.advanced w x r s a b c d q)) := by
  apply ex_congr
  apply ex_congr
  apply ex_congr
  apply ex_congr
  let Δ : Context (m+4) := Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ)))
  have hZ4 : ZFContext.Evidence Δ := ZFContext.rename (ZFContext.rename (ZFContext.rename (ZFContext.rename hZ Fin.castSucc) Fin.castSucc) Fin.castSucc) Fin.castSucc
  have hD4 : Derives Δ (ordinal D.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [ordinal_rename]) (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hD))))
  have hx4 : Derives Δ (.mem x.castSucc.castSucc.castSucc.castSucc D.castSucc.castSucc.castSucc.castSucc) := Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hx)))
  have hg4 : Derives Δ (SyntaxMixedFormulaRecursionSyntax.graph w.castSucc.castSucc.castSucc.castSucc h.castSucc.castSucc.castSucc.castSucc D.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [SyntaxMixedFormulaRecursionSyntax.graph_rename]) (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hg))))
  exact conj_congr (SyntaxTypeLocalTransfer.iff_refl (SyntaxCodedMixedBinderSyntax.lifted w.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc
      (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+3))))
    (SyntaxMixedFormulaJudgment.read_iff hZ4 w.castSucc.castSucc.castSucc.castSucc h.castSucc.castSucc.castSucc.castSucc D.castSucc.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+3))
      (Fin.last m).castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc.castSucc hD4 hx4 hg4)

theorem check_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (advance : Bool) (w h D x r s a b c d q : Fin m)
    (hD : Derives Γ (ordinal D)) (hx : Derives Γ (.mem x D))
    (hg : Derives Γ (SyntaxMixedFormulaRecursionSyntax.graph w h D)) :
    Derives Γ ((SyntaxMixedFormulaLogicalSyntax.check advance w h x r s a b c d q).iff
      (SyntaxMixedFormulaRecursiveSyntax.check advance w x r s a b c d q)) := by
  cases advance with
  | false => exact SyntaxMixedFormulaJudgment.read_iff hZ w h D x r s a b c d q hD hx hg
  | true => exact advanced_iff hZ w h D x r s a b c d q hD hx hg
end PPAC.Migration.Internal.SyntaxMixedFormulaReadTransfer
