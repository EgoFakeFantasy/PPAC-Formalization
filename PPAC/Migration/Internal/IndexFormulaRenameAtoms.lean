import PPAC.Migration.Internal.IndexFormulaRenameBinders

/-! 两个原子公式分支在全部内部列表码环境上的实际双向传输。 -/
namespace PPAC.Migration.Internal.IndexFormulaRenameAtoms
open Source SourceAlgebra SourceLogic OmegaSyntax IndexTermRenameTransportSyntax
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem membership_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w I J R S a b c d r s n q : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (IndexTermImageCodeSyntax.environment w I J R S a b c d))
    (hr : Derives Γ (SyntaxMapCodeSyntax.encoded w r a c I)) (hs : Derives Γ (SyntaxMapCodeSyntax.encoded w s b d J)) :
    Derives Γ ((SyntaxRenameAtomSyntax.membership w r s a b c d n q).iff (SyntaxMixedFormulaAtomSyntax.membership w R S a b c d n q)) := by
  let B := realization w.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply SyntaxRenameBinders.eliminate_2 B _ (IndexTermImageEnvironment.realization_exists hZ w I J R S a b c d r s he hr hs)
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ B
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hOld := IndexTermAtomTransport.membership_iff hZ2 w.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc n.castSucc.castSucc q.castSucc.castSucc hw2 hB
  have hNew := FormulaTransformAtomCorrectness.membership_iff hZ2 w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc n.castSucc.castSucc q.castSucc.castSucc hw2
  have ho := SyntaxTypeLocalTransfer.iff_trans (.conjI (.conjR hOld) (.conjL hOld)) hNew
  exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, SyntaxRenameAtomSyntax.membership_rename, SyntaxMixedFormulaAtomSyntax.membership_rename]) ho

theorem equality_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w I J R S a b c d r s n q : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (IndexTermImageCodeSyntax.environment w I J R S a b c d))
    (hr : Derives Γ (SyntaxMapCodeSyntax.encoded w r a c I)) (hs : Derives Γ (SyntaxMapCodeSyntax.encoded w s b d J)) :
    Derives Γ ((SyntaxRenameAtomSyntax.equality w r s a b c d n q).iff (SyntaxMixedFormulaAtomSyntax.equality w R S a b c d n q)) := by
  let B := realization w.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply SyntaxRenameBinders.eliminate_2 B _ (IndexTermImageEnvironment.realization_exists hZ w I J R S a b c d r s he hr hs)
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ B
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hOld := IndexTermAtomTransport.equality_iff hZ2 w.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc n.castSucc.castSucc q.castSucc.castSucc hw2 hB
  have hNew := FormulaTransformAtomCorrectness.equality_iff hZ2 w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc n.castSucc.castSucc q.castSucc.castSucc hw2
  have ho := SyntaxTypeLocalTransfer.iff_trans (.conjI (.conjR hOld) (.conjL hOld)) hNew
  exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, SyntaxRenameAtomSyntax.equality_rename, SyntaxMixedFormulaAtomSyntax.equality_rename]) ho

end PPAC.Migration.Internal.IndexFormulaRenameAtoms
