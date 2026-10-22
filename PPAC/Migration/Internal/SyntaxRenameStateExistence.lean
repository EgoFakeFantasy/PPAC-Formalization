import PPAC.Migration.Internal.SyntaxRenameStateDecode

/-! 合法元数据实际取得自然状态见证；供联合构造使用的最小存在接口。 -/
namespace PPAC.Migration.Internal.SyntaxRenameStateExistence
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxForestSyntax SyntaxRenameStateSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem actual_exists {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s a b c d q : Fin m)
    (hw : Derives Γ (omega w)) (hl : Derives Γ (legal w r s a b c d q)) :
    Derives Γ (existsState w r s a b c d q) := by
  have he := SyntaxForests.exists_forest hZ 7 w (seven r s a b c d q) hw (SyntaxRenameState.legal_inputs w r s a b c d q hl)
  let H := (Formula.mem (Fin.last m) w.castSucc).conj
    (cell w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc q.castSucc (Fin.last m))
  let Δ := Context.add H (Context.image Formula.raise Γ)
  change Derives Γ (.ex H) at he
  apply Derives.exE he
  have hl1 : Derives Δ (legal w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc q.castSucc) := by
    simpa only [Formula.raise, legal_rename] using under hl H
  have hH : Derives Δ H := .hyp (Or.inl rfl)
  have ho : Derives Δ (existsState w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc q.castSucc) := by
    apply Derives.exI (Fin.last m)
    simp only [Formula.instantiate, Formula.rename, state_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
    exact .conjI (.conjL hH) (.conjI (.conjR hH) hl1)
  simpa only [Formula.raise, existsState_rename] using ho
end PPAC.Migration.Internal.SyntaxRenameStateExistence
