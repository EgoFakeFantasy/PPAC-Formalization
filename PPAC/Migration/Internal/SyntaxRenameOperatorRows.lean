import PPAC.Migration.Internal.SyntaxRenameOperatorExistence

/-! 原七字段同码单射将任意实际分离行恢复到给定元数据；全部候选字段内部量化。 -/
namespace PPAC.Migration.Internal.SyntaxRenameOperatorRows
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax SyntaxRenameLocalSyntax SyntaxRenameOperatorSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem at_state {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n h p R S a b c d q : Fin m)
    (hw : Derives Γ (omega w)) (hp : Derives Γ (SyntaxRenameStateSyntax.state w R S a b c d q p))
    (hr : Derives Γ (row w n h p)) : Derives Γ (content w R S a b c d h n q) := by
  let B := rowBody w n h p
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise
    (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ)))))))
  apply eliminate_row w n h p _ hr
  have hZ7 := SyntaxRenameStateSyntax.zf_under_seven hZ B
  have ew : (omega w).raise.raise.raise.raise.raise.raise.raise = omega w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc := by
    simp only [Formula.raise, omega_rename]
  have hw7 := of_eq ew (SyntaxRenameStateSyntax.under_seven hw B)
  have ep : (SyntaxRenameStateSyntax.state w R S a b c d q p).raise.raise.raise.raise.raise.raise.raise = SyntaxRenameStateSyntax.state w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc R.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc S.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc p.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc := by
    simp only [Formula.raise, SyntaxRenameStateSyntax.state_rename]
  have hp7 := of_eq ep (SyntaxRenameStateSyntax.under_seven hp B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have he := SyntaxRenameState.same_fields hZ7 w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc p.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc.castSucc.castSucc (Fin.last (m+4)).castSucc.castSucc (Fin.last (m+5)).castSucc (Fin.last (m+6)) R.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc S.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc hw7 (.conjL (.conjL hB)) (.conjL hp7)
  have ho := content_subst w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc.castSucc.castSucc (Fin.last (m+4)).castSucc.castSucc (Fin.last (m+5)).castSucc h.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+6)) R.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc S.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc he (.conjR hB)
  have e : (content w R S a b c d h n q).raise.raise.raise.raise.raise.raise.raise = content w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc R.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc S.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc h.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc := by
    simp only [Formula.raise, content_rename]
  exact of_eq e.symm ho

theorem state_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n h p R S a b c d q : Fin m)
    (hw : Derives Γ (omega w)) (hp : Derives Γ (SyntaxRenameStateSyntax.state w R S a b c d q p)) :
    Derives Γ ((row w n h p).iff (content w R S a b c d h n q)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact at_state (ZFContext.add hZ _) w n h p R S a b c d q (add hw _) (add hp _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact intro_row w n h p R S a b c d q (add hp _) (.hyp (Or.inl rfl))

theorem recognized {m} {Γ : Context m} (w n h p : Fin m) (hr : Derives Γ (row w n h p)) :
    Derives Γ (SyntaxRenameStateSyntax.recognized w p) := by
  let B := rowBody w n h p
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise
    (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ)))))))
  apply eliminate_row w n h p _ hr
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := SyntaxRenameStateSyntax.intro_recognized w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc p.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc.castSucc.castSucc (Fin.last (m+4)).castSucc.castSucc (Fin.last (m+5)).castSucc (Fin.last (m+6)) (.conjL hB)
  have e : (SyntaxRenameStateSyntax.recognized w p).raise.raise.raise.raise.raise.raise.raise = SyntaxRenameStateSyntax.recognized w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc p.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc := by
    simp only [Formula.raise, SyntaxRenameStateSyntax.recognized_rename]
  exact of_eq e.symm ho

theorem source_natural {m} {Γ : Context m} (w n h p : Fin m) (hr : Derives Γ (row w n h p)) : Derives Γ (.mem n w) := by
  let B := rowBody w n h p
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise
    (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ)))))))
  apply eliminate_row w n h p _ hr
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  exact .conjL (FormulaCodeProperties.guards w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc.castSucc.castSucc (.conjL (.conjR hB)))

theorem natural {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n h p : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (row w n h p)) : Derives Γ (.mem p w) :=
  SyntaxRenameStateDecode.recognized_natural hZ w p hw (recognized w n h p hr)
end PPAC.Migration.Internal.SyntaxRenameOperatorRows
