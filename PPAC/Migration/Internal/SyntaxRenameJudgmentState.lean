import PPAC.Migration.Internal.SyntaxRenameJudgmentSyntax

/-! 实际状态集合成员与同一元数据的完整局部判据精确对应；不假定唯一公式输出。 -/
namespace PPAC.Migration.Internal.SyntaxRenameJudgmentState
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax SyntaxRenameLocalSyntax SyntaxRenameOperatorSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem contains_natural {m} {Γ : Context m} (w n h v r s a b c d q : Fin m)
    (hv : Derives Γ (value w n h v)) (hc : Derives Γ (contains w v r s a b c d q)) : Derives Γ (.mem n w) := by
  let B := (Formula.mem (Fin.last m) v.castSucc).conj
    (SyntaxRenameStateSyntax.state w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc q.castSucc (Fin.last m))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hc
  have hv1 := of_eq (value_rename w n h v Fin.castSucc) (under hv B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  exact SyntaxRenameOperatorMembership.source_natural _ _ _ _ _ hv1 (.conjL hB)

theorem contains_content {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n h v r s a b c d q : Fin m)
    (hw : Derives Γ (omega w)) (hv : Derives Γ (value w n h v)) (hc : Derives Γ (contains w v r s a b c d q)) :
    Derives Γ (content w r s a b c d h n q) := by
  let B := (Formula.mem (Fin.last m) v.castSucc).conj
    (SyntaxRenameStateSyntax.state w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc q.castSucc (Fin.last m))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hc
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hv1 := of_eq (value_rename w n h v Fin.castSucc) (under hv B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hi := SyntaxRenameOperatorMembership.at_state (ZFContext.under hZ B) w.castSucc n.castSucc h.castSucc v.castSucc
    (Fin.last m) r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc q.castSucc hw1 hv1 (.conjR hB)
  exact of_eq (content_rename w r s a b c d h n q Fin.castSucc).symm (.impE (.conjL hi) (.conjL hB))

theorem content_contains {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n h v r s a b c d q : Fin m)
    (hw : Derives Γ (omega w)) (hv : Derives Γ (value w n h v))
    (hl : Derives Γ (SyntaxRenameStateSyntax.legal w r s a b c d q)) (hc : Derives Γ (content w r s a b c d h n q)) :
    Derives Γ (contains w v r s a b c d q) := by
  have he := SyntaxRenameStateExistence.actual_exists hZ w r s a b c d q hw hl
  let B := (Formula.mem (Fin.last m) w.castSucc).conj
    (SyntaxRenameStateSyntax.state w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc q.castSucc (Fin.last m))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) he
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hv1 := of_eq (value_rename w n h v Fin.castSucc) (under hv B)
  have hc1 := of_eq (content_rename w r s a b c d h n q Fin.castSucc) (under hc B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hi := SyntaxRenameOperatorMembership.at_state (ZFContext.under hZ B) w.castSucc n.castSucc h.castSucc v.castSucc
    (Fin.last m) r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc q.castSucc hw1 hv1 (.conjR hB)
  have ho := intro_contains w.castSucc v.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc q.castSucc
    (Fin.last m) (.impE (.conjR hi) hc1) (.conjR hB)
  exact of_eq (contains_rename w v r s a b c d q Fin.castSucc).symm ho

theorem contains_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n h v r s a b c d q : Fin m)
    (hw : Derives Γ (omega w)) (hv : Derives Γ (value w n h v)) :
    Derives Γ ((contains w v r s a b c d q).iff
      ((SyntaxRenameStateSyntax.legal w r s a b c d q).conj (content w r s a b c d h n q))) := by
  apply Derives.conjI
  · apply Derives.impI
    have hc : Derives (Context.add (contains w v r s a b c d q) Γ) (contains w v r s a b c d q) := .hyp (Or.inl rfl)
    exact .conjI (SyntaxRenameQuery.contains_legal _ _ _ _ _ _ _ _ _ hc)
      (contains_content (ZFContext.add hZ _) w n h v r s a b c d q (add hw _) (add hv _) hc)
  · apply Derives.impI
    have hc : Derives (Context.add ((SyntaxRenameStateSyntax.legal w r s a b c d q).conj (content w r s a b c d h n q)) Γ)
      ((SyntaxRenameStateSyntax.legal w r s a b c d q).conj (content w r s a b c d h n q)) := .hyp (Or.inl rfl)
    exact content_contains (ZFContext.add hZ _) w n h v r s a b c d q (add hw _) (add hv _) (.conjL hc) (.conjR hc)

theorem evaluation_contains_natural {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n v r s a b c d q : Fin m)
    (hn : Derives Γ (OrdinalSyntax.ordinal n)) (hv : Derives Γ (SyntaxRenameEvaluationSyntax.evaluation w n v))
    (hc : Derives Γ (contains w v r s a b c d q)) : Derives Γ (.mem n w) := by
  have hh := SyntaxRenameHistory.from_value hZ w n v hn hv
  let B := (SyntaxRenameRecursionSyntax.graph w.castSucc (Fin.last m) n.castSucc).conj
    (value w.castSucc n.castSucc (Fin.last m) v.castSucc)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hh
  have hc1 := of_eq (contains_rename w v r s a b c d q Fin.castSucc) (under hc B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  exact contains_natural _ _ _ _ _ _ _ _ _ _ _ (.conjR hB) hc1
end PPAC.Migration.Internal.SyntaxRenameJudgmentState
