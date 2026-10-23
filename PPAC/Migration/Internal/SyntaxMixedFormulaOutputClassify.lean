import PPAC.Migration.Internal.SyntaxMixedFormulaOutputInduction

/-! 全候选输入/实际输出存在的双条件及形式否定；完整内部归纳已关闭。 -/
namespace PPAC.Migration.Internal.SyntaxMixedFormulaOutputClassify
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax SyntaxMixedFormulaOutputSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem input_of_exists {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s a b c d n : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (existsOutput w r s a b c d n)) : Derives Γ (input w r s a b c d n) := by
  let Q := SyntaxMixedFormulaJudgmentSyntax.substituted w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m)
  let Δ := Context.add Q (Context.image Formula.raise Γ)
  apply Derives.exE (p := Q) he
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw Q)
  have ho := SyntaxMixedFormulaOutput.input_of_substituted (ZFContext.under hZ Q) w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m) hw1 (.hyp (Or.inl rfl))
  exact of_eq (input_rename w r s a b c d n Fin.castSucc).symm ho

theorem fiber_iff_input {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s a b c d n : Fin m)
    (hw : Derives Γ (omega w)) : Derives Γ ((fiber w r s a b c d n).iff (input w r s a b c d n)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact input_of_exists (ZFContext.add hZ _) w r s a b c d n (add hw _) (SyntaxMixedFormulaOutput.exists_of_fiber _ _ _ _ _ _ _ _ (.hyp (Or.inl rfl)))
  · apply Derives.impI
    exact SyntaxMixedFormulaOutputInduction.actual_fiber (ZFContext.add hZ _) w r s a b c d n (add hw _) (.hyp (Or.inl rfl))

theorem exists_iff_input {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s a b c d n : Fin m)
    (hw : Derives Γ (omega w)) : Derives Γ ((existsOutput w r s a b c d n).iff (input w r s a b c d n)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact input_of_exists (ZFContext.add hZ _) w r s a b c d n (add hw _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact SyntaxMixedFormulaOutputInduction.actual_exists (ZFContext.add hZ _) w r s a b c d n (add hw _) (.hyp (Or.inl rfl))

theorem reject_input {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s a b c d n : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (input w r s a b c d n).neg) : Derives Γ (existsOutput w r s a b c d n).neg := by
  apply Derives.impI
  exact .impE (add hn _) (input_of_exists (ZFContext.add hZ _) w r s a b c d n (add hw _) (.hyp (Or.inl rfl)))

theorem unique_output_of_substituted {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s a b c d n q : Fin m)
    (hw : Derives Γ (omega w)) (hq : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w r s a b c d n q)) :
    Derives Γ (uniqueOutput w r s a b c d n q) := by
  apply Derives.allI
  apply Derives.impI
  let Q := SyntaxMixedFormulaJudgmentSyntax.substituted w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m)
  let Δ := Context.add Q (Context.image Formula.raise Γ)
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw Q)
  have hq1 : Derives Δ (SyntaxMixedFormulaJudgmentSyntax.substituted w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc q.castSucc) := of_eq (SyntaxMixedFormulaJudgmentSyntax.substituted_rename w r s a b c d n q Fin.castSucc) (under hq Q)
  exact SyntaxMixedFormulaOutputInduction.unique (ZFContext.under hZ Q) _ _ _ _ _ _ _ _ (Fin.last m) q.castSucc hw1 (.hyp (Or.inl rfl)) hq1
end PPAC.Migration.Internal.SyntaxMixedFormulaOutputClassify
