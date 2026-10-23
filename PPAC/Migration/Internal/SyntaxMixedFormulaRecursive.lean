import PPAC.Migration.Internal.SyntaxMixedFormulaLocalTransfer

/-! 所有内部候选上的完整混合公式递归双条件；不把状态集合唯一性升级为公式输出码唯一性。 -/
namespace PPAC.Migration.Internal.SyntaxMixedFormulaRecursive
open SyntaxRenameQuerySyntax (of_eq)
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxMixedFormulaQuerySyntax SyntaxMixedFormulaJudgmentSyntax SyntaxMixedFormulaRecursiveSyntax SyntaxTypeLocalTransfer FormulaCodeCongruence
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem at_step {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s a b c d h n q v : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w))
    (hv : Derives Γ (SyntaxMixedFormulaEvaluationSyntax.evaluation w n v))
    (hg : Derives Γ (SyntaxMixedFormulaRecursionSyntax.graph w h n))
    (hs : Derives Γ (SyntaxMixedFormulaOperatorSyntax.value w n h v)) :
    Derives Γ ((substituted w r s a b c d n q).iff (criterion w r s a b c d n q)) := by
  have ho := NaturalOrderBasic.ordinal hZ w n hw hn
  have h1 := SyntaxMixedFormulaJudgment.at_value hZ w r s a b c d n q v ho hv
  have h2 := SyntaxMixedFormulaJudgmentState.contains_iff hZ w n h v r s a b c d q hw hs
  have h3 := SyntaxMixedFormulaLocalTransfer.content_iff hZ w r s a b c d h n q ho hg
  have hh := iff_trans h1 (iff_trans h2 (conj_congr (iff_refl (SyntaxMixedFormulaStateSyntax.legal w r s a b c d q)) h3))
  apply Derives.conjI
  · apply Derives.impI
    exact .conjI (add hn _) (.impE (add (.conjL hh) _) (.hyp (Or.inl rfl)))
  · apply Derives.impI
    exact .impE (add (.conjR hh) _) (.conjR (.hyp (Or.inl rfl)))

theorem at_value {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s a b c d n q v : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w))
    (hv : Derives Γ (SyntaxMixedFormulaEvaluationSyntax.evaluation w n v)) :
    Derives Γ ((substituted w r s a b c d n q).iff (criterion w r s a b c d n q)) := by
  have ho := NaturalOrderBasic.ordinal hZ w n hw hn
  have hh := SyntaxMixedFormulaHistory.from_value hZ w n v ho hv
  let B := (SyntaxMixedFormulaRecursionSyntax.graph w.castSucc (Fin.last m) n.castSucc).conj
    (SyntaxMixedFormulaOperatorSyntax.value w.castSucc n.castSucc (Fin.last m) v.castSucc)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hh
  have hZ1 := ZFContext.under hZ B
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hv1 := of_eq (SyntaxMixedFormulaEvaluationSyntax.evaluation_rename w n v Fin.castSucc) (under hv B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ht := at_step hZ1 w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc
    (Fin.last m) n.castSucc q.castSucc v.castSucc hw1 (under hn B) hv1 (.conjL hB) (.conjR hB)
  exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, substituted_rename, criterion_rename]) ht

theorem recursive_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s a b c d n q : Fin m)
    (hw : Derives Γ (omega w)) :
    Derives Γ ((substituted w r s a b c d n q).iff (criterion w r s a b c d n q)) := by
  apply SourcePropositional.by_cases (Formula.mem n w)
  · let N := Formula.mem n w
    let Ξ := Context.add N Γ
    have hn : Derives Ξ N := .hyp (Or.inl rfl)
    have he := SyntaxMixedFormulaEvaluationExistence.at_natural (ZFContext.add hZ N) w n (add hw N) hn
    let V := SyntaxMixedFormulaEvaluationSyntax.evaluation w.castSucc n.castSucc (Fin.last m)
    let Δ := Context.add V (Context.image Formula.raise Ξ)
    apply Derives.exE (p := V) he
    have hZ1 := ZFContext.under (ZFContext.add hZ N) V
    have hw1 := of_eq (omega_rename w Fin.castSucc) (under (add hw N) V)
    have hV : Derives Δ V := .hyp (Or.inl rfl)
    have ht := at_value hZ1 w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc
      n.castSucc q.castSucc (Fin.last m) hw1 (under hn V) hV
    exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, substituted_rename, criterion_rename]) ht
  · apply Derives.conjI
    · apply Derives.impI
      exact .botE (.impE (.hyp (Or.inr (Or.inl rfl))) (.conjL (.hyp (Or.inl rfl))))
    · apply Derives.impI
      exact .botE (.impE (.hyp (Or.inr (Or.inl rfl))) (.conjL (.hyp (Or.inl rfl))))

theorem source_type {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s a b c d n q : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (substituted w r s a b c d n q)) :
    Derives Γ (FormulaCodeSyntax.formulaCode w n a b) := by
  have hc := Derives.impE (.conjL (recursive_iff hZ w r s a b c d n q hw)) hr
  exact .conjL (.conjR (.conjR hc))
end PPAC.Migration.Internal.SyntaxMixedFormulaRecursive
