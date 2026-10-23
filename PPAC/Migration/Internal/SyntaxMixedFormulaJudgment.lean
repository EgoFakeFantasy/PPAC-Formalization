import PPAC.Migration.Internal.SyntaxMixedFormulaJudgmentState

/-! 原实际集合值上的MixedFormulaSubst判断及完整原前段上的精确查询双条件。 -/
namespace PPAC.Migration.Internal.SyntaxMixedFormulaJudgment
open SyntaxRenameQuerySyntax (of_eq)
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax OrdinalSyntax SyntaxMixedFormulaQuerySyntax SyntaxMixedFormulaEvaluationSyntax SyntaxMixedFormulaJudgmentSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem legal {m} {Γ : Context m} (w r s a b c d n q : Fin m)
    (hr : Derives Γ (substituted w r s a b c d n q)) : Derives Γ (SyntaxMixedFormulaStateSyntax.legal w r s a b c d q) := by
  let B := body w r s a b c d n q
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply eliminate_substituted w r s a b c d n q _ hr
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  exact of_eq (SyntaxMixedFormulaStateSyntax.legal_rename w r s a b c d q Fin.castSucc).symm
    (SyntaxMixedFormulaQuery.contains_legal _ _ _ _ _ _ _ _ _ (.conjR hB))

theorem target_type {m} {Γ : Context m} (w r s a b c d n q : Fin m)
    (hr : Derives Γ (substituted w r s a b c d n q)) : Derives Γ (FormulaCodeSyntax.formulaCode w q c d) :=
  .conjR (legal w r s a b c d n q hr)

theorem at_value {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s a b c d n q v : Fin m)
    (hn : Derives Γ (ordinal n)) (hv : Derives Γ (evaluation w n v)) :
    Derives Γ ((substituted w r s a b c d n q).iff (contains w v r s a b c d q)) := by
  apply Derives.conjI
  · apply Derives.impI
    let T := substituted w r s a b c d n q
    let B := body w r s a b c d n q
    let Δ := Context.add B (Context.image Formula.raise (Context.add T Γ))
    apply eliminate_substituted w r s a b c d n q _ (.hyp (Or.inl rfl))
    have hn1 := of_eq (ordinal_rename n Fin.castSucc) (under (add hn T) B)
    have hv1 := of_eq (evaluation_rename w n v Fin.castSucc) (under (add hv T) B)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have he := SyntaxMixedFormulaEvaluationUnique.unique (ZFContext.under (ZFContext.add hZ T) B) _ _ _ _ hn1 (.conjL hB) hv1
    have ho := contains_subst_set _ _ _ _ _ _ _ _ _ _ he (.conjR hB)
    exact of_eq (contains_rename w v r s a b c d q Fin.castSucc).symm ho
  · apply Derives.impI
    have hc : Derives (Context.add (contains w v r s a b c d q) Γ) (contains w v r s a b c d q) := .hyp (Or.inl rfl)
    have hnw := SyntaxMixedFormulaJudgmentState.evaluation_contains_natural (ZFContext.add hZ _) _ _ _ _ _ _ _ _ _ _ (add hn _) (add hv _) hc
    exact intro_substituted w r s a b c d n q v hnw (add hv _) hc

theorem read_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h D x r s a b c d q : Fin m)
    (hD : Derives Γ (ordinal D)) (hx : Derives Γ (.mem x D)) (hg : Derives Γ (SyntaxMixedFormulaRecursionSyntax.graph w h D)) :
    Derives Γ ((read w h x r s a b c d q).iff (substituted w r s a b c d x q)) := by
  apply Derives.conjI
  · apply Derives.impI
    let T := read w h x r s a b c d q
    let B := (edge h.castSucc x.castSucc (Fin.last m)).conj
      (contains w.castSucc (Fin.last m) r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc q.castSucc)
    let Δ := Context.add B (Context.image Formula.raise (Context.add T Γ))
    apply Derives.exE (p := B) (.hyp (Or.inl rfl))
    have hZ1 := ZFContext.under (ZFContext.add hZ T) B
    have hD1 := of_eq (ordinal_rename D Fin.castSucc) (under (add hD T) B)
    have hg1 := of_eq (SyntaxMixedFormulaRecursionSyntax.graph_rename w h D Fin.castSucc) (under (add hg T) B)
    have hx1 := under (add hx T) B
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hv := SyntaxMixedFormulaGraphValues.value_of_edge hZ1 _ _ _ _ _ hD1 hx1 hg1 (.conjL hB)
    have hn := OrdinalRestriction.member D.castSucc x.castSucc hD1 hx1
    have hnw := SyntaxMixedFormulaJudgmentState.evaluation_contains_natural hZ1 _ _ _ _ _ _ _ _ _ _ hn hv (.conjR hB)
    have ho := intro_substituted _ _ _ _ _ _ _ _ _ (Fin.last m) hnw hv (.conjR hB)
    exact of_eq (substituted_rename w r s a b c d x q Fin.castSucc).symm ho
  · apply Derives.impI
    let T := substituted w r s a b c d x q
    let B := body w r s a b c d x q
    let Δ := Context.add B (Context.image Formula.raise (Context.add T Γ))
    apply eliminate_substituted w r s a b c d x q _ (.hyp (Or.inl rfl))
    have hD1 := of_eq (ordinal_rename D Fin.castSucc) (under (add hD T) B)
    have hg1 := of_eq (SyntaxMixedFormulaRecursionSyntax.graph_rename w h D Fin.castSucc) (under (add hg T) B)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have he := SyntaxMixedFormulaGraphValues.edge_of_value (ZFContext.under (ZFContext.add hZ T) B) _ _ _ _ _ hD1 (under (add hx T) B) hg1 (.conjL hB)
    have ho := intro_read _ _ _ _ _ _ _ _ _ _ (Fin.last m) he (.conjR hB)
    exact of_eq (read_rename w h x r s a b c d q Fin.castSucc).symm ho
end PPAC.Migration.Internal.SyntaxMixedFormulaJudgment
