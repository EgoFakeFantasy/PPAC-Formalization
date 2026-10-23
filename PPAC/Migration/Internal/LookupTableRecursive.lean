import PPAC.Migration.Internal.LookupTableLocalTransfer

/-! 独立按表码递归执行的全内部无历史判据；所有历史/集合值均实际取得。 -/
namespace PPAC.Migration.Internal.LookupTableRecursive
open Source SourceAlgebra SourceLogic OmegaSyntax LookupTableExecutionSyntax LookupTableRecursiveSyntax
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem at_step {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h n i y v : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w))
    (hv : Derives Γ (LookupTableEvaluationSyntax.evaluation w n v))
    (hg : Derives Γ (LookupTableRecursionSyntax.graph w h n))
    (hs : Derives Γ (LookupTableOperatorSyntax.value w n h v)) :
    Derives Γ ((executed w n i y).iff (criterion w n i y)) := by
  have ho := NaturalOrderBasic.ordinal hZ w n hw hn
  have h1 := LookupTableJudgment.at_value hZ w n i y v ho hn hv
  have h2 := LookupTableOperatorMembership.contains_iff hZ w n h v i y hw hs
  have h3 := LookupTableLocalTransfer.run_iff hZ w h n i y hw hn hg
  have hh := SyntaxTypeLocalTransfer.iff_trans h1 (SyntaxTypeLocalTransfer.iff_trans h2
    (FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl (LookupTableProgramSyntax.legal w i y)) h3))
  apply Derives.conjI
  · apply Derives.impI
    exact .conjI (add hn _) (.impE (add (.conjL hh) _) (.hyp (Or.inl rfl)))
  · apply Derives.impI
    exact .impE (add (.conjR hh) _) (.conjR (.hyp (Or.inl rfl)))

theorem at_value {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n i y v : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w))
    (hv : Derives Γ (LookupTableEvaluationSyntax.evaluation w n v)) :
    Derives Γ ((executed w n i y).iff (criterion w n i y)) := by
  have ho := NaturalOrderBasic.ordinal hZ w n hw hn
  have hh := LookupTableHistory.from_value hZ w n v ho hv
  let B := (LookupTableRecursionSyntax.graph w.castSucc (Fin.last m) n.castSucc).conj
    (LookupTableOperatorSyntax.value w.castSucc n.castSucc (Fin.last m) v.castSucc)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hh
  have hZ1 := ZFContext.under hZ B
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hv1 := of_eq (LookupTableEvaluationSyntax.evaluation_rename w n v Fin.castSucc) (under hv B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ht := at_step hZ1 w.castSucc (Fin.last m) n.castSucc i.castSucc y.castSucc v.castSucc hw1 (under hn B) hv1 (.conjL hB) (.conjR hB)
  exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, executed_rename, criterion_rename]) ht

theorem recursive_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n i y : Fin m)
    (hw : Derives Γ (omega w)) :
    Derives Γ ((executed w n i y).iff (criterion w n i y)) := by
  apply SourcePropositional.by_cases (Formula.mem n w)
  · let N := Formula.mem n w
    let Ξ := Context.add N Γ
    have hn : Derives Ξ N := .hyp (Or.inl rfl)
    have he := LookupTableEvaluationExistence.at_natural (ZFContext.add hZ N) w n (add hw N) hn
    let V := LookupTableEvaluationSyntax.evaluation w.castSucc n.castSucc (Fin.last m)
    let Δ := Context.add V (Context.image Formula.raise Ξ)
    apply Derives.exE (p := V) he
    have hZ1 := ZFContext.under (ZFContext.add hZ N) V
    have hw1 := of_eq (omega_rename w Fin.castSucc) (under (add hw N) V)
    have hV : Derives Δ V := .hyp (Or.inl rfl)
    have ht := at_value hZ1 w.castSucc
      n.castSucc i.castSucc y.castSucc (Fin.last m) hw1 (under hn V) hV
    exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, executed_rename, criterion_rename]) ht
  · apply Derives.conjI
    · apply Derives.impI
      exact .botE (.impE (.hyp (Or.inr (Or.inl rfl))) (.conjL (.hyp (Or.inl rfl))))
    · apply Derives.impI
      exact .botE (.impE (.hyp (Or.inr (Or.inl rfl))) (.conjL (.hyp (Or.inl rfl))))

end PPAC.Migration.Internal.LookupTableRecursive
