import PPAC.Migration.Internal.SyntaxRenameGraphValues

/-! 真实集合值求值的历史本身是完整前段递归图；当前输出是该历史的实际分离状态。 -/
namespace PPAC.Migration.Internal.SyntaxRenameHistory
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax OrdinalSyntax SyntaxRenameEvaluationSyntax
open SyntaxRenameRecursionSyntax
open SyntaxRenameRecursionSyntax (one one_map)
open SyntaxRenameOperatorSyntax
open ReplacementPredicates (paramsUp)
attribute [local irreducible] NaturalRecursionSyntax.matrix

def stepHistory {m} (w n y : Fin m) : Formula m := .ex
  ((graph w.castSucc (Fin.last m) n.castSucc).conj
    (value w.castSucc n.castSucc (Fin.last m) y.castSucc))

theorem stepHistory_rename {m k} (w n y : Fin m) (s : Fin m → Fin k) : (stepHistory w n y).rename s = stepHistory (s w) (s n) (s y) := by
  simp only [stepHistory, Formula.rename, graph_rename, value_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem from_data {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w s f n y : Fin m)
    (hn : Derives Γ (ordinal n)) (hy : Derives Γ (data w s f n y)) : Derives Γ (stepHistory w n y) := by
  have hhist := Derives.impE (Derives.impE (OrdinalRecursionSyntax.equations_at matrix (one w) f s n y
    (.conjR (.conjL (.conjR hy)))) (InsertLogic.new_member s n n (.conjL hy))) (.conjR (.conjR hy))
  let H := (RestrictionSyntax.restrict (Fin.last m) f.castSucc n.castSucc).conj
    (value w.castSucc n.castSucc (Fin.last m) y.castSucc)
  let Δ := Context.add H (Context.image Formula.raise Γ)
  have h0 : one w 0 = w := rfl
  have hh : Derives Γ (.ex H) := by
    exact SyntaxRenameQuerySyntax.of_eq (by simp only [H, OrdinalRecursionSyntax.history, matrix_operator, paramsUp, h0]) (hhist)
  apply Derives.exE (p := H) hh
  have hZ1 : ZFContext.Evidence Δ := ZFContext.under hZ H
  have hn1 : Derives Δ (ordinal n.castSucc) := by exact SyntaxRenameQuerySyntax.of_eq (by simp only [Formula.raise, ordinal_rename]) (under hn H)
  have hy1 : Derives Δ (data w.castSucc s.castSucc f.castSucc n.castSucc y.castSucc) := by
    exact SyntaxRenameQuerySyntax.of_eq (by simp only [Formula.raise, data_rename]) (under hy H)
  have hSOrd := OrdinalSuccessor.ordinal s.castSucc n.castSucc (ZFContext.arithmetic hZ1).base.foundation (.conjL hy1) hn1
  have hsub := OrdinalTransitivity.subset_of_member s.castSucc n.castSucc (.conjL hSOrd) (InsertLogic.new_member _ _ _ (.conjL hy1))
  have hH : Derives Δ H := .hyp (Or.inl rfl)
  have hg : Derives Δ (graph w.castSucc (Fin.last m) n.castSucc) :=
    OrdinalRecursionRestriction.recursor_restrict matrix (one w.castSucc) (Fin.last m) f.castSucc n.castSucc s.castSucc
      (.conjL hn1) hsub (.conjL hH) (.conjL (.conjR hy1))
  have hout : Derives Δ (stepHistory w.castSucc n.castSucc y.castSucc) := by
    apply Derives.exI (Fin.last m)
    simp only [Formula.instantiate, Formula.rename, graph_rename, value_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
    exact .conjI hg (.conjR hH)
  exact SyntaxRenameQuerySyntax.of_eq (by simp only [Formula.raise, stepHistory_rename]) (hout)

theorem from_value {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n y : Fin m)
    (hn : Derives Γ (ordinal n)) (hy : Derives Γ (evaluation w n y)) : Derives Γ (stepHistory w n y) := by
  let D := witnesses w n y
  let Δ := Context.add D (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_value w n y _ hy
  have hn2 : Derives Δ (ordinal n.castSucc.castSucc) := by exact SyntaxRenameQuerySyntax.of_eq (by simp only [Formula.raise, ordinal_rename]) (OrderedPairElimination.under_two hn D)
  have hD : Derives Δ D := .hyp (Or.inl rfl)
  have hout := from_data (ZFContext.under_two hZ D) _ _ _ _ _ hn2 hD
  exact SyntaxRenameQuerySyntax.of_eq (by simp only [Formula.raise, stepHistory_rename]) (hout)

theorem range_subset {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n y : Fin m)
    (hn : Derives Γ (ordinal n)) (hy : Derives Γ (evaluation w n y)) : Derives Γ (RestrictionSyntax.subset y w) := by
  have hh := from_value hZ w n y hn hy
  let H := (graph w.castSucc (Fin.last m) n.castSucc).conj
    (value w.castSucc n.castSucc (Fin.last m) y.castSucc)
  let Δ := Context.add H (Context.image Formula.raise Γ)
  apply Derives.exE (p := H) hh
  have hH : Derives Δ H := .hyp (Or.inl rfl)
  exact SyntaxRenameQuerySyntax.of_eq (by simp only [Formula.raise, RestrictionSyntax.subset_rename]) (SyntaxRenameOperatorExistence.subset _ _ _ _ (.conjR hH))

theorem range_member {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w u n y : Fin m)
    (hu : Derives Γ (PowerSetSyntax.powerOf u w)) (hn : Derives Γ (ordinal n))
    (hy : Derives Γ (evaluation w n y)) : Derives Γ (.mem y u) :=
  SyntaxContextCarrier.state_member w u y hu (range_subset hZ w n y hn hy)

theorem off_natural {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n y : Fin m)
    (hn : Derives Γ (ordinal n)) (hb : Derives Γ (Formula.mem n w).neg)
    (hy : Derives Γ (evaluation w n y)) : Derives Γ (empty y) := by
  have hh := from_value hZ w n y hn hy
  let H := (graph w.castSucc (Fin.last m) n.castSucc).conj
    (value w.castSucc n.castSucc (Fin.last m) y.castSucc)
  let Δ := Context.add H (Context.image Formula.raise Γ)
  apply Derives.exE (p := H) hh
  have hH : Derives Δ H := .hyp (Or.inl rfl)
  exact SyntaxRenameQuerySyntax.of_eq (by simp only [Formula.raise, empty_rename]) (SyntaxRenameOperatorMembership.off_natural _ _ _ _ (under hb H) (.conjR hH))
end PPAC.Migration.Internal.SyntaxRenameHistory
