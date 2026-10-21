import PPAC.Migration.Internal.StructuralTreeGraphValues

/-! 真实求值的限制历史本身是完整前段递归图；得到实际二值范围及零根规律。 -/
namespace PPAC.Migration.Internal.StructuralTreeHistory
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax OrdinalSyntax StructuralTreeEvaluationSyntax
open StructuralTreeOperatorSyntax (matrix matrix_operator)
open NaturalAdditionTransport (params3 params3_0 params3_1 params3_2)
open ReplacementPredicates (paramsUp)
attribute [local irreducible] NaturalRecursionSyntax.matrix

def stepHistory {m} (w z e n y : Fin m) : Formula m := .ex
  ((graph w.castSucc z.castSucc e.castSucc (Fin.last m) n.castSucc).conj
    (StructuralTreeOperatorSyntax.step w.castSucc z.castSucc e.castSucc n.castSucc (Fin.last m) y.castSucc))

theorem stepHistory_rename {m k} (w z e n y : Fin m) (s : Fin m → Fin k) : (stepHistory w z e n y).rename s = stepHistory (s w) (s z) (s e) (s n) (s y) := by
  simp only [stepHistory, Formula.rename, graph_rename, StructuralTreeOperatorSyntax.step_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem from_data {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z e s f n y : Fin m)
    (hn : Derives Γ (ordinal n)) (hy : Derives Γ (data w z e s f n y)) : Derives Γ (stepHistory w z e n y) := by
  have hhist := Derives.impE (Derives.impE (OrdinalRecursionSyntax.equations_at matrix (params3 w z e) f s n y
    (.conjR (.conjL (.conjR hy)))) (InsertLogic.new_member s n n (.conjL hy))) (.conjR (.conjR hy))
  let H := (RestrictionSyntax.restrict (Fin.last m) f.castSucc n.castSucc).conj
    (StructuralTreeOperatorSyntax.step w.castSucc z.castSucc e.castSucc n.castSucc (Fin.last m) y.castSucc)
  let Δ := Context.add H (Context.image Formula.raise Γ)
  have hh : Derives Γ (.ex H) := by
    simpa only [OrdinalRecursionSyntax.history, matrix_operator, paramsUp, params3_0, params3_1, params3_2] using hhist
  apply Derives.exE (p := H) hh
  have hZ1 : ZFContext.Evidence Δ := ZFContext.under hZ H
  have hn1 : Derives Δ (ordinal n.castSucc) := by simpa only [Formula.raise, ordinal_rename] using under hn H
  have hy1 : Derives Δ (data w.castSucc z.castSucc e.castSucc s.castSucc f.castSucc n.castSucc y.castSucc) := by
    simpa only [Formula.raise, data_rename] using under hy H
  have hSOrd := OrdinalSuccessor.ordinal s.castSucc n.castSucc (ZFContext.arithmetic hZ1).base.foundation (.conjL hy1) hn1
  have hsub := OrdinalTransitivity.subset_of_member s.castSucc n.castSucc (.conjL hSOrd) (InsertLogic.new_member _ _ _ (.conjL hy1))
  have hH : Derives Δ H := .hyp (Or.inl rfl)
  have hg : Derives Δ (graph w.castSucc z.castSucc e.castSucc (Fin.last m) n.castSucc) :=
    OrdinalRecursionRestriction.recursor_restrict matrix (params3 w.castSucc z.castSucc e.castSucc) (Fin.last m) f.castSucc n.castSucc s.castSucc
      (.conjL hn1) hsub (.conjL hH) (.conjL (.conjR hy1))
  have hout : Derives Δ (stepHistory w.castSucc z.castSucc e.castSucc n.castSucc y.castSucc) := by
    apply Derives.exI (Fin.last m)
    simp only [Formula.instantiate, Formula.rename, graph_rename, StructuralTreeOperatorSyntax.step_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
    exact .conjI hg (.conjR hH)
  simpa only [Formula.raise, stepHistory_rename] using hout

theorem from_value {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z e n y : Fin m)
    (hn : Derives Γ (ordinal n)) (hy : Derives Γ (evaluation w z e n y)) : Derives Γ (stepHistory w z e n y) := by
  let D := witnesses w z e n y
  let Δ := Context.add D (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_value w z e n y _ hy
  have hn2 : Derives Δ (ordinal n.castSucc.castSucc) := by simpa only [Formula.raise, ordinal_rename] using OrderedPairElimination.under_two hn D
  have hD : Derives Δ D := .hyp (Or.inl rfl)
  have hout := from_data (ZFContext.under_two hZ D) _ _ _ _ _ _ _ hn2 hD
  simpa only [Formula.raise, stepHistory_rename] using hout

theorem range {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z e n y : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (he : Derives Γ (successor e z))
    (hn : Derives Γ (ordinal n)) (hy : Derives Γ (evaluation w z e n y)) :
    Derives Γ ((Formula.mem y w).conj ((Formula.equal y z).disj (.equal y e))) := by
  have hh := from_value hZ w z e n y hn hy
  let H := (graph w.castSucc z.castSucc e.castSucc (Fin.last m) n.castSucc).conj
    (StructuralTreeOperatorSyntax.step w.castSucc z.castSucc e.castSucc n.castSucc (Fin.last m) y.castSucc)
  let Δ := Context.add H (Context.image Formula.raise Γ)
  change Derives Γ (.ex H) at hh
  apply Derives.exE (p := H) hh
  have hZ1 : ZFContext.Evidence Δ := ZFContext.under hZ H
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw H
  have hz1 : Derives Δ (empty z.castSucc) := by simpa only [Formula.raise, empty_rename] using under hz H
  have he1 : Derives Δ (successor e.castSucc z.castSucc) := by simpa only [Formula.raise, successor_rename] using under he H
  have hH : Derives Δ H := .hyp (Or.inl rfl)
  exact StructuralTreeOperatorStep.range hZ1 _ _ _ _ _ _ hw1 hz1 he1 (.conjR hH)

theorem unit_distinct {m} {Γ : Context m} (z e : Fin m) (hz : Derives Γ (empty z))
    (he : Derives Γ (successor e z)) : Derives Γ (Formula.equal e z).neg := by
  apply Derives.impI
  have hzE : Derives (Context.add (Formula.equal e z) Γ) (.mem z e) := InsertLogic.new_member e z z (add he (.equal e z))
  have hzZ := UnorderedPairLogic.mem_container_subst e z z (.hyp (Or.inl rfl)) hzE
  exact .impE (empty_at z z (add hz _)) hzZ
end PPAC.Migration.Internal.StructuralTreeHistory
