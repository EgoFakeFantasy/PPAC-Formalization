import PPAC.Migration.Internal.ProjectCompilerGraphValues

/-! Actual compiler set recursion or guarded output relation; output correctness and functionality remain unproved. -/
namespace PPAC.Migration.Internal.ProjectCompilerHistory
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax OrdinalSyntax ProjectCompilerEvaluationSyntax
open ProjectCompilerRecursionSyntax
open SyntaxAtomSyntax (two two_map)
open ProjectCompilerStateSyntax
open ReplacementPredicates (paramsUp)
attribute [local irreducible] NaturalRecursionSyntax.matrix

def stepHistory {m} (w c n y : Fin m) : Formula m := .ex
  ((graph w.castSucc c.castSucc (Fin.last m) n.castSucc).conj
    (state w.castSucc c.castSucc n.castSucc (Fin.last m) y.castSucc))

theorem stepHistory_rename {m k} (w c n y : Fin m) (s : Fin m → Fin k) : (stepHistory w c n y).rename s = stepHistory (s w) (s c) (s n) (s y) := by
  simp only [stepHistory, Formula.rename, graph_rename, state_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem from_data {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w c s f n y : Fin m)
    (hn : Derives Γ (ordinal n)) (hy : Derives Γ (data w c s f n y)) : Derives Γ (stepHistory w c n y) := by
  have hhist := Derives.impE (Derives.impE (OrdinalRecursionSyntax.equations_at matrix (two w c) f s n y
    (.conjR (.conjL (.conjR hy)))) (InsertLogic.new_member s n n (.conjL hy))) (.conjR (.conjR hy))
  let H := (RestrictionSyntax.restrict (Fin.last m) f.castSucc n.castSucc).conj
    (state w.castSucc c.castSucc n.castSucc (Fin.last m) y.castSucc)
  let Δ := Context.add H (Context.image Formula.raise Γ)
  have h0 : two w c 0 = w := rfl
  have h1 : two w c 1 = c := rfl
  have hh : Derives Γ (.ex H) := by
    simpa only [H, OrdinalRecursionSyntax.history, matrix_operator, paramsUp, h0, h1] using hhist
  apply Derives.exE (p := H) hh
  have hZ1 : ZFContext.Evidence Δ := ZFContext.under hZ H
  have hn1 : Derives Δ (ordinal n.castSucc) := by simpa only [Formula.raise, ordinal_rename] using under hn H
  have hy1 : Derives Δ (data w.castSucc c.castSucc s.castSucc f.castSucc n.castSucc y.castSucc) := by
    simpa only [Formula.raise, data_rename] using under hy H
  have hSOrd := OrdinalSuccessor.ordinal s.castSucc n.castSucc (ZFContext.arithmetic hZ1).base.foundation (.conjL hy1) hn1
  have hsub := OrdinalTransitivity.subset_of_member s.castSucc n.castSucc (.conjL hSOrd) (InsertLogic.new_member _ _ _ (.conjL hy1))
  have hH : Derives Δ H := .hyp (Or.inl rfl)
  have hg : Derives Δ (graph w.castSucc c.castSucc (Fin.last m) n.castSucc) :=
    OrdinalRecursionRestriction.recursor_restrict matrix (two w.castSucc c.castSucc) (Fin.last m) f.castSucc n.castSucc s.castSucc
      (.conjL hn1) hsub (.conjL hH) (.conjL (.conjR hy1))
  have hout : Derives Δ (stepHistory w.castSucc c.castSucc n.castSucc y.castSucc) := by
    apply Derives.exI (Fin.last m)
    simp only [Formula.instantiate, Formula.rename, graph_rename, state_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
    exact .conjI hg (.conjR hH)
  simpa only [Formula.raise, stepHistory_rename] using hout

theorem from_value {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w c n y : Fin m)
    (hn : Derives Γ (ordinal n)) (hy : Derives Γ (evaluation w c n y)) : Derives Γ (stepHistory w c n y) := by
  let D := witnesses w c n y
  let Δ := Context.add D (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_value w c n y _ hy
  have hn2 : Derives Δ (ordinal n.castSucc.castSucc) := by simpa only [Formula.raise, ordinal_rename] using OrderedPairElimination.under_two hn D
  have hD : Derives Δ D := .hyp (Or.inl rfl)
  have hout := from_data (ZFContext.under_two hZ D) _ _ _ _ _ _ hn2 hD
  simpa only [Formula.raise, stepHistory_rename] using hout

theorem range_subset {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w c n y : Fin m)
    (hn : Derives Γ (ordinal n)) (hy : Derives Γ (evaluation w c n y)) : Derives Γ (RestrictionSyntax.subset y c) := by
  have hh := from_value hZ w c n y hn hy
  let H := (graph w.castSucc c.castSucc (Fin.last m) n.castSucc).conj
    (state w.castSucc c.castSucc n.castSucc (Fin.last m) y.castSucc)
  let Δ := Context.add H (Context.image Formula.raise Γ)
  apply Derives.exE (p := H) hh
  have hH : Derives Δ H := .hyp (Or.inl rfl)
  simpa only [Formula.raise, RestrictionSyntax.subset_rename] using ProjectCompilerStateExistence.subset _ _ _ _ _ (.conjR hH)

theorem range_member {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w c u n y : Fin m)
    (hu : Derives Γ (PowerSetSyntax.powerOf u c)) (hn : Derives Γ (ordinal n))
    (hy : Derives Γ (evaluation w c n y)) : Derives Γ (.mem y u) :=
  SyntaxContextCarrier.state_member c u y hu (range_subset hZ w c n y hn hy)

theorem off_natural {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w c n y : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (ordinal n)) (hb : Derives Γ (Formula.mem n w).neg)
    (hy : Derives Γ (evaluation w c n y)) : Derives Γ (empty y) := by
  have hh := from_value hZ w c n y hn hy
  let H := (graph w.castSucc c.castSucc (Fin.last m) n.castSucc).conj
    (state w.castSucc c.castSucc n.castSucc (Fin.last m) y.castSucc)
  let Δ := Context.add H (Context.image Formula.raise Γ)
  apply Derives.exE (p := H) hh
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw H
  have hH : Derives Δ H := .hyp (Or.inl rfl)
  simpa only [Formula.raise, empty_rename] using ProjectCompilerStateMembership.off_natural (ZFContext.under hZ H) _ _ _ _ _ hw1 (under hb H) (.conjR hH)
end PPAC.Migration.Internal.ProjectCompilerHistory
