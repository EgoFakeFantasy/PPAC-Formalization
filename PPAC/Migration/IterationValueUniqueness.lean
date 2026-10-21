import PPAC.Migration.IterationValueExistence

/-! 末值的对象唯一性来自实际轨迹唯一性与完整函数图单值性。 -/
namespace PPAC.Migration.IterationValueUniqueness
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax IterationSyntax IterationValueSyntax

theorem edge_subst_graph {m} {Γ : Context m} (f g n r : Fin m)
    (he : Derives Γ (.equal f g)) (hr : Derives Γ (edge f n r)) : Derives Γ (edge g n r) := by
  have hi : Derives Γ ((edge (Fin.last m) n.castSucc r.castSucc).instantiate f) := by
    simpa only [Formula.instantiate, edge_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hr
  have h := Derives.eqSubst (edge (Fin.last m) n.castSucc r.castSucc) he hi
  simpa only [Formula.instantiate, edge_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using h

theorem unique_at {m} {Γ : Context m} (hA : IterationContext.Evidence Γ) (n z a w r t : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hn : Derives Γ (.mem n w))
    (hr : Derives Γ (value n z a r)) (ht : Derives Γ (value n z a t)) : Derives Γ (.equal r t) := by
  let P := witnesses n z a r
  let Γp := Context.add P (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_value n z a r _ hr
  have hAP := IterationContext.under_two hA P
  have hwP : Derives Γp (omega w.castSucc.castSucc) := by
    simpa only [Formula.raise, omega_rename] using OrderedPairElimination.under_two hw P
  have hzP : Derives Γp (empty z.castSucc.castSucc) := by
    simpa only [Formula.raise, empty_rename] using OrderedPairElimination.under_two hz P
  have hnP : Derives Γp (.mem n.castSucc.castSucc w.castSucc.castSucc) := OrderedPairElimination.under_two hn P
  have htP : Derives Γp (value n.castSucc.castSucc z.castSucc.castSucc a.castSucc.castSucc t.castSucc.castSucc) := by
    simpa only [Formula.raise, value_rename] using OrderedPairElimination.under_two ht P
  let Q := witnesses n.castSucc.castSucc z.castSucc.castSucc a.castSucc.castSucc t.castSucc.castSucc
  let Γq := Context.add Q (Context.image Formula.raise (Context.image Formula.raise Γp))
  apply eliminate_value n.castSucc.castSucc z.castSucc.castSucc a.castSucc.castSucc t.castSucc.castSucc _ htP
  have hAQ := IterationContext.under_two hAP Q
  have hwQ : Derives Γq (omega w.castSucc.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, omega_rename] using OrderedPairElimination.under_two hwP Q
  have hzQ : Derives Γq (empty z.castSucc.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, empty_rename] using OrderedPairElimination.under_two hzP Q
  have hnQ : Derives Γq (.mem n.castSucc.castSucc.castSucc.castSucc w.castSucc.castSucc.castSucc.castSucc) :=
    OrderedPairElimination.under_two hnP Q
  have hP : Derives Γp P := .hyp (Or.inl rfl)
  have hPQ : Derives Γq ((FiniteIterationSyntax.witness (Fin.last (m+1)).castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc
      n.castSucc.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc).conj
        (edge (Fin.last (m+1)).castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc)) := by
    simpa only [Formula.raise, P, witnesses, Formula.rename, FiniteIterationSyntax.witness_rename, edge_rename]
      using OrderedPairElimination.under_two hP Q
  have hQ : Derives Γq Q := .hyp (Or.inl rfl)
  have heq := IterationContext.unique hAQ (Fin.last (m+1)).castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc
    (Fin.last (m+3)) (Fin.last (m+2)).castSucc n.castSucc.castSucc.castSucc.castSucc
    z.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc w.castSucc.castSucc.castSucc.castSucc
    hwQ hzQ hnQ (.conjL hPQ) (.conjL hQ)
  have htf := edge_subst_graph (Fin.last (m+3)) (Fin.last (m+1)).castSucc.castSucc
    n.castSucc.castSucc.castSucc.castSucc t.castSucc.castSucc.castSucc.castSucc (eq_symm (.conjR heq)) (.conjR hQ)
  have hres := GraphProperties.single_valued (Fin.last (m+1)).castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc
    n.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc t.castSucc.castSucc.castSucc.castSucc
    hAQ.extensionality (.conjL (.conjR (.conjL hPQ))) (.conjR hPQ) htf
  simpa only [Formula.raise, Formula.rename] using hres

theorem unique_formula {m} {Γ : Context m} (hA : IterationContext.Evidence Γ) (n z a w r : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hn : Derives Γ (.mem n w))
    (hr : Derives Γ (value n z a r)) : Derives Γ (uniqueValue n z a r) := by
  apply Derives.allI
  have hA' := IterationContext.rename hA Fin.castSucc
  have hw' : Derives (Context.image Formula.raise Γ) (omega w.castSucc) := by
    simpa only [Formula.raise, omega_rename] using Derives.rename Fin.castSucc hw
  have hz' : Derives (Context.image Formula.raise Γ) (empty z.castSucc) := by
    simpa only [Formula.raise, empty_rename] using Derives.rename Fin.castSucc hz
  have hn' := Derives.rename Fin.castSucc hn
  have hr' : Derives (Context.image Formula.raise Γ) (value n.castSucc z.castSucc a.castSucc r.castSucc) := by
    simpa only [Formula.raise, value_rename] using Derives.rename Fin.castSucc hr
  apply Derives.impI
  exact unique_at (IterationContext.add hA' _) n.castSucc z.castSucc a.castSucc w.castSucc (Fin.last m) r.castSucc
    (add hw' _) (add hz' _) (add hn' _) (.hyp (Or.inl rfl)) (add hr' _)
end PPAC.Migration.IterationValueUniqueness
