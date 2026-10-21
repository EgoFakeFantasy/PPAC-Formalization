import PPAC.Migration.IterationValueCollection

/-! 相邻内部长度的实际末值满足原并集公式；不假定外部长度比较。 -/
namespace PPAC.Migration.IterationValueStep
open Source SourceAlgebra SourceLogic OmegaSyntax OmegaStructureSyntax GraphSyntax InsertSyntax IterationSyntax IterationValueSyntax

theorem compatible_tracks {m} {Γ : Context m} (hA : IterationContext.Evidence Γ) (f d g e n s z a w : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hn : Derives Γ (.mem n w)) (hs : Derives Γ (.mem s w))
    (hf : Derives Γ (FiniteIterationSyntax.witness f d n z a)) (hg : Derives Γ (FiniteIterationSyntax.witness g e s z a)) :
    Derives Γ (GraphFamilySyntax.agrees f g) := by
  have hAll := OmegaStructureInduction.elements_transitive w hA.transitiveSeparation hw
  have htn := OmegaStructureAlgebra.element_transitive_at w n hAll hn
  have hts := OmegaStructureAlgebra.element_transitive_at w s hAll hs
  have htd := OmegaElementary.successor_transitive d n (.conjL hf) htn
  have hte := OmegaElementary.successor_transitive e s (.conjL hg) hts
  have hdw := OmegaStructureAlgebra.successor_member w d n hA.extensionality hw hn (.conjL hf)
  have htw := OmegaStructureInduction.omega_transitive w hA.subsetSeparation hw
  have hdb := Derives.impE (transitive_at w d htw) hdw
  exact IterationCompatibility.compatible f g d e z a w hA.extensionality hA.agreementSeparation hw hz (.conjR hf) (.conjR hg) htd hte hdb

theorem graph_values {m} {Γ : Context m} (hA : IterationContext.Evidence Γ) (f d g e n s z a w r t : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hn : Derives Γ (.mem n w)) (hsn : Derives Γ (successor s n))
    (hf : Derives Γ (FiniteIterationSyntax.witness f d n z a)) (hg : Derives Γ (FiniteIterationSyntax.witness g e s z a))
    (hr : Derives Γ (edge f n r)) (ht : Derives Γ (edge g s t)) : Derives Γ (unionOf t r) := by
  have hsw := OmegaStructureAlgebra.successor_member w s n hA.extensionality hw hn hsn
  have hc := compatible_tracks hA f d g e n s z a w hw hz hn hsw hf hg
  have hne := InsertLogic.old_member e s s n (.conjL hg) (InsertLogic.new_member s n n hsn)
  have he := GraphProperties.output_exists g e n (.conjL (.conjR hg)) hne
  let U := edge g.castSucc n.castSucc (Fin.last m)
  let Γu := Context.add U (Context.image Formula.raise Γ)
  change Derives Γ (.ex U) at he
  apply Derives.exE (p := U) he
  have hcU : Derives Γu (GraphFamilySyntax.agrees f.castSucc g.castSucc) := by
    simpa only [Formula.raise, GraphFamilySyntax.agrees_rename] using under hc U
  have hsU : Derives Γu (successor s.castSucc n.castSucc) := by
    simpa only [Formula.raise, successor_rename] using under hsn U
  have hrU : Derives Γu (edge f.castSucc n.castSucc r.castSucc) := by
    simpa only [Formula.raise, edge_rename] using under hr U
  have htU : Derives Γu (edge g.castSucc s.castSucc t.castSucc) := by
    simpa only [Formula.raise, edge_rename] using under ht U
  have hnextU : Derives Γu (next g.castSucc) := by
    simpa only [Formula.raise, next_rename] using under (.conjR (.conjR (.conjR hg))) U
  have hU : Derives Γu U := .hyp (Or.inl rfl)
  have heq := Derives.impE (Derives.impE (GraphFamilySyntax.agrees_at f.castSucc g.castSucc n.castSucc r.castSucc (Fin.last m) hcU) hrU) hU
  have hgr := GraphPointwiseSyntax.edge_subst_output g.castSucc n.castSucc (Fin.last m) r.castSucc (eq_symm heq) hU
  have hu := Derives.impE (Derives.impE (Derives.impE (next_at g.castSucc n.castSucc s.castSucc r.castSucc t.castSucc hnextU) hsU) hgr) htU
  simpa only [Formula.raise, unionOf_rename] using hu

theorem adjacent_values {m} {Γ : Context m} (hA : IterationContext.Evidence Γ) (n s z a w r t : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hn : Derives Γ (.mem n w)) (hs : Derives Γ (successor s n))
    (hr : Derives Γ (value n z a r)) (ht : Derives Γ (value s z a t)) : Derives Γ (unionOf t r) := by
  let P := witnesses n z a r
  let Γp := Context.add P (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_value n z a r _ hr
  have hAP := IterationContext.under_two hA P
  have hwP : Derives Γp (omega w.castSucc.castSucc) := by
    simpa only [Formula.raise, omega_rename] using OrderedPairElimination.under_two hw P
  have hzP : Derives Γp (empty z.castSucc.castSucc) := by
    simpa only [Formula.raise, empty_rename] using OrderedPairElimination.under_two hz P
  have hnP : Derives Γp (.mem n.castSucc.castSucc w.castSucc.castSucc) := OrderedPairElimination.under_two hn P
  have hsP : Derives Γp (successor s.castSucc.castSucc n.castSucc.castSucc) := by
    simpa only [Formula.raise, successor_rename] using OrderedPairElimination.under_two hs P
  have htP : Derives Γp (value s.castSucc.castSucc z.castSucc.castSucc a.castSucc.castSucc t.castSucc.castSucc) := by
    simpa only [Formula.raise, value_rename] using OrderedPairElimination.under_two ht P
  let Q := witnesses s.castSucc.castSucc z.castSucc.castSucc a.castSucc.castSucc t.castSucc.castSucc
  let Γq := Context.add Q (Context.image Formula.raise (Context.image Formula.raise Γp))
  apply eliminate_value s.castSucc.castSucc z.castSucc.castSucc a.castSucc.castSucc t.castSucc.castSucc _ htP
  have hAQ := IterationContext.under_two hAP Q
  have hwQ : Derives Γq (omega w.castSucc.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, omega_rename] using OrderedPairElimination.under_two hwP Q
  have hzQ : Derives Γq (empty z.castSucc.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, empty_rename] using OrderedPairElimination.under_two hzP Q
  have hnQ : Derives Γq (.mem n.castSucc.castSucc.castSucc.castSucc w.castSucc.castSucc.castSucc.castSucc) := OrderedPairElimination.under_two hnP Q
  have hsQ : Derives Γq (successor s.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, successor_rename] using OrderedPairElimination.under_two hsP Q
  have hP : Derives Γp P := .hyp (Or.inl rfl)
  have hPQ : Derives Γq ((FiniteIterationSyntax.witness (Fin.last (m+1)).castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc
      n.castSucc.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc).conj
        (edge (Fin.last (m+1)).castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc)) := by
    simpa only [Formula.raise, P, witnesses, Formula.rename, FiniteIterationSyntax.witness_rename, edge_rename]
      using OrderedPairElimination.under_two hP Q
  have hQ : Derives Γq Q := .hyp (Or.inl rfl)
  have hu := graph_values hAQ (Fin.last (m+1)).castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc
    (Fin.last (m+3)) (Fin.last (m+2)).castSucc n.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc
    z.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc w.castSucc.castSucc.castSucc.castSucc
    r.castSucc.castSucc.castSucc.castSucc t.castSucc.castSucc.castSucc.castSucc hwQ hzQ hnQ hsQ
    (.conjL hPQ) (.conjL hQ) (.conjR hPQ) (.conjR hQ)
  simpa only [Formula.raise, unionOf_rename] using hu
end PPAC.Migration.IterationValueStep
