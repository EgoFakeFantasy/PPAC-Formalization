import PPAC.Migration.HierarchyFamilySyntax

/-! 原全Replacement实际收集任意内部原序数以前的全部层值。 -/
namespace PPAC.Migration.HierarchyLayerCollection
open Source SourceAlgebra SourceLogic OrdinalSyntax HierarchyFamilySyntax

theorem total_layers {m} {Γ : Context m} (a : Fin m)
    (hUnique : Derives Γ (ObjectCumulativeHierarchy.uniquenessSentence.rename Fin.elim0))
    (ha : Derives Γ (ordinal a)) : Derives Γ (ReplacementPredicates.total matrix Fin.elim0 a) := by
  simp only [ReplacementPredicates.total, matrix_fiber]
  apply Derives.allI
  let Δ := Context.image Formula.raise Γ
  have hUnique' : Derives Δ (ObjectCumulativeHierarchy.uniquenessSentence.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc hUnique
  have ha' : Derives Δ (ordinal a.castSucc) := by
    simpa only [Formula.raise, ordinal_rename] using Derives.rename Fin.castSucc ha
  apply Derives.impI
  let M := Formula.mem (Fin.last m) a.castSucc
  have hm : Derives (Context.add M Δ) M := .hyp (Or.inl rfl)
  exact HierarchyClosedInstances.uniqueness (Fin.last m) (add hUnique' M)
    (OrdinalRestriction.member a.castSucc (Fin.last m) (add ha' M) hm)

theorem exists_range {m} {Γ : Context m} (a : Fin m)
    (hUnique : Derives Γ (ObjectCumulativeHierarchy.uniquenessSentence.rename Fin.elim0))
    (hr : Derives Γ ((Source.SetLanguage.replacement matrix).rename Fin.elim0))
    (ha : Derives Γ (ordinal a)) : Derives Γ (rangeExists a) := by
  have hi := Derives.impE (IterationValueCollection.replacement_instance matrix Fin.elim0 a hr) (total_layers a hUnique ha)
  simpa only [ReplacementPredicates.imageExists, matrix_range, rangeExists] using hi

theorem range_unique {m} {Γ : Context m} (c d a : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hc : Derives Γ (range c a)) (hd : Derives Γ (range d a)) : Derives Γ (.equal c d) := by
  apply Derives.impE (PairSyntax.extensionality_instance c d he)
  apply Derives.allI
  let Δ := Context.image Formula.raise Γ
  have hc' : Derives Δ (range c.castSucc a.castSucc) := by
    simpa only [Formula.raise, range_rename] using Derives.rename Fin.castSucc hc
  have hd' : Derives Δ (range d.castSucc a.castSucc) := by
    simpa only [Formula.raise, range_rename] using Derives.rename Fin.castSucc hd
  have hcz := range_at c.castSucc a.castSucc (Fin.last m) hc'
  have hdz := range_at d.castSucc a.castSucc (Fin.last m) hd'
  apply Derives.conjI
  · apply Derives.impI
    exact .impE (.conjR (add hdz _)) (.impE (.conjL (add hcz _)) (.hyp (Or.inl rfl)))
  · apply Derives.impI
    exact .impE (.conjR (add hcz _)) (.impE (.conjL (add hdz _)) (.hyp (Or.inl rfl)))
end PPAC.Migration.HierarchyLayerCollection
