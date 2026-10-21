import PPAC.Migration.LayerRankBound

/-! 实际唯一秩收集和共同层界给对象全体集合归纳的进步步。 -/
namespace PPAC.Migration.LayerCoverInduction
open Source SourceAlgebra SourceLogic HierarchyLayerSyntax LayerCoverSyntax LayerRankSyntax

theorem step {m} {Γ : Context m} (x : Fin m)
    (hUnique : Derives Γ ((ObjectOrdinalLeast.uniquenessSentence containsMatrix).rename Fin.elim0))
    (hBound : Derives Γ (ObjectOrdinalUnion.strictSentence.rename Fin.elim0))
    (hEx : Derives Γ (ObjectCumulativeHierarchy.existenceSentence.rename Fin.elim0))
    (hMem : Derives Γ (ObjectHierarchyAlgebra.membershipSentence.rename Fin.elim0))
    (hRep : Derives Γ ((Source.SetLanguage.replacement matrix).rename Fin.elim0))
    (hh : Derives Γ (membersCovered x)) : Derives Γ (cover x) := by
  have ht := LayerRankCollection.total_ranks x hUnique hh
  have hc := LayerRankCollection.exists_range x hUnique hRep hh
  let C := range (Fin.last m) x.castSucc
  let Ξ := Context.add C (Context.image Formula.raise Γ)
  change Derives Γ (.ex C) at hc
  apply Derives.exE (p := C) hc
  have hBoundC : Derives Ξ (ObjectOrdinalUnion.strictSentence.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hBound C
  have hExC : Derives Ξ (ObjectCumulativeHierarchy.existenceSentence.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hEx C
  have hMemC : Derives Ξ (ObjectHierarchyAlgebra.membershipSentence.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hMem C
  have htC : Derives Ξ (ReplacementPredicates.total matrix Fin.elim0 x.castSucc) := by
    simpa only [Formula.raise, ReplacementPredicates.total_rename, empty_parameters] using under ht C
  have hC : Derives Ξ C := .hyp (Or.inl rfl)
  simpa only [Formula.raise, cover_rename] using LayerRankBound.cover_from_range (Fin.last m) x.castSucc hBoundC hExC hMemC htC hC

theorem progressive {m} {Γ : Context m}
    (hUnique : Derives Γ ((ObjectOrdinalLeast.uniquenessSentence containsMatrix).rename Fin.elim0))
    (hBound : Derives Γ (ObjectOrdinalUnion.strictSentence.rename Fin.elim0))
    (hEx : Derives Γ (ObjectCumulativeHierarchy.existenceSentence.rename Fin.elim0))
    (hMem : Derives Γ (ObjectHierarchyAlgebra.membershipSentence.rename Fin.elim0))
    (hRep : Derives Γ ((Source.SetLanguage.replacement matrix).rename Fin.elim0)) :
    Derives Γ (SetInductionSyntax.progressive coverMatrix Fin.elim0) := by
  simp only [SetInductionSyntax.progressive, members_below, cover_pred]
  apply Derives.allI
  let Δ := Context.image Formula.raise Γ
  have hUnique' : Derives Δ ((ObjectOrdinalLeast.uniquenessSentence containsMatrix).rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc hUnique
  have hBound' : Derives Δ (ObjectOrdinalUnion.strictSentence.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc hBound
  have hEx' : Derives Δ (ObjectCumulativeHierarchy.existenceSentence.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc hEx
  have hMem' : Derives Δ (ObjectHierarchyAlgebra.membershipSentence.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc hMem
  have hRep' : Derives Δ ((Source.SetLanguage.replacement matrix).rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc hRep
  apply Derives.impI
  exact step (Fin.last m) (add hUnique' _) (add hBound' _) (add hEx' _) (add hMem' _) (add hRep' _) (.hyp (Or.inl rfl))

theorem all_covers {m} {Γ : Context m}
    (hUnique : Derives Γ ((ObjectOrdinalLeast.uniquenessSentence containsMatrix).rename Fin.elim0))
    (hBound : Derives Γ (ObjectOrdinalUnion.strictSentence.rename Fin.elim0))
    (hEx : Derives Γ (ObjectCumulativeHierarchy.existenceSentence.rename Fin.elim0))
    (hMem : Derives Γ (ObjectHierarchyAlgebra.membershipSentence.rename Fin.elim0))
    (hRep : Derives Γ ((Source.SetLanguage.replacement matrix).rename Fin.elim0))
    (hSep : Derives Γ ((Source.SetLanguage.separation coverMatrix.neg).rename Fin.elim0))
    (hFoundation : Derives Γ (Source.SetLanguage.foundation.rename Fin.elim0))
    (hTC : Derives Γ (ObjectTransitiveCover.coverSentence.rename Fin.elim0)) :
    Derives Γ (SetInductionSyntax.holds coverMatrix Fin.elim0) :=
  SetInduction.all_holds coverMatrix Fin.elim0 hSep hFoundation hTC (progressive hUnique hBound hEx hMem hRep)
end PPAC.Migration.LayerCoverInduction
