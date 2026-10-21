import PPAC.Migration.LayerCoverClosedInstances

/-! 在对象归纳前提内取得各成员唯一秩，原Replacement实际构造其精确序数集合。 -/
namespace PPAC.Migration.LayerRankCollection
open Source SourceAlgebra SourceLogic OrdinalSyntax LayerCoverSyntax LayerRankSyntax

theorem total_ranks {m} {Γ : Context m} (x : Fin m)
    (hUnique : Derives Γ ((ObjectOrdinalLeast.uniquenessSentence containsMatrix).rename Fin.elim0))
    (hh : Derives Γ (membersCovered x)) : Derives Γ (ReplacementPredicates.total matrix Fin.elim0 x) := by
  simp only [ReplacementPredicates.total, matrix_fiber]
  apply Derives.allI
  let Δ := Context.image Formula.raise Γ
  have hUnique' : Derives Δ ((ObjectOrdinalLeast.uniquenessSentence containsMatrix).rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc hUnique
  have hh' : Derives Δ (membersCovered x.castSucc) := by
    simpa only [Formula.raise, membersCovered_rename] using Derives.rename Fin.castSucc hh
  apply Derives.impI
  let M := Formula.mem (Fin.last m) x.castSucc
  have hm : Derives (Context.add M Δ) M := .hyp (Or.inl rfl)
  have hcov := Derives.impE (add (members_at x.castSucc (Fin.last m) hh') M) hm
  exact LayerCoverClosedInstances.rank_fiber (Fin.last m) (add hUnique' M) hcov

theorem exists_range {m} {Γ : Context m} (x : Fin m)
    (hUnique : Derives Γ ((ObjectOrdinalLeast.uniquenessSentence containsMatrix).rename Fin.elim0))
    (hr : Derives Γ ((Source.SetLanguage.replacement matrix).rename Fin.elim0))
    (hh : Derives Γ (membersCovered x)) : Derives Γ (rangeExists x) := by
  have hi := Derives.impE (IterationValueCollection.replacement_instance matrix Fin.elim0 x hr) (total_ranks x hUnique hh)
  simpa only [ReplacementPredicates.imageExists, matrix_range, rangeExists] using hi

theorem ordinals {m} {Γ : Context m} (c x : Fin m) (hr : Derives Γ (range c x)) :
    Derives Γ (OrdinalFamilySyntax.ordinals c) := by
  apply Derives.allI
  let Δ := Context.image Formula.raise Γ
  have hr' : Derives Δ (range c.castSucc x.castSucc) := by
    simpa only [Formula.raise, range_rename] using Derives.rename Fin.castSucc hr
  apply Derives.impI
  let M := Formula.mem (Fin.last m) c.castSucc
  let Γa := Context.add M Δ
  have hm : Derives Γa M := .hyp (Or.inl rfl)
  have hi := Derives.impE (.conjL (add (range_at c.castSucc x.castSucc (Fin.last m) hr') M)) hm
  let Y := (Formula.mem (Fin.last (m+1)) x.castSucc.castSucc).conj (rank (Fin.last (m+1)) (Fin.last m).castSucc)
  let Ξ := Context.add Y (Context.image Formula.raise Γa)
  change Derives Γa (.ex Y) at hi
  apply Derives.exE (p := Y) hi
  have hY : Derives Ξ Y := .hyp (Or.inl rfl)
  have ho : Derives Ξ (ordinal (Fin.last m).castSucc) :=
    .conjL (rank_property (Fin.last (m+1)) (Fin.last m).castSucc (.conjR hY))
  simpa only [Formula.raise, ordinal_rename] using ho

theorem fiber_at {m} {Γ : Context m} (x y : Fin m)
    (ht : Derives Γ (ReplacementPredicates.total matrix Fin.elim0 x)) (hy : Derives Γ (.mem y x)) : Derives Γ (fiber y) := by
  have hi := Derives.impE (ReplacementPredicates.specialize_total matrix Fin.elim0 x y ht) hy
  simpa only [matrix_fiber] using hi
end PPAC.Migration.LayerRankCollection
