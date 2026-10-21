import PPAC.Migration.WitnessRankFibers

/-! 原Replacement收集任意原关系的唯一最小见证秩，实际得到精确内部序数族。 -/
namespace PPAC.Migration.WitnessRankCollection
open Source SourceAlgebra SourceLogic OrdinalSyntax WitnessRankSyntax
open ReplacementPredicates (paramsUp)

theorem exists_range {n m} {Γ : Context m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (a : Fin m)
    (hRank : Derives Γ (ObjectRankCover.rankSentence.rename Fin.elim0))
    (hMin : Derives Γ ((ObjectOrdinalLeast.uniquenessSentence (predicate p)).rename Fin.elim0))
    (hRep : Derives Γ ((Source.SetLanguage.replacement (matrix p)).rename Fin.elim0))
    (ht : Derives Γ (ReplacementPredicates.totalRelation p ρ a)) : Derives Γ (rangeExists p ρ a) := by
  have hi := Derives.impE (IterationValueCollection.replacement_instance (matrix p) ρ a hRep)
    (WitnessRankFibers.total_least p ρ a hRank hMin ht)
  simpa only [ReplacementPredicates.imageExists, matrix_range, rangeExists] using hi

theorem ordinals {n m} {Γ : Context m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (c a : Fin m)
    (hr : Derives Γ (range p ρ c a)) : Derives Γ (OrdinalFamilySyntax.ordinals c) := by
  apply Derives.allI
  let Δ := Context.image Formula.raise Γ
  have hr' : Derives Δ (range p (paramsUp ρ) c.castSucc a.castSucc) := by
    simpa only [Formula.raise, range_rename] using Derives.rename Fin.castSucc hr
  apply Derives.impI
  let M := Formula.mem (Fin.last m) c.castSucc
  let Γb := Context.add M Δ
  have hm : Derives Γb M := .hyp (Or.inl rfl)
  have hi := Derives.impE (.conjL (add (range_at p (paramsUp ρ) c.castSucc a.castSucc (Fin.last m) hr') M)) hm
  let X := (Formula.mem (Fin.last (m+1)) a.castSucc.castSucc).conj
    (least p (paramsUp (paramsUp ρ)) (Fin.last (m+1)) (Fin.last m).castSucc)
  let Ξ := Context.add X (Context.image Formula.raise Γb)
  change Derives Γb (.ex X) at hi
  apply Derives.exE (p := X) hi
  have hX : Derives Ξ X := .hyp (Or.inl rfl)
  have ho : Derives Ξ (ordinal (Fin.last m).castSucc) :=
    .conjL (least_property p (paramsUp (paramsUp ρ)) (Fin.last (m+1)) (Fin.last m).castSucc (.conjR hX))
  simpa only [Formula.raise, ordinal_rename] using ho

theorem fiber_at {n m} {Γ : Context m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (a x : Fin m)
    (ht : Derives Γ (ReplacementPredicates.total (matrix p) ρ a)) (hx : Derives Γ (.mem x a)) : Derives Γ (fiber p ρ x) := by
  have hi := Derives.impE (ReplacementPredicates.specialize_total (matrix p) ρ a x ht) hx
  simpa only [matrix_fiber] using hi
end PPAC.Migration.WitnessRankCollection
