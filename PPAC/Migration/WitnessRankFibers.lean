import PPAC.Migration.WitnessRankSyntax

/-! 每个原关系见证有实际秩；非空见证秩性质给唯一最小序数，原见证无须唯一。 -/
namespace PPAC.Migration.WitnessRankFibers
open Source SourceAlgebra SourceLogic OrdinalSyntax WitnessRankSyntax
open ReplacementPredicates (paramsUp rel rel_rename)

theorem global_rank_at {m} {Γ : Context m} (y : Fin m)
    (hh : Derives Γ (ObjectRankCover.rankSentence.rename Fin.elim0)) : Derives Γ (LayerRankSyntax.fiber y) := by
  have hi := specialize_close (LayerRankSyntax.fiber (0 : Fin 1)) (fun _ => y) hh
  simpa only [LayerRankSyntax.fiber_rename] using hi

theorem has_of_value {n m} {Γ : Context m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (x : Fin m)
    (hRank : Derives Γ (ObjectRankCover.rankSentence.rename Fin.elim0))
    (hv : Derives Γ (ReplacementPredicates.hasValue p ρ x)) : Derives Γ (hasOrdinal p ρ x) := by
  let Y := rel p (paramsUp ρ) x.castSucc (Fin.last m)
  let Γy := Context.add Y (Context.image Formula.raise Γ)
  change Derives Γ (.ex Y) at hv
  apply Derives.exE (p := Y) hv
  have hRankY : Derives Γy (ObjectRankCover.rankSentence.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hRank Y
  have hY : Derives Γy Y := .hyp (Or.inl rfl)
  have ha := global_rank_at (Fin.last m) hRankY
  let A := (LayerRankSyntax.rank (Fin.last m).castSucc (Fin.last (m+1))).conj
    (LayerRankSyntax.uniqueRank (Fin.last m).castSucc (Fin.last (m+1)))
  let Ξ := Context.add A (Context.image Formula.raise Γy)
  change Derives Γy (.ex A) at ha
  apply Derives.exE (p := A) ha
  have hYA : Derives Ξ (rel p (paramsUp (paramsUp ρ)) x.castSucc.castSucc (Fin.last m).castSucc) := by
    simpa only [Formula.raise, Y, rel_rename] using under hY A
  have hA : Derives Ξ A := .hyp (Or.inl rfl)
  have ho := Derives.conjL (LayerRankSyntax.rank_property (Fin.last m).castSucc (Fin.last (m+1)) (.conjL hA))
  have hw := intro_witness p (paramsUp (paramsUp ρ)) x.castSucc.castSucc (Fin.last (m+1)) (Fin.last m).castSucc hYA (.conjL hA)
  simpa only [Formula.raise, hasOrdinal_rename] using intro_hasOrdinal p (paramsUp (paramsUp ρ)) x.castSucc.castSucc (Fin.last (m+1)) ho hw

theorem fiber_of_has {n m} {Γ : Context m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (x : Fin m)
    (hMin : Derives Γ ((ObjectOrdinalLeast.uniquenessSentence (predicate p)).rename Fin.elim0))
    (hh : Derives Γ (hasOrdinal p ρ x)) : Derives Γ (fiber p ρ x) := by
  have hi := specialize_close ((OrdinalLeastSyntax.has (predicate p) (id : Fin (n+1) → Fin (n+1))).imp
    (OrdinalLeastSyntax.fiber (predicate p) id)) (Fin.lastCases x ρ) hMin
  have hc : Derives Γ ((hasOrdinal p ρ x).imp (fiber p ρ x)) := by
    simpa only [Formula.rename, OrdinalLeastSyntax.has_rename, OrdinalLeastSyntax.fiber_rename,
      id_eq, has_least, least_fiber] using hi
  exact .impE hc hh

theorem total_relation_at {n m} {Γ : Context m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (a x : Fin m)
    (ht : Derives Γ (ReplacementPredicates.totalRelation p ρ a)) :
    Derives Γ ((Formula.mem x a).imp (ReplacementPredicates.hasValue p ρ x)) := by
  have hi := Derives.allE x ht
  simpa only [Formula.instantiate, Formula.rename, ReplacementPredicates.hasValue_rename, paramsUp,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi

theorem total_least {n m} {Γ : Context m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (a : Fin m)
    (hRank : Derives Γ (ObjectRankCover.rankSentence.rename Fin.elim0))
    (hMin : Derives Γ ((ObjectOrdinalLeast.uniquenessSentence (predicate p)).rename Fin.elim0))
    (ht : Derives Γ (ReplacementPredicates.totalRelation p ρ a)) :
    Derives Γ (ReplacementPredicates.total (matrix p) ρ a) := by
  simp only [ReplacementPredicates.total, matrix_fiber]
  apply Derives.allI
  let Δ := Context.image Formula.raise Γ
  have hRank' : Derives Δ (ObjectRankCover.rankSentence.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc hRank
  have hMin' : Derives Δ ((ObjectOrdinalLeast.uniquenessSentence (predicate p)).rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc hMin
  have ht' : Derives Δ (ReplacementPredicates.totalRelation p (paramsUp ρ) a.castSucc) := by
    simpa only [Formula.raise, ReplacementPredicates.totalRelation_rename] using Derives.rename Fin.castSucc ht
  apply Derives.impI
  let M := Formula.mem (Fin.last m) a.castSucc
  have hm : Derives (Context.add M Δ) M := .hyp (Or.inl rfl)
  have hv := Derives.impE (add (total_relation_at p (paramsUp ρ) a.castSucc (Fin.last m) ht') M) hm
  exact fiber_of_has p (paramsUp ρ) (Fin.last m) (add hMin' M)
    (has_of_value p (paramsUp ρ) (Fin.last m) (add hRank' M) hv)
end PPAC.Migration.WitnessRankFibers
