import PPAC.Migration.WitnessRankCollection

/-! 最小见证秩的共同严格界层内，对每个原输入重新取得真实关系见证。 -/
namespace PPAC.Migration.WitnessRankBounds
open Source SourceAlgebra SourceLogic OrdinalSyntax WitnessRankSyntax
open ReplacementPredicates (paramsUp rel rel_rename)

theorem least_to_bounded {n m} {Γ : Context m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (x a b v : Fin m)
    (hl : Derives Γ (least p ρ x a)) (ha : Derives Γ (.mem a b))
    (heq : Derives Γ (HierarchyMemberSyntax.membership b v)) : Derives Γ (ReplacementPredicates.boundFiber p ρ v x) := by
  have hw := Derives.conjR (least_property p ρ x a hl)
  let Y := (rel p (paramsUp ρ) x.castSucc (Fin.last m)).conj (LayerRankSyntax.rank (Fin.last m) a.castSucc)
  let Ξ := Context.add Y (Context.image Formula.raise Γ)
  change Derives Γ (.ex Y) at hw
  apply Derives.exE (p := Y) hw
  have haY : Derives Ξ (.mem a.castSucc b.castSucc) := under ha Y
  have heqY : Derives Ξ (HierarchyMemberSyntax.membership b.castSucc v.castSucc) := by
    simpa only [Formula.raise, HierarchyMemberSyntax.membership_rename] using under heq Y
  have hY : Derives Ξ Y := .hyp (Or.inl rfl)
  have hm := LayerRankBound.rank_into_layer (Fin.last m) a.castSucc b.castSucc v.castSucc (.conjR hY) haY heqY
  have hout : Derives Ξ (ReplacementPredicates.boundFiber p (paramsUp ρ) v.castSucc x.castSucc) := by
    apply Derives.exI (Fin.last m)
    simp only [Formula.instantiate, Formula.rename, rel_rename, paramsUp,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
    exact .conjI hm (.conjL hY)
  simpa only [Formula.raise, ReplacementPredicates.boundFiber_rename] using hout

theorem input_bounded {n m} {Γ : Context m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (c a b v x : Fin m)
    (ht : Derives Γ (ReplacementPredicates.total (matrix p) ρ a))
    (hr : Derives Γ (range p ρ c a)) (hb : Derives Γ (OrdinalStrictBound.strictUpper c b))
    (heq : Derives Γ (HierarchyMemberSyntax.membership b v)) (hx : Derives Γ (.mem x a)) :
    Derives Γ (ReplacementPredicates.boundFiber p ρ v x) := by
  have hf := WitnessRankCollection.fiber_at p ρ a x ht hx
  let A := (least p (paramsUp ρ) x.castSucc (Fin.last m)).conj (uniqueLeast p (paramsUp ρ) x.castSucc (Fin.last m))
  let Ξ := Context.add A (Context.image Formula.raise Γ)
  change Derives Γ (.ex A) at hf
  apply Derives.exE (p := A) hf
  have hrA : Derives Ξ (range p (paramsUp ρ) c.castSucc a.castSucc) := by
    simpa only [Formula.raise, range_rename] using under hr A
  have hbA : Derives Ξ (OrdinalStrictBound.strictUpper c.castSucc b.castSucc) := by
    simpa only [Formula.raise, OrdinalStrictBound.strictUpper_rename] using under hb A
  have heqA : Derives Ξ (HierarchyMemberSyntax.membership b.castSucc v.castSucc) := by
    simpa only [Formula.raise, HierarchyMemberSyntax.membership_rename] using under heq A
  have hxA : Derives Ξ (.mem x.castSucc a.castSucc) := under hx A
  have hA : Derives Ξ A := .hyp (Or.inl rfl)
  have hi := intro_image p (paramsUp ρ) a.castSucc (Fin.last m) x.castSucc hxA (.conjL hA)
  have hm := Derives.impE (.conjR (range_at p (paramsUp ρ) c.castSucc a.castSucc (Fin.last m) hrA)) hi
  have hd := Derives.impE (LayerCoverClosedInstances.strict_at c.castSucc b.castSucc (Fin.last m) hbA) hm
  simpa only [Formula.raise, ReplacementPredicates.boundFiber_rename] using
    least_to_bounded p (paramsUp ρ) x.castSucc (Fin.last m) b.castSucc v.castSucc (.conjL hA) hd heqA

theorem covered {n m} {Γ : Context m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (c a b v : Fin m)
    (ht : Derives Γ (ReplacementPredicates.total (matrix p) ρ a))
    (hr : Derives Γ (range p ρ c a)) (hb : Derives Γ (OrdinalStrictBound.strictUpper c b))
    (heq : Derives Γ (HierarchyMemberSyntax.membership b v)) : Derives Γ (ReplacementPredicates.covered p ρ a v) := by
  apply Derives.allI
  let Δ := Context.image Formula.raise Γ
  have ht' : Derives Δ (ReplacementPredicates.total (matrix p) (paramsUp ρ) a.castSucc) := by
    simpa only [Formula.raise, ReplacementPredicates.total_rename] using Derives.rename Fin.castSucc ht
  have hr' : Derives Δ (range p (paramsUp ρ) c.castSucc a.castSucc) := by
    simpa only [Formula.raise, range_rename] using Derives.rename Fin.castSucc hr
  have hb' : Derives Δ (OrdinalStrictBound.strictUpper c.castSucc b.castSucc) := by
    simpa only [Formula.raise, OrdinalStrictBound.strictUpper_rename] using Derives.rename Fin.castSucc hb
  have heq' : Derives Δ (HierarchyMemberSyntax.membership b.castSucc v.castSucc) := by
    simpa only [Formula.raise, HierarchyMemberSyntax.membership_rename] using Derives.rename Fin.castSucc heq
  apply Derives.impI
  exact input_bounded p (paramsUp ρ) c.castSucc a.castSucc b.castSucc v.castSucc (Fin.last m)
    (add ht' _) (add hr' _) (add hb' _) (add heq' _) (.hyp (Or.inl rfl))

theorem collects_from_range {n m} {Γ : Context m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (c a : Fin m)
    (hBound : Derives Γ (ObjectOrdinalUnion.strictSentence.rename Fin.elim0))
    (hEx : Derives Γ (ObjectCumulativeHierarchy.existenceSentence.rename Fin.elim0))
    (hMem : Derives Γ (ObjectHierarchyAlgebra.membershipSentence.rename Fin.elim0))
    (ht : Derives Γ (ReplacementPredicates.total (matrix p) ρ a)) (hr : Derives Γ (range p ρ c a)) :
    Derives Γ (ReplacementPredicates.collects p ρ a) := by
  have hx := LayerCoverClosedInstances.strict_bound c hBound (WitnessRankCollection.ordinals p ρ c a hr)
  let B := (ordinal (Fin.last m)).conj (OrdinalStrictBound.strictUpper c.castSucc (Fin.last m))
  let Γb := Context.add B (Context.image Formula.raise Γ)
  change Derives Γ (.ex B) at hx
  apply Derives.exE (p := B) hx
  have hExB : Derives Γb (ObjectCumulativeHierarchy.existenceSentence.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hEx B
  have hMemB : Derives Γb (ObjectHierarchyAlgebra.membershipSentence.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hMem B
  have htB : Derives Γb (ReplacementPredicates.total (matrix p) (paramsUp ρ) a.castSucc) := by
    simpa only [Formula.raise, ReplacementPredicates.total_rename] using under ht B
  have hrB : Derives Γb (range p (paramsUp ρ) c.castSucc a.castSucc) := by
    simpa only [Formula.raise, range_rename] using under hr B
  have hB : Derives Γb B := .hyp (Or.inl rfl)
  have hv := HierarchyClosedInstances.existence (Fin.last m) hExB (.conjL hB)
  let V := HierarchyLayerSyntax.layer (Fin.last m).castSucc (Fin.last (m+1))
  let Ξ := Context.add V (Context.image Formula.raise Γb)
  change Derives Γb (.ex V) at hv
  apply Derives.exE (p := V) hv
  have hMemV : Derives Ξ (ObjectHierarchyAlgebra.membershipSentence.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hMemB V
  have htV : Derives Ξ (ReplacementPredicates.total (matrix p) (paramsUp (paramsUp ρ)) a.castSucc.castSucc) := by
    simpa only [Formula.raise, ReplacementPredicates.total_rename] using under htB V
  have hrV : Derives Ξ (range p (paramsUp (paramsUp ρ)) c.castSucc.castSucc a.castSucc.castSucc) := by
    simpa only [Formula.raise, range_rename] using under hrB V
  have hoV : Derives Ξ (ordinal (Fin.last m).castSucc) := by
    simpa only [Formula.raise, ordinal_rename] using under (.conjL hB) V
  have hbV : Derives Ξ (OrdinalStrictBound.strictUpper c.castSucc.castSucc (Fin.last m).castSucc) := by
    simpa only [Formula.raise, OrdinalStrictBound.strictUpper_rename] using under (.conjR hB) V
  have hV : Derives Ξ V := .hyp (Or.inl rfl)
  have heq := HierarchyClosedInstances.membership (Fin.last m).castSucc (Fin.last (m+1)) hMemV hoV hV
  have hc := covered p (paramsUp (paramsUp ρ)) c.castSucc.castSucc a.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) htV hrV hbV heq
  have hout : Derives Ξ (ReplacementPredicates.collects p (paramsUp (paramsUp ρ)) a.castSucc.castSucc) := by
    apply Derives.exI (Fin.last (m+1))
    simp only [Formula.instantiate, ReplacementPredicates.covered_rename, paramsUp,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
    exact hc
  simpa only [Formula.raise, ReplacementPredicates.collects_rename] using hout
end PPAC.Migration.WitnessRankBounds
