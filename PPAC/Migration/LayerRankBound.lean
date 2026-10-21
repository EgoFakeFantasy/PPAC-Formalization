import PPAC.Migration.LayerRankCollection

/-! 实际秩精确族的严格界给出包含全部成员的共同实际层。 -/
namespace PPAC.Migration.LayerRankBound
open Source SourceAlgebra SourceLogic RestrictionSyntax OrdinalSyntax HierarchyLayerSyntax
open LayerCoverSyntax LayerRankSyntax

theorem rank_into_layer {m} {Γ : Context m} (y a b v : Fin m)
    (hr : Derives Γ (rank y a)) (ha : Derives Γ (.mem a b))
    (heq : Derives Γ (HierarchyMemberSyntax.membership b v)) : Derives Γ (.mem y v) := by
  have hc := Derives.conjR (rank_property y a hr)
  let U := (layer a.castSucc (Fin.last m)).conj (subset y.castSucc (Fin.last m))
  let Ξ := Context.add U (Context.image Formula.raise Γ)
  change Derives Γ (.ex U) at hc
  apply Derives.exE (p := U) hc
  have haU : Derives Ξ (.mem a.castSucc b.castSucc) := under ha U
  have heqU : Derives Ξ (HierarchyMemberSyntax.membership b.castSucc v.castSucc) := by
    simpa only [Formula.raise, HierarchyMemberSyntax.membership_rename] using under heq U
  have hU : Derives Ξ U := .hyp (Or.inl rfl)
  have hm := HierarchyMemberSyntax.intro_layerMember b.castSucc y.castSucc a.castSucc (Fin.last m) (.conjI haU hU)
  exact .impE (.conjR (HierarchyMemberSyntax.membership_at b.castSucc v.castSucc y.castSucc heqU)) hm

theorem member_into_layer {m} {Γ : Context m} (c x b v y : Fin m)
    (ht : Derives Γ (ReplacementPredicates.total LayerRankSyntax.matrix Fin.elim0 x))
    (hr : Derives Γ (range c x)) (hb : Derives Γ (OrdinalStrictBound.strictUpper c b))
    (heq : Derives Γ (HierarchyMemberSyntax.membership b v)) (hy : Derives Γ (.mem y x)) : Derives Γ (.mem y v) := by
  have hf := LayerRankCollection.fiber_at x y ht hy
  let A := (rank y.castSucc (Fin.last m)).conj (uniqueRank y.castSucc (Fin.last m))
  let Ξ := Context.add A (Context.image Formula.raise Γ)
  change Derives Γ (.ex A) at hf
  apply Derives.exE (p := A) hf
  have hrA : Derives Ξ (range c.castSucc x.castSucc) := by
    simpa only [Formula.raise, range_rename] using under hr A
  have hbA : Derives Ξ (OrdinalStrictBound.strictUpper c.castSucc b.castSucc) := by
    simpa only [Formula.raise, OrdinalStrictBound.strictUpper_rename] using under hb A
  have heqA : Derives Ξ (HierarchyMemberSyntax.membership b.castSucc v.castSucc) := by
    simpa only [Formula.raise, HierarchyMemberSyntax.membership_rename] using under heq A
  have hyA : Derives Ξ (.mem y.castSucc x.castSucc) := under hy A
  have hA : Derives Ξ A := .hyp (Or.inl rfl)
  have hi := intro_image x.castSucc (Fin.last m) y.castSucc hyA (.conjL hA)
  have hm := Derives.impE (.conjR (range_at c.castSucc x.castSucc (Fin.last m) hrA)) hi
  have hd := Derives.impE (LayerCoverClosedInstances.strict_at c.castSucc b.castSucc (Fin.last m) hbA) hm
  exact rank_into_layer y.castSucc (Fin.last m) b.castSucc v.castSucc (.conjL hA) hd heqA

theorem subset_layer {m} {Γ : Context m} (c x b v : Fin m)
    (ht : Derives Γ (ReplacementPredicates.total LayerRankSyntax.matrix Fin.elim0 x))
    (hr : Derives Γ (range c x)) (hb : Derives Γ (OrdinalStrictBound.strictUpper c b))
    (heq : Derives Γ (HierarchyMemberSyntax.membership b v)) : Derives Γ (subset x v) := by
  apply Derives.allI
  let Δ := Context.image Formula.raise Γ
  have ht' : Derives Δ (ReplacementPredicates.total LayerRankSyntax.matrix Fin.elim0 x.castSucc) := by
    simpa only [Formula.raise, ReplacementPredicates.total_rename, empty_parameters] using Derives.rename Fin.castSucc ht
  have hr' : Derives Δ (range c.castSucc x.castSucc) := by
    simpa only [Formula.raise, range_rename] using Derives.rename Fin.castSucc hr
  have hb' : Derives Δ (OrdinalStrictBound.strictUpper c.castSucc b.castSucc) := by
    simpa only [Formula.raise, OrdinalStrictBound.strictUpper_rename] using Derives.rename Fin.castSucc hb
  have heq' : Derives Δ (HierarchyMemberSyntax.membership b.castSucc v.castSucc) := by
    simpa only [Formula.raise, HierarchyMemberSyntax.membership_rename] using Derives.rename Fin.castSucc heq
  apply Derives.impI
  exact member_into_layer c.castSucc x.castSucc b.castSucc v.castSucc (Fin.last m)
    (add ht' _) (add hr' _) (add hb' _) (add heq' _) (.hyp (Or.inl rfl))

theorem cover_from_range {m} {Γ : Context m} (c x : Fin m)
    (hBound : Derives Γ (ObjectOrdinalUnion.strictSentence.rename Fin.elim0))
    (hEx : Derives Γ (ObjectCumulativeHierarchy.existenceSentence.rename Fin.elim0))
    (hMem : Derives Γ (ObjectHierarchyAlgebra.membershipSentence.rename Fin.elim0))
    (ht : Derives Γ (ReplacementPredicates.total LayerRankSyntax.matrix Fin.elim0 x)) (hr : Derives Γ (range c x)) : Derives Γ (cover x) := by
  have hx := LayerCoverClosedInstances.strict_bound c hBound (LayerRankCollection.ordinals c x hr)
  let B := (ordinal (Fin.last m)).conj (OrdinalStrictBound.strictUpper c.castSucc (Fin.last m))
  let Γb := Context.add B (Context.image Formula.raise Γ)
  change Derives Γ (.ex B) at hx
  apply Derives.exE (p := B) hx
  have hExB : Derives Γb (ObjectCumulativeHierarchy.existenceSentence.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hEx B
  have hMemB : Derives Γb (ObjectHierarchyAlgebra.membershipSentence.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hMem B
  have htB : Derives Γb (ReplacementPredicates.total LayerRankSyntax.matrix Fin.elim0 x.castSucc) := by
    simpa only [Formula.raise, ReplacementPredicates.total_rename, empty_parameters] using under ht B
  have hrB : Derives Γb (range c.castSucc x.castSucc) := by
    simpa only [Formula.raise, range_rename] using under hr B
  have hB : Derives Γb B := .hyp (Or.inl rfl)
  have hv := HierarchyClosedInstances.existence (Fin.last m) hExB (.conjL hB)
  let V := layer (Fin.last m).castSucc (Fin.last (m+1))
  let Ξ := Context.add V (Context.image Formula.raise Γb)
  change Derives Γb (.ex V) at hv
  apply Derives.exE (p := V) hv
  have hMemV : Derives Ξ (ObjectHierarchyAlgebra.membershipSentence.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hMemB V
  have htV : Derives Ξ (ReplacementPredicates.total LayerRankSyntax.matrix Fin.elim0 x.castSucc.castSucc) := by
    simpa only [Formula.raise, ReplacementPredicates.total_rename, empty_parameters] using under htB V
  have hrV : Derives Ξ (range c.castSucc.castSucc x.castSucc.castSucc) := by
    simpa only [Formula.raise, range_rename] using under hrB V
  have hoV : Derives Ξ (ordinal (Fin.last m).castSucc) := by
    simpa only [Formula.raise, ordinal_rename] using under (.conjL hB) V
  have hbV : Derives Ξ (OrdinalStrictBound.strictUpper c.castSucc.castSucc (Fin.last m).castSucc) := by
    simpa only [Formula.raise, OrdinalStrictBound.strictUpper_rename] using under (.conjR hB) V
  have hV : Derives Ξ V := .hyp (Or.inl rfl)
  have heq := HierarchyClosedInstances.membership (Fin.last m).castSucc (Fin.last (m+1)) hMemV hoV hV
  have hs := subset_layer c.castSucc.castSucc x.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) htV hrV hbV heq
  simpa only [Formula.raise, cover_rename] using intro_cover x.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hoV hV hs
end PPAC.Migration.LayerRankBound
