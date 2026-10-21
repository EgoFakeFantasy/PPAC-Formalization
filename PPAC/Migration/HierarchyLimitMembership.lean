import PPAC.Migration.HierarchyLimitSyntax

/-! 在全部内部零或极限序数上，实际层成员恰来自某个实际早层。 -/
namespace PPAC.Migration.HierarchyLimitMembership
open Source SourceAlgebra SourceLogic RestrictionSyntax OrdinalSyntax HierarchyLayerSyntax
open HierarchyMemberSyntax HierarchyLimitSyntax

theorem point_forward {m} {Γ : Context m} (a z b v : Fin m)
    (hEx : Derives Γ (ObjectCumulativeHierarchy.existenceSentence.rename Fin.elim0))
    (hSucc : Derives Γ (ObjectHierarchyAlgebra.successorSentence.rename Fin.elim0))
    (ha : Derives Γ (ordinal a)) (hc : Derives Γ (closedSuccessor a))
    (hb : Derives Γ (.mem b a)) (hv : Derives Γ (layer b v)) (hz : Derives Γ (subset z v)) :
    Derives Γ (unionMember a z) := by
  have hs := Derives.impE (closed_at a b hc) hb
  let S := (OmegaSyntax.successor (Fin.last m) b.castSucc).conj (.mem (Fin.last m) a.castSucc)
  let Γs := Context.add S (Context.image Formula.raise Γ)
  change Derives Γ (.ex S) at hs
  apply Derives.exE (p := S) hs
  have hExS : Derives Γs (ObjectCumulativeHierarchy.existenceSentence.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hEx S
  have hSuccS : Derives Γs (ObjectHierarchyAlgebra.successorSentence.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hSucc S
  have haS : Derives Γs (ordinal a.castSucc) := by
    simpa only [Formula.raise, ordinal_rename] using under ha S
  have hbS : Derives Γs (.mem b.castSucc a.castSucc) := under hb S
  have hvS : Derives Γs (layer b.castSucc v.castSucc) := by
    simpa only [Formula.raise, layer_rename] using under hv S
  have hzS : Derives Γs (subset z.castSucc v.castSucc) := by
    simpa only [Formula.raise, subset_rename] using under hz S
  have hS : Derives Γs S := .hyp (Or.inl rfl)
  have hoB := OrdinalRestriction.member a.castSucc b.castSucc haS hbS
  have hoS := OrdinalRestriction.member a.castSucc (Fin.last m) haS (.conjR hS)
  have hy := HierarchyClosedInstances.existence (Fin.last m) hExS hoS
  let Y := layer (Fin.last m).castSucc (Fin.last (m+1))
  let Ξ := Context.add Y (Context.image Formula.raise Γs)
  change Derives Γs (.ex Y) at hy
  apply Derives.exE (p := Y) hy
  have hSuccY : Derives Ξ (ObjectHierarchyAlgebra.successorSentence.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hSuccS Y
  have hoBY : Derives Ξ (ordinal b.castSucc.castSucc) := by
    simpa only [Formula.raise, ordinal_rename] using under hoB Y
  have hvY : Derives Ξ (layer b.castSucc.castSucc v.castSucc.castSucc) := by
    simpa only [Formula.raise, layer_rename] using under hvS Y
  have hzY : Derives Ξ (subset z.castSucc.castSucc v.castSucc.castSucc) := by
    simpa only [Formula.raise, subset_rename] using under hzS Y
  have hSY : Derives Ξ ((OmegaSyntax.successor (Fin.last m).castSucc b.castSucc.castSucc).conj
      (.mem (Fin.last m).castSucc a.castSucc.castSucc)) := by
    simpa only [Formula.raise, S, Formula.rename, OmegaSyntax.successor_rename] using under hS Y
  have hY : Derives Ξ Y := .hyp (Or.inl rfl)
  have hp := HierarchyClosedInstances.successor b.castSucc.castSucc (Fin.last m).castSucc v.castSucc.castSucc (Fin.last (m+1))
    hSuccY hoBY (.conjL hSY) hvY hY
  have hm := Derives.impE (.conjR (PowerSetSyntax.power_at (Fin.last (m+1)) v.castSucc.castSucc z.castSucc.castSucc hp)) hzY
  simpa only [Formula.raise, unionMember_rename] using intro_unionMember a.castSucc.castSucc z.castSucc.castSucc
    (Fin.last m).castSucc (Fin.last (m+1)) (.conjI (.conjR hSY) (.conjI hY hm))

theorem forward {m} {Γ : Context m} (a z : Fin m)
    (hEx : Derives Γ (ObjectCumulativeHierarchy.existenceSentence.rename Fin.elim0))
    (hSucc : Derives Γ (ObjectHierarchyAlgebra.successorSentence.rename Fin.elim0))
    (hl : Derives Γ (limitIndex a)) (hz : Derives Γ (layerMember a z)) : Derives Γ (unionMember a z) := by
  let W := layerMemberWitnesses a z
  let Ξ := Context.add W (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_layerMember a z _ hz
  have hExW : Derives Ξ (ObjectCumulativeHierarchy.existenceSentence.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using OrderedPairElimination.under_two hEx W
  have hSuccW : Derives Ξ (ObjectHierarchyAlgebra.successorSentence.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using OrderedPairElimination.under_two hSucc W
  have hlW : Derives Ξ (limitIndex a.castSucc.castSucc) := by
    simpa only [Formula.raise, limitIndex_rename] using OrderedPairElimination.under_two hl W
  have hW : Derives Ξ W := .hyp (Or.inl rfl)
  simpa only [Formula.raise, unionMember_rename] using point_forward a.castSucc.castSucc z.castSucc.castSucc
    (Fin.last m).castSucc (Fin.last (m+1)) hExW hSuccW (.conjL hlW) (.conjR hlW)
    (.conjL hW) (.conjL (.conjR hW)) (.conjR (.conjR hW))

theorem backward {m} {Γ : Context m} (a y z : Fin m)
    (hMem : Derives Γ (ObjectHierarchyAlgebra.membershipSentence.rename Fin.elim0))
    (ha : Derives Γ (ordinal a)) (hy : Derives Γ (membership a y)) (hz : Derives Γ (unionMember a z)) :
    Derives Γ (.mem z y) := by
  let W := unionWitnesses a z
  let Ξ := Context.add W (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_unionMember a z _ hz
  have hMemW : Derives Ξ (ObjectHierarchyAlgebra.membershipSentence.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using OrderedPairElimination.under_two hMem W
  have haW : Derives Ξ (ordinal a.castSucc.castSucc) := by
    simpa only [Formula.raise, ordinal_rename] using OrderedPairElimination.under_two ha W
  have hyW : Derives Ξ (membership a.castSucc.castSucc y.castSucc.castSucc) := by
    simpa only [Formula.raise, membership_rename] using OrderedPairElimination.under_two hy W
  have hW : Derives Ξ W := .hyp (Or.inl rfl)
  have hb := OrdinalRestriction.member a.castSucc.castSucc (Fin.last m).castSucc haW (.conjL hW)
  have hv := HierarchyClosedInstances.membership (Fin.last m).castSucc (Fin.last (m+1)) hMemW hb (.conjL (.conjR hW))
  have hs := OrdinalTransitivity.subset_of_member a.castSucc.castSucc (Fin.last m).castSucc (.conjL haW) (.conjL hW)
  have hmon := HierarchyAlgebra.monotone a.castSucc.castSucc (Fin.last m).castSucc y.castSucc.castSucc (Fin.last (m+1)) hs hyW hv
  exact .impE (subset_at (Fin.last (m+1)) y.castSucc.castSucc z.castSucc.castSucc hmon) (.conjR (.conjR hW))

theorem layer_union_equation {m} {Γ : Context m} (a y : Fin m)
    (hEx : Derives Γ (ObjectCumulativeHierarchy.existenceSentence.rename Fin.elim0))
    (hSucc : Derives Γ (ObjectHierarchyAlgebra.successorSentence.rename Fin.elim0))
    (hMem : Derives Γ (ObjectHierarchyAlgebra.membershipSentence.rename Fin.elim0))
    (hl : Derives Γ (limitIndex a)) (hy : Derives Γ (layer a y)) : Derives Γ (unionEquation a y) := by
  have heq := HierarchyClosedInstances.membership a y hMem (.conjL hl) hy
  apply Derives.allI
  let Δ := Context.image Formula.raise Γ
  have hEx' : Derives Δ (ObjectCumulativeHierarchy.existenceSentence.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc hEx
  have hSucc' : Derives Δ (ObjectHierarchyAlgebra.successorSentence.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc hSucc
  have hMem' : Derives Δ (ObjectHierarchyAlgebra.membershipSentence.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc hMem
  have hl' : Derives Δ (limitIndex a.castSucc) := by
    simpa only [Formula.raise, limitIndex_rename] using Derives.rename Fin.castSucc hl
  have heq' : Derives Δ (membership a.castSucc y.castSucc) := by
    simpa only [Formula.raise, membership_rename] using Derives.rename Fin.castSucc heq
  apply Derives.conjI
  · apply Derives.impI
    let M := Formula.mem (Fin.last m) y.castSucc
    have hm : Derives (Context.add M Δ) M := .hyp (Or.inl rfl)
    have hx := Derives.impE (.conjL (add (membership_at a.castSucc y.castSucc (Fin.last m) heq') M)) hm
    exact forward a.castSucc (Fin.last m) (add hEx' M) (add hSucc' M) (add hl' M) hx
  · apply Derives.impI
    exact backward a.castSucc y.castSucc (Fin.last m) (add hMem' _) (add (.conjL hl') _) (add heq' _) (.hyp (Or.inl rfl))
end PPAC.Migration.HierarchyLimitMembership
