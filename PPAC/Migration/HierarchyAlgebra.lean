import PPAC.Migration.HierarchyMembership

/-! 由实际成员递归方程推出层的单调性、早期层成员性和传递性。 -/
namespace PPAC.Migration.HierarchyAlgebra
open Source SourceAlgebra SourceLogic RestrictionSyntax OrdinalSyntax HierarchyLayerSyntax HierarchyMemberSyntax

theorem index_subset {m} {Γ : Context m} (a b z : Fin m)
    (hs : Derives Γ (subset b a)) (hz : Derives Γ (layerMember b z)) : Derives Γ (layerMember a z) := by
  let W := layerMemberWitnesses b z
  let Ξ := Context.add W (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_layerMember b z _ hz
  have hsW : Derives Ξ (subset b.castSucc.castSucc a.castSucc.castSucc) := by
    simpa only [Formula.raise, subset_rename] using OrderedPairElimination.under_two hs W
  have hW : Derives Ξ W := .hyp (Or.inl rfl)
  have hba := Derives.impE (subset_at b.castSucc.castSucc a.castSucc.castSucc (Fin.last m).castSucc hsW) (.conjL hW)
  simpa only [Formula.raise, layerMember_rename] using intro_layerMember a.castSucc.castSucc z.castSucc.castSucc
    (Fin.last m).castSucc (Fin.last (m+1)) (.conjI hba (.conjR hW))

theorem monotone {m} {Γ : Context m} (a b u v : Fin m)
    (hs : Derives Γ (subset b a)) (hu : Derives Γ (membership a u)) (hv : Derives Γ (membership b v)) :
    Derives Γ (subset v u) := by
  apply Derives.allI
  let Δ := Context.image Formula.raise Γ
  have hs' : Derives Δ (subset b.castSucc a.castSucc) := by
    simpa only [Formula.raise, subset_rename] using Derives.rename Fin.castSucc hs
  have hu' : Derives Δ (membership a.castSucc u.castSucc) := by
    simpa only [Formula.raise, membership_rename] using Derives.rename Fin.castSucc hu
  have hv' : Derives Δ (membership b.castSucc v.castSucc) := by
    simpa only [Formula.raise, membership_rename] using Derives.rename Fin.castSucc hv
  apply Derives.impI
  let M := Formula.mem (Fin.last m) v.castSucc
  have hm : Derives (Context.add M Δ) M := .hyp (Or.inl rfl)
  have hx := Derives.impE (.conjL (add (membership_at b.castSucc v.castSucc (Fin.last m) hv') M)) hm
  have hy := index_subset a.castSucc b.castSucc (Fin.last m) (add hs' M) hx
  exact .impE (.conjR (add (membership_at a.castSucc u.castSucc (Fin.last m) hu') M)) hy

theorem value_member {m} {Γ : Context m} (a b u v : Fin m)
    (hb : Derives Γ (.mem b a)) (hv : Derives Γ (layer b v)) (hu : Derives Γ (membership a u)) :
    Derives Γ (.mem v u) :=
  .impE (.conjR (membership_at a u v hu)) (intro_layerMember a v b v
    (.conjI hb (.conjI hv (.allI (.impI (.hyp (Or.inl rfl)))))))

theorem element_subset {m} {Γ : Context m} (hA : OrdinalRecursionContext.Evidence Γ)
    (hsep : Derives Γ ((Source.SetLanguage.separation RestrictionSyntax.matrix).rename Fin.elim0))
    (hp : Derives Γ (Source.SetLanguage.powerSet.rename Fin.elim0)) (a u z : Fin m)
    (hd : Derives Γ (OrdinalRecursionDeterminism.deterministic PowerUnionSyntax.matrix Fin.elim0))
    (ha : Derives Γ (ordinal a)) (hu : Derives Γ (membership a u)) (hz : Derives Γ (.mem z u)) :
    Derives Γ (subset z u) := by
  have hx := Derives.impE (.conjL (membership_at a u z hu)) hz
  let W := layerMemberWitnesses a z
  let Ξ := Context.add W (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_layerMember a z _ hx
  have hAW := OrdinalRecursionContext.under_two hA W
  have hsepW : Derives Ξ ((Source.SetLanguage.separation RestrictionSyntax.matrix).rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using OrderedPairElimination.under_two hsep W
  have hpW : Derives Ξ (Source.SetLanguage.powerSet.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using OrderedPairElimination.under_two hp W
  have hdW : Derives Ξ (OrdinalRecursionDeterminism.deterministic PowerUnionSyntax.matrix Fin.elim0) := by
    simpa only [Formula.raise, OrdinalRecursionDeterminism.deterministic_rename, empty_parameters] using OrderedPairElimination.under_two hd W
  have haW : Derives Ξ (ordinal a.castSucc.castSucc) := by
    simpa only [Formula.raise, ordinal_rename] using OrderedPairElimination.under_two ha W
  have huW : Derives Ξ (membership a.castSucc.castSucc u.castSucc.castSucc) := by
    simpa only [Formula.raise, membership_rename] using OrderedPairElimination.under_two hu W
  have hW : Derives Ξ W := .hyp (Or.inl rfl)
  have hb := OrdinalRestriction.member a.castSucc.castSucc (Fin.last m).castSucc haW (.conjL hW)
  have hv := HierarchyMembership.layer_membership hAW hsepW hpW (Fin.last m).castSucc (Fin.last (m+1)) hdW hb (.conjL (.conjR hW))
  have hs := OrdinalTransitivity.subset_of_member a.castSucc.castSucc (Fin.last m).castSucc (.conjL haW) (.conjL hW)
  have hmon := monotone a.castSucc.castSucc (Fin.last m).castSucc u.castSucc.castSucc (Fin.last (m+1)) hs huW hv
  simpa only [Formula.raise, subset_rename] using OrdinalTransitivity.subset_trans z.castSucc.castSucc (Fin.last (m+1)) u.castSucc.castSucc
    (.conjR (.conjR hW)) hmon

theorem transitive {m} {Γ : Context m} (hA : OrdinalRecursionContext.Evidence Γ)
    (hsep : Derives Γ ((Source.SetLanguage.separation RestrictionSyntax.matrix).rename Fin.elim0))
    (hp : Derives Γ (Source.SetLanguage.powerSet.rename Fin.elim0)) (a u : Fin m)
    (hd : Derives Γ (OrdinalRecursionDeterminism.deterministic PowerUnionSyntax.matrix Fin.elim0))
    (ha : Derives Γ (ordinal a)) (hu : Derives Γ (membership a u)) : Derives Γ (transitiveSet u) := by
  apply OrdinalTransitivity.from_canonical u
  apply Derives.allI
  let Δ := Context.image Formula.raise Γ
  have hA' := OrdinalRecursionContext.rename hA Fin.castSucc
  have hsep' : Derives Δ ((Source.SetLanguage.separation RestrictionSyntax.matrix).rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc hsep
  have hp' : Derives Δ (Source.SetLanguage.powerSet.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc hp
  have hd' : Derives Δ (OrdinalRecursionDeterminism.deterministic PowerUnionSyntax.matrix Fin.elim0) := by
    simpa only [Formula.raise, OrdinalRecursionDeterminism.deterministic_rename, empty_parameters] using Derives.rename Fin.castSucc hd
  have ha' : Derives Δ (ordinal a.castSucc) := by
    simpa only [Formula.raise, ordinal_rename] using Derives.rename Fin.castSucc ha
  have hu' : Derives Δ (membership a.castSucc u.castSucc) := by
    simpa only [Formula.raise, membership_rename] using Derives.rename Fin.castSucc hu
  apply Derives.impI
  exact element_subset (OrdinalRecursionContext.add hA' _) (add hsep' _) (add hp' _) a.castSucc u.castSucc (Fin.last m)
    (add hd' _) (add ha' _) (add hu' _) (.hyp (Or.inl rfl))
end PPAC.Migration.HierarchyAlgebra
