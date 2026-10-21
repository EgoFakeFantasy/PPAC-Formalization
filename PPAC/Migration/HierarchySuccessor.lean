import PPAC.Migration.HierarchyAlgebra

/-! 实际后继索引的层值正是前层的原PowerOf幂集，无宿主幂集符号。 -/
namespace PPAC.Migration.HierarchySuccessor
open Source SourceAlgebra SourceLogic RestrictionSyntax OrdinalSyntax HierarchyLayerSyntax HierarchyMemberSyntax

theorem layer_subst_index {m} {Γ : Context m} (a b v : Fin m)
    (he : Derives Γ (.equal b a)) (hv : Derives Γ (layer b v)) : Derives Γ (layer a v) := by
  have hi : Derives Γ ((layer (Fin.last m) v.castSucc).instantiate b) := by
    simpa only [Formula.instantiate, layer_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hv
  have hx := Derives.eqSubst (layer (Fin.last m) v.castSucc) he hi
  simpa only [Formula.instantiate, layer_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hx

theorem subset_subst_base {m} {Γ : Context m} (z v u : Fin m)
    (he : Derives Γ (.equal v u)) (hz : Derives Γ (subset z v)) : Derives Γ (subset z u) := by
  have hi : Derives Γ ((subset z.castSucc (Fin.last m)).instantiate v) := by
    simpa only [Formula.instantiate, subset_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hz
  have hx := Derives.eqSubst (subset z.castSucc (Fin.last m)) he hi
  simpa only [Formula.instantiate, subset_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hx

theorem point_subset {m} {Γ : Context m} (hA : OrdinalRecursionContext.Evidence Γ)
    (hsep : Derives Γ ((Source.SetLanguage.separation RestrictionSyntax.matrix).rename Fin.elim0))
    (hp : Derives Γ (Source.SetLanguage.powerSet.rename Fin.elim0)) (a u s z b v : Fin m)
    (hd : Derives Γ (OrdinalRecursionDeterminism.deterministic PowerUnionSyntax.matrix Fin.elim0))
    (ha : Derives Γ (ordinal a)) (hl : Derives Γ (layer a u)) (hu : Derives Γ (membership a u))
    (hs : Derives Γ (OmegaSyntax.successor s a)) (hw : Derives Γ (layerData s z b v)) : Derives Γ (subset z u) := by
  have hc := InsertLogic.member_cases s a a b hs (.conjL hw)
  apply Derives.disjE hc
  · let B := Formula.mem b a
    have hb : Derives (Context.add B Γ) B := .hyp (Or.inl rfl)
    have hx := intro_layerMember a z b v (.conjI hb (add (.conjR hw) B))
    have hz := Derives.impE (.conjR (add (membership_at a u z hu) B)) hx
    exact HierarchyAlgebra.element_subset (OrdinalRecursionContext.add hA B) (add hsep B) (add hp B)
      a u z (add hd B) (add ha B) (add hu B) hz
  · let E := Formula.equal b a
    have he : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have hv := layer_subst_index a b v he (add (.conjL (.conjR hw)) E)
    have heq := HierarchyLayerUnique.layers_unique (OrdinalRecursionContext.add hA E) a v u
      (add hd E) (add ha E) hv (add hl E)
    exact subset_subst_base z v u heq (add (.conjR (.conjR hw)) E)

theorem member_subset {m} {Γ : Context m} (hA : OrdinalRecursionContext.Evidence Γ)
    (hsep : Derives Γ ((Source.SetLanguage.separation RestrictionSyntax.matrix).rename Fin.elim0))
    (hp : Derives Γ (Source.SetLanguage.powerSet.rename Fin.elim0)) (a u s z : Fin m)
    (hd : Derives Γ (OrdinalRecursionDeterminism.deterministic PowerUnionSyntax.matrix Fin.elim0))
    (ha : Derives Γ (ordinal a)) (hl : Derives Γ (layer a u)) (hu : Derives Γ (membership a u))
    (hs : Derives Γ (OmegaSyntax.successor s a)) (hz : Derives Γ (layerMember s z)) : Derives Γ (subset z u) := by
  let W := layerMemberWitnesses s z
  let Ξ := Context.add W (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_layerMember s z _ hz
  have hAW := OrdinalRecursionContext.under_two hA W
  have hsepW : Derives Ξ ((Source.SetLanguage.separation RestrictionSyntax.matrix).rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using OrderedPairElimination.under_two hsep W
  have hpW : Derives Ξ (Source.SetLanguage.powerSet.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using OrderedPairElimination.under_two hp W
  have hdW : Derives Ξ (OrdinalRecursionDeterminism.deterministic PowerUnionSyntax.matrix Fin.elim0) := by
    simpa only [Formula.raise, OrdinalRecursionDeterminism.deterministic_rename, empty_parameters] using OrderedPairElimination.under_two hd W
  have haW : Derives Ξ (ordinal a.castSucc.castSucc) := by
    simpa only [Formula.raise, ordinal_rename] using OrderedPairElimination.under_two ha W
  have hlW : Derives Ξ (layer a.castSucc.castSucc u.castSucc.castSucc) := by
    simpa only [Formula.raise, layer_rename] using OrderedPairElimination.under_two hl W
  have huW : Derives Ξ (membership a.castSucc.castSucc u.castSucc.castSucc) := by
    simpa only [Formula.raise, membership_rename] using OrderedPairElimination.under_two hu W
  have hsW : Derives Ξ (OmegaSyntax.successor s.castSucc.castSucc a.castSucc.castSucc) := by
    simpa only [Formula.raise, OmegaSyntax.successor_rename] using OrderedPairElimination.under_two hs W
  have hW : Derives Ξ W := .hyp (Or.inl rfl)
  simpa only [Formula.raise, subset_rename] using point_subset hAW hsepW hpW a.castSucc.castSucc u.castSucc.castSucc
    s.castSucc.castSucc z.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hdW haW hlW huW hsW hW

theorem power {m} {Γ : Context m} (hA : OrdinalRecursionContext.Evidence Γ)
    (hsep : Derives Γ ((Source.SetLanguage.separation RestrictionSyntax.matrix).rename Fin.elim0))
    (hp : Derives Γ (Source.SetLanguage.powerSet.rename Fin.elim0)) (a u s v : Fin m)
    (hd : Derives Γ (OrdinalRecursionDeterminism.deterministic PowerUnionSyntax.matrix Fin.elim0))
    (ha : Derives Γ (ordinal a)) (hl : Derives Γ (layer a u)) (hu : Derives Γ (membership a u))
    (hs : Derives Γ (OmegaSyntax.successor s a)) (hv : Derives Γ (membership s v)) : Derives Γ (PowerSetSyntax.powerOf v u) := by
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
  have hl' : Derives Δ (layer a.castSucc u.castSucc) := by
    simpa only [Formula.raise, layer_rename] using Derives.rename Fin.castSucc hl
  have hu' : Derives Δ (membership a.castSucc u.castSucc) := by
    simpa only [Formula.raise, membership_rename] using Derives.rename Fin.castSucc hu
  have hs' : Derives Δ (OmegaSyntax.successor s.castSucc a.castSucc) := by
    simpa only [Formula.raise, OmegaSyntax.successor_rename] using Derives.rename Fin.castSucc hs
  have hv' : Derives Δ (membership s.castSucc v.castSucc) := by
    simpa only [Formula.raise, membership_rename] using Derives.rename Fin.castSucc hv
  apply Derives.conjI
  · apply Derives.impI
    let M := Formula.mem (Fin.last m) v.castSucc
    have hm : Derives (Context.add M Δ) M := .hyp (Or.inl rfl)
    have hx := Derives.impE (.conjL (add (membership_at s.castSucc v.castSucc (Fin.last m) hv') M)) hm
    exact member_subset (OrdinalRecursionContext.add hA' M) (add hsep' M) (add hp' M)
      a.castSucc u.castSucc s.castSucc (Fin.last m) (add hd' M) (add ha' M) (add hl' M) (add hu' M) (add hs' M) hx
  · apply Derives.impI
    let M := subset (Fin.last m) u.castSucc
    have hm : Derives (Context.add M Δ) M := .hyp (Or.inl rfl)
    have hx := intro_layerMember s.castSucc (Fin.last m) a.castSucc u.castSucc
      (.conjI (InsertLogic.new_member s.castSucc a.castSucc a.castSucc (add hs' M)) (.conjI (add hl' M) hm))
    exact .impE (.conjR (add (membership_at s.castSucc v.castSucc (Fin.last m) hv') M)) hx
end PPAC.Migration.HierarchySuccessor
