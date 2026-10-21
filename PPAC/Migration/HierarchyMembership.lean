import PPAC.Migration.HierarchyMemberTransfer

/-! 每个内部原序数的实际层值满足完整的成员递归方程。 -/
namespace PPAC.Migration.HierarchyMembership
open Source SourceAlgebra SourceLogic GraphSyntax RestrictionSyntax OrdinalSyntax
open OrdinalRecursionSyntax HierarchyLayerSyntax HierarchyMemberSyntax

theorem operator_membership {m} {Γ : Context m} (hA : OrdinalRecursionContext.Evidence Γ)
    (hsep : Derives Γ ((Source.SetLanguage.separation RestrictionSyntax.matrix).rename Fin.elim0))
    (hp : Derives Γ (Source.SetLanguage.powerSet.rename Fin.elim0))
    (a h y : Fin m)
    (hd : Derives Γ (OrdinalRecursionDeterminism.deterministic PowerUnionSyntax.matrix Fin.elim0))
    (ha : Derives Γ (ordinal a)) (hh : Derives Γ (graph h a))
    (hop : Derives Γ (PowerUnionSyntax.operation a h y)) : Derives Γ (membership a y) := by
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
  have hh' : Derives Δ (graph h.castSucc a.castSucc) := by
    simpa only [Formula.raise, graph_rename] using Derives.rename Fin.castSucc hh
  have hop' : Derives Δ (PowerUnionSyntax.operation a.castSucc h.castSucc y.castSucc) := by
    simpa only [Formula.raise, PowerUnionSyntax.operation_rename] using Derives.rename Fin.castSucc hop
  apply Derives.conjI
  · apply Derives.impI
    let M := Formula.mem (Fin.last m) y.castSucc
    have hm : Derives (Context.add M Δ) M := .hyp (Or.inl rfl)
    have hx := PowerUnionMembership.operation_forward a.castSucc h.castSucc y.castSucc (Fin.last m) (add hop' M) hm
    exact HierarchyMemberTransfer.forward (OrdinalRecursionContext.add hA' M) (add hsep' M)
      a.castSucc h.castSucc (Fin.last m) (add ha' M) (add hh' M) hx
  · apply Derives.impI
    let M := layerMember a.castSucc (Fin.last m)
    have hm : Derives (Context.add M Δ) M := .hyp (Or.inl rfl)
    have hx := HierarchyMemberTransfer.backward (OrdinalRecursionContext.add hA' M)
      a.castSucc h.castSucc (Fin.last m) (add hd' M) (add ha' M) (add hh' M) hm
    exact PowerUnionMembership.operation_backward a.castSucc h.castSucc y.castSucc (Fin.last m) (add hp' M) (add hop' M) hx

theorem history_membership {m} {Γ : Context m} (hA : OrdinalRecursionContext.Evidence Γ)
    (hsep : Derives Γ ((Source.SetLanguage.separation RestrictionSyntax.matrix).rename Fin.elim0))
    (hp : Derives Γ (Source.SetLanguage.powerSet.rename Fin.elim0))
    (s f a y : Fin m)
    (hd : Derives Γ (OrdinalRecursionDeterminism.deterministic PowerUnionSyntax.matrix Fin.elim0))
    (ha : Derives Γ (ordinal a)) (hf : Derives Γ (graph f s)) (hs : Derives Γ (subset a s))
    (hh : Derives Γ (history PowerUnionSyntax.matrix Fin.elim0 f a y)) : Derives Γ (membership a y) := by
  let H := (restrict (Fin.last m) f.castSucc a.castSucc).conj
    (operator PowerUnionSyntax.matrix (ReplacementPredicates.paramsUp (Fin.elim0 : Fin 0 → Fin m)) a.castSucc (Fin.last m) y.castSucc)
  let Ξ := Context.add H (Context.image Formula.raise Γ)
  change Derives Γ (.ex H) at hh
  apply Derives.exE (p := H) hh
  have hAH := OrdinalRecursionContext.under hA H
  have hsepH : Derives Ξ ((Source.SetLanguage.separation RestrictionSyntax.matrix).rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hsep H
  have hpH : Derives Ξ (Source.SetLanguage.powerSet.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hp H
  have hdH : Derives Ξ (OrdinalRecursionDeterminism.deterministic PowerUnionSyntax.matrix Fin.elim0) := by
    simpa only [Formula.raise, OrdinalRecursionDeterminism.deterministic_rename, empty_parameters] using under hd H
  have haH : Derives Ξ (ordinal a.castSucc) := by
    simpa only [Formula.raise, ordinal_rename] using under ha H
  have hfH : Derives Ξ (graph f.castSucc s.castSucc) := by
    simpa only [Formula.raise, graph_rename] using under hf H
  have hsH : Derives Ξ (subset a.castSucc s.castSucc) := by
    simpa only [Formula.raise, subset_rename] using under hs H
  have hH : Derives Ξ H := .hyp (Or.inl rfl)
  have hg := OrdinalRecursionRestriction.recursor_restrict PowerUnionSyntax.matrix Fin.elim0 (Fin.last m)
    f.castSucc a.castSucc s.castSucc (.conjL haH) hsH (.conjL hH) hfH
  have hop : Derives Ξ (PowerUnionSyntax.operation a.castSucc (Fin.last m) y.castSucc) := by
    simpa only [PowerUnionSyntax.matrix_operator] using Derives.conjR hH
  simpa only [Formula.raise, membership_rename] using operator_membership hAH hsepH hpH a.castSucc (Fin.last m) y.castSucc hdH haH hg hop

theorem data_membership {m} {Γ : Context m} (hA : OrdinalRecursionContext.Evidence Γ)
    (hsep : Derives Γ ((Source.SetLanguage.separation RestrictionSyntax.matrix).rename Fin.elim0))
    (hp : Derives Γ (Source.SetLanguage.powerSet.rename Fin.elim0)) (s f a y : Fin m)
    (hd : Derives Γ (OrdinalRecursionDeterminism.deterministic PowerUnionSyntax.matrix Fin.elim0))
    (ha : Derives Γ (ordinal a)) (hw : Derives Γ (data s f a y)) : Derives Γ (membership a y) := by
  have hx := InsertLogic.new_member s a a (.conjL hw)
  have hOrdS := OrdinalSuccessor.ordinal s a hA.foundation (.conjL hw) ha
  have hs := OrdinalTransitivity.subset_of_member s a (.conjL hOrdS) hx
  have hg := Derives.conjL (Derives.conjR hw)
  have hy := Derives.conjR (Derives.conjR hw)
  have hh := Derives.impE (Derives.impE (equations_at PowerUnionSyntax.matrix Fin.elim0 f s a y (.conjR hg)) hx) hy
  exact history_membership hA hsep hp s f a y hd ha hg hs hh

theorem layer_membership {m} {Γ : Context m} (hA : OrdinalRecursionContext.Evidence Γ)
    (hsep : Derives Γ ((Source.SetLanguage.separation RestrictionSyntax.matrix).rename Fin.elim0))
    (hp : Derives Γ (Source.SetLanguage.powerSet.rename Fin.elim0)) (a y : Fin m)
    (hd : Derives Γ (OrdinalRecursionDeterminism.deterministic PowerUnionSyntax.matrix Fin.elim0))
    (ha : Derives Γ (ordinal a)) (hy : Derives Γ (layer a y)) : Derives Γ (membership a y) := by
  let W := witnesses a y
  let Ξ := Context.add W (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_layer a y _ hy
  have hAW := OrdinalRecursionContext.under_two hA W
  have hsepW : Derives Ξ ((Source.SetLanguage.separation RestrictionSyntax.matrix).rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using OrderedPairElimination.under_two hsep W
  have hpW : Derives Ξ (Source.SetLanguage.powerSet.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using OrderedPairElimination.under_two hp W
  have hdW : Derives Ξ (OrdinalRecursionDeterminism.deterministic PowerUnionSyntax.matrix Fin.elim0) := by
    simpa only [Formula.raise, OrdinalRecursionDeterminism.deterministic_rename, empty_parameters] using OrderedPairElimination.under_two hd W
  have haW : Derives Ξ (ordinal a.castSucc.castSucc) := by
    simpa only [Formula.raise, ordinal_rename] using OrderedPairElimination.under_two ha W
  have hW : Derives Ξ W := .hyp (Or.inl rfl)
  simpa only [Formula.raise, membership_rename] using data_membership hAW hsepW hpW
    (Fin.last m).castSucc (Fin.last (m+1)) a.castSucc.castSucc y.castSucc.castSucc hdW haW hW
end PPAC.Migration.HierarchyMembership
