import PPAC.Migration.HierarchyLayerUnique

/-! 任意内部原序数递归图的早期输出，恰好是相应索引的实际层值。 -/
namespace PPAC.Migration.HierarchyHistory
open Source SourceAlgebra SourceLogic GraphSyntax RestrictionSyntax OrdinalSyntax
open OrdinalRecursionSyntax HierarchyLayerSyntax

theorem layer_of_edge {m} {Γ : Context m} (hA : OrdinalRecursionContext.Evidence Γ)
    (hsep : Derives Γ ((Source.SetLanguage.separation RestrictionSyntax.matrix).rename Fin.elim0))
    (h a b v : Fin m) (ha : Derives Γ (ordinal a)) (hh : Derives Γ (graph h a))
    (hb : Derives Γ (.mem b a)) (hv : Derives Γ (edge h b v)) : Derives Γ (layer b v) := by
  have hs := InsertExistence.exists_insert b b hA.pairing hA.union
  let S := OmegaSyntax.successor (Fin.last m) b.castSucc
  let Γs := Context.add S (Context.image Formula.raise Γ)
  change Derives Γ (.ex S) at hs
  apply Derives.exE (p := S) hs
  have hAS := OrdinalRecursionContext.under hA S
  have hsepS : Derives Γs ((Source.SetLanguage.separation RestrictionSyntax.matrix).rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hsep S
  have haS : Derives Γs (ordinal a.castSucc) := by
    simpa only [Formula.raise, ordinal_rename] using under ha S
  have hhS : Derives Γs (graph h.castSucc a.castSucc) := by
    simpa only [Formula.raise, graph_rename] using under hh S
  have hbS : Derives Γs (.mem b.castSucc a.castSucc) := under hb S
  have hvS : Derives Γs (edge h.castSucc b.castSucc v.castSucc) := by
    simpa only [Formula.raise, edge_rename] using under hv S
  have hS : Derives Γs S := .hyp (Or.inl rfl)
  have hOrdB := OrdinalRestriction.member a.castSucc b.castSucc haS hbS
  have hOrdS := OrdinalSuccessor.ordinal (Fin.last m) b.castSucc hAS.foundation hS hOrdB
  have hsub := OmegaElementary.successor_subset (Fin.last m) b.castSucc a.castSucc hS hbS
    (OrdinalTransitivity.subset_of_member a.castSucc b.castSucc (.conjL haS) hbS)
  have hg := OrdinalRecursionRestriction.exists_restricted PowerUnionSyntax.matrix Fin.elim0
    h.castSucc (Fin.last m) a.castSucc hsepS (.conjL hOrdS) hsub hhS
  let G := (restrict (Fin.last (m+1)) h.castSucc.castSucc (Fin.last m).castSucc).conj
    (graph (Fin.last (m+1)) (Fin.last m).castSucc)
  let Ξ := Context.add G (Context.image Formula.raise Γs)
  change Derives Γs (.ex G) at hg
  apply Derives.exE (p := G) hg
  have hSG : Derives Ξ (OmegaSyntax.successor (Fin.last m).castSucc b.castSucc.castSucc) := by
    simpa only [Formula.raise, S, OmegaSyntax.successor_rename] using under hS G
  have hvG : Derives Ξ (edge h.castSucc.castSucc b.castSucc.castSucc v.castSucc.castSucc) := by
    simpa only [Formula.raise, edge_rename] using under hvS G
  have hG : Derives Ξ G := .hyp (Or.inl rfl)
  have he := RestrictionEdges.restricted_edge (Fin.last (m+1)) h.castSucc.castSucc (Fin.last m).castSucc
    b.castSucc.castSucc v.castSucc.castSucc (.conjL hG) hvG
    (InsertLogic.new_member (Fin.last m).castSucc b.castSucc.castSucc b.castSucc.castSucc hSG)
  simpa only [Formula.raise, layer_rename] using intro_layer (Fin.last m).castSucc (Fin.last (m+1))
    b.castSucc.castSucc v.castSucc.castSucc hSG (.conjR hG) he

theorem edge_of_data {m} {Γ : Context m} (hA : OrdinalRecursionContext.Evidence Γ)
    (h a b v s f : Fin m)
    (hd : Derives Γ (OrdinalRecursionDeterminism.deterministic PowerUnionSyntax.matrix Fin.elim0))
    (ha : Derives Γ (ordinal a)) (hh : Derives Γ (graph h a))
    (hb : Derives Γ (.mem b a)) (hv : Derives Γ (data s f b v)) : Derives Γ (edge h b v) := by
  have hOrdB := OrdinalRestriction.member a b ha hb
  have hOrdS := OrdinalSuccessor.ordinal s b hA.foundation (.conjL hv) hOrdB
  have hsub := OmegaElementary.successor_subset s b a (.conjL hv) hb
    (OrdinalTransitivity.subset_of_member a b (.conjL ha) hb)
  have hcomp := OrdinalRecursionCompatibility.compatible PowerUnionSyntax.matrix Fin.elim0 f h s a
    hA.extensionality hA.foundation hA.agreementSeparation hd hOrdS ha (.conjL (.conjR hv)) hh
  exact GraphPointwise.transfer_edge f h s a b v hA.extensionality
    (.conjL (.conjL (.conjR hv))) (.conjL hh) hsub hcomp (.conjR (.conjR hv))

theorem edge_of_layer {m} {Γ : Context m} (hA : OrdinalRecursionContext.Evidence Γ)
    (h a b v : Fin m)
    (hd : Derives Γ (OrdinalRecursionDeterminism.deterministic PowerUnionSyntax.matrix Fin.elim0))
    (ha : Derives Γ (ordinal a)) (hh : Derives Γ (graph h a))
    (hb : Derives Γ (.mem b a)) (hv : Derives Γ (layer b v)) : Derives Γ (edge h b v) := by
  let W := witnesses b v
  let Ξ := Context.add W (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_layer b v _ hv
  have hAW := OrdinalRecursionContext.under_two hA W
  have hdW : Derives Ξ (OrdinalRecursionDeterminism.deterministic PowerUnionSyntax.matrix Fin.elim0) := by
    simpa only [Formula.raise, OrdinalRecursionDeterminism.deterministic_rename, empty_parameters] using OrderedPairElimination.under_two hd W
  have haW : Derives Ξ (ordinal a.castSucc.castSucc) := by
    simpa only [Formula.raise, ordinal_rename] using OrderedPairElimination.under_two ha W
  have hhW : Derives Ξ (graph h.castSucc.castSucc a.castSucc.castSucc) := by
    simpa only [Formula.raise, graph_rename] using OrderedPairElimination.under_two hh W
  have hbW : Derives Ξ (.mem b.castSucc.castSucc a.castSucc.castSucc) := OrderedPairElimination.under_two hb W
  have hW : Derives Ξ W := .hyp (Or.inl rfl)
  simpa only [Formula.raise, edge_rename] using edge_of_data hAW h.castSucc.castSucc a.castSucc.castSucc
    b.castSucc.castSucc v.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hdW haW hhW hbW hW

theorem edge_iff_layer {m} {Γ : Context m} (hA : OrdinalRecursionContext.Evidence Γ)
    (hsep : Derives Γ ((Source.SetLanguage.separation RestrictionSyntax.matrix).rename Fin.elim0))
    (h a b v : Fin m)
    (hd : Derives Γ (OrdinalRecursionDeterminism.deterministic PowerUnionSyntax.matrix Fin.elim0))
    (ha : Derives Γ (ordinal a)) (hh : Derives Γ (graph h a)) (hb : Derives Γ (.mem b a)) :
    Derives Γ ((edge h b v).iff (layer b v)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact layer_of_edge (OrdinalRecursionContext.add hA _) (add hsep _) h a b v
      (add ha _) (add hh _) (add hb _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact edge_of_layer (OrdinalRecursionContext.add hA _) h a b v (add hd _)
      (add ha _) (add hh _) (add hb _) (.hyp (Or.inl rfl))
end PPAC.Migration.HierarchyHistory
