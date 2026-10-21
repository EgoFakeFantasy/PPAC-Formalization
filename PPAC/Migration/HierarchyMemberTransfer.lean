import PPAC.Migration.PowerUnionMembership

/-! 精确成员存在式中的历史输出与实际层值双向替换。 -/
namespace PPAC.Migration.HierarchyMemberTransfer
open Source SourceAlgebra SourceLogic GraphSyntax OrdinalSyntax HierarchyLayerSyntax HierarchyMemberSyntax

theorem forward {m} {Γ : Context m} (hA : OrdinalRecursionContext.Evidence Γ)
    (hsep : Derives Γ ((Source.SetLanguage.separation RestrictionSyntax.matrix).rename Fin.elim0))
    (a h z : Fin m) (ha : Derives Γ (ordinal a)) (hh : Derives Γ (graph h a))
    (hz : Derives Γ (graphMember a h z)) : Derives Γ (layerMember a z) := by
  let W := graphMemberWitnesses a h z
  let Ξ := Context.add W (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_graphMember a h z _ hz
  have hAW := OrdinalRecursionContext.under_two hA W
  have hsepW : Derives Ξ ((Source.SetLanguage.separation RestrictionSyntax.matrix).rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using OrderedPairElimination.under_two hsep W
  have haW : Derives Ξ (ordinal a.castSucc.castSucc) := by
    simpa only [Formula.raise, ordinal_rename] using OrderedPairElimination.under_two ha W
  have hhW : Derives Ξ (graph h.castSucc.castSucc a.castSucc.castSucc) := by
    simpa only [Formula.raise, graph_rename] using OrderedPairElimination.under_two hh W
  have hW : Derives Ξ W := .hyp (Or.inl rfl)
  have hl := HierarchyHistory.layer_of_edge hAW hsepW h.castSucc.castSucc a.castSucc.castSucc
    (Fin.last m).castSucc (Fin.last (m+1)) haW hhW (.conjL hW) (.conjL (.conjR hW))
  simpa only [Formula.raise, layerMember_rename] using intro_layerMember a.castSucc.castSucc z.castSucc.castSucc
    (Fin.last m).castSucc (Fin.last (m+1)) (.conjI (.conjL hW) (.conjI hl (.conjR (.conjR hW))))

theorem backward {m} {Γ : Context m} (hA : OrdinalRecursionContext.Evidence Γ)
    (a h z : Fin m)
    (hd : Derives Γ (OrdinalRecursionDeterminism.deterministic PowerUnionSyntax.matrix Fin.elim0))
    (ha : Derives Γ (ordinal a)) (hh : Derives Γ (graph h a))
    (hz : Derives Γ (layerMember a z)) : Derives Γ (graphMember a h z) := by
  let W := layerMemberWitnesses a z
  let Ξ := Context.add W (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_layerMember a z _ hz
  have hAW := OrdinalRecursionContext.under_two hA W
  have hdW : Derives Ξ (OrdinalRecursionDeterminism.deterministic PowerUnionSyntax.matrix Fin.elim0) := by
    simpa only [Formula.raise, OrdinalRecursionDeterminism.deterministic_rename, empty_parameters] using OrderedPairElimination.under_two hd W
  have haW : Derives Ξ (ordinal a.castSucc.castSucc) := by
    simpa only [Formula.raise, ordinal_rename] using OrderedPairElimination.under_two ha W
  have hhW : Derives Ξ (graph h.castSucc.castSucc a.castSucc.castSucc) := by
    simpa only [Formula.raise, graph_rename] using OrderedPairElimination.under_two hh W
  have hW : Derives Ξ W := .hyp (Or.inl rfl)
  have he := HierarchyHistory.edge_of_layer hAW h.castSucc.castSucc a.castSucc.castSucc
    (Fin.last m).castSucc (Fin.last (m+1)) hdW haW hhW (.conjL hW) (.conjL (.conjR hW))
  simpa only [Formula.raise, graphMember_rename] using intro_graphMember a.castSucc.castSucc h.castSucc.castSucc z.castSucc.castSucc
    (Fin.last m).castSucc (Fin.last (m+1)) (.conjI (.conjL hW) (.conjI he (.conjR (.conjR hW))))
end PPAC.Migration.HierarchyMemberTransfer
