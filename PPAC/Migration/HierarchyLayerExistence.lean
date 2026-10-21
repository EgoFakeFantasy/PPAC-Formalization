import PPAC.Migration.HierarchyLayerSyntax

/-! 已实际消去算子前提的层序列在每个内部原序数处具有实际层值。 -/
namespace PPAC.Migration.HierarchyLayerExistence
open Source SourceAlgebra SourceLogic GraphSyntax OrdinalSyntax OrdinalRecursionSyntax HierarchyLayerSyntax

theorem exists_graph {m} {Γ : Context m} (a : Fin m)
    (hh : Derives Γ (HierarchyRecursion.existenceSentence.rename Fin.elim0))
    (ha : Derives Γ (ordinal a)) : Derives Γ (graphExists a) := by
  have hAll : Derives Γ (OrdinalRecursionExistenceSyntax.holds PowerUnionSyntax.matrix Fin.elim0) := by
    simpa only [HierarchyRecursion.existenceSentence, OrdinalRecursionExistenceSyntax.holds_rename, empty_parameters] using hh
  have hx := Derives.impE (OrdinalRecursionExistenceSyntax.holds_at PowerUnionSyntax.matrix Fin.elim0 a hAll) ha
  simpa only [recursorExists, graphExists, graph, empty_parameters] using hx

theorem exists_layer {m} {Γ : Context m} (hA : OrdinalRecursionContext.Evidence Γ) (a : Fin m)
    (hh : Derives Γ (HierarchyRecursion.existenceSentence.rename Fin.elim0))
    (ha : Derives Γ (ordinal a)) : Derives Γ (layerExists a) := by
  have hex := InsertExistence.exists_insert a a hA.pairing hA.union
  let S := OmegaSyntax.successor (Fin.last m) a.castSucc
  let Γs := Context.add S (Context.image Formula.raise Γ)
  change Derives Γ (.ex S) at hex
  apply Derives.exE (p := S) hex
  have hAS := OrdinalRecursionContext.under hA S
  have hhS : Derives Γs (HierarchyRecursion.existenceSentence.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hh S
  have haS : Derives Γs (ordinal a.castSucc) := by
    simpa only [Formula.raise, ordinal_rename] using under ha S
  have hS : Derives Γs S := .hyp (Or.inl rfl)
  have hOrd := OrdinalSuccessor.ordinal (Fin.last m) a.castSucc hAS.foundation hS haS
  have hf := exists_graph (Fin.last m) hhS hOrd
  let F := graph (Fin.last (m+1)) (Fin.last m).castSucc
  let Γf := Context.add F (Context.image Formula.raise Γs)
  change Derives Γs (.ex F) at hf
  apply Derives.exE (p := F) hf
  have hSF : Derives Γf (OmegaSyntax.successor (Fin.last m).castSucc a.castSucc.castSucc) := by
    simpa only [Formula.raise, S, OmegaSyntax.successor_rename] using under hS F
  have hF : Derives Γf F := .hyp (Or.inl rfl)
  have hx := InsertLogic.new_member (Fin.last m).castSucc a.castSucc.castSucc a.castSucc.castSucc hSF
  have hy := GraphProperties.output_exists (Fin.last (m+1)) (Fin.last m).castSucc a.castSucc.castSucc (.conjL hF) hx
  let Y := edge (Fin.last (m+1)).castSucc a.castSucc.castSucc.castSucc (Fin.last (m+2))
  let Ξ := Context.add Y (Context.image Formula.raise Γf)
  change Derives Γf (.ex Y) at hy
  apply Derives.exE (p := Y) hy
  have hSY : Derives Ξ (OmegaSyntax.successor (Fin.last m).castSucc.castSucc a.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, OmegaSyntax.successor_rename] using under hSF Y
  have hFY : Derives Ξ (graph (Fin.last (m+1)).castSucc (Fin.last m).castSucc.castSucc) := by
    simpa only [Formula.raise, F, graph_rename] using under hF Y
  have hY : Derives Ξ Y := .hyp (Or.inl rfl)
  have hLayer := intro_layer (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc
    a.castSucc.castSucc.castSucc (Fin.last (m+2)) hSY hFY hY
  have hout : Derives Ξ (layerExists a.castSucc.castSucc.castSucc) := by
    apply Derives.exI (Fin.last (m+2))
    simpa only [Formula.instantiate, layer_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hLayer
  simpa only [Formula.raise, layerExists_rename] using hout
end PPAC.Migration.HierarchyLayerExistence
