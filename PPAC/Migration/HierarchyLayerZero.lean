import PPAC.Migration.HierarchyLayerUnique
import PPAC.Migration.PowerUnionEmpty

/-! 空原索引的实际层值确为空集，核验递归定义没有索引偏移。 -/
namespace PPAC.Migration.HierarchyLayerZero
open Source SourceAlgebra SourceLogic GraphSyntax OrdinalRecursionSyntax HierarchyLayerSyntax

theorem history_empty {m} {Γ : Context m} (f a y : Fin m)
    (hz : Derives Γ (OmegaSyntax.empty a))
    (hh : Derives Γ (history PowerUnionSyntax.matrix Fin.elim0 f a y)) : Derives Γ (OmegaSyntax.empty y) := by
  let H := (RestrictionSyntax.restrict (Fin.last m) f.castSucc a.castSucc).conj
    (operator PowerUnionSyntax.matrix (ReplacementPredicates.paramsUp (Fin.elim0 : Fin 0 → Fin m)) a.castSucc (Fin.last m) y.castSucc)
  let Ξ := Context.add H (Context.image Formula.raise Γ)
  change Derives Γ (.ex H) at hh
  apply Derives.exE (p := H) hh
  have hzH : Derives Ξ (OmegaSyntax.empty a.castSucc) := by
    simpa only [Formula.raise, OmegaSyntax.empty_rename] using under hz H
  have hH : Derives Ξ H := .hyp (Or.inl rfl)
  have hop : Derives Ξ (PowerUnionSyntax.operation a.castSucc (Fin.last m) y.castSucc) := by
    simpa only [PowerUnionSyntax.matrix_operator] using Derives.conjR hH
  simpa only [Formula.raise, OmegaSyntax.empty_rename] using PowerUnionEmpty.operation_empty a.castSucc (Fin.last m) y.castSucc hzH hop

theorem data_empty {m} {Γ : Context m} (s f a y : Fin m)
    (hz : Derives Γ (OmegaSyntax.empty a)) (hw : Derives Γ (data s f a y)) : Derives Γ (OmegaSyntax.empty y) := by
  have hx := InsertLogic.new_member s a a (.conjL hw)
  have hgraph := Derives.conjL (Derives.conjR hw)
  have hEdge := Derives.conjR (Derives.conjR hw)
  have hh := Derives.impE (Derives.impE (equations_at PowerUnionSyntax.matrix Fin.elim0 f s a y (.conjR hgraph)) hx) hEdge
  exact history_empty f a y hz hh

theorem layer_empty {m} {Γ : Context m} (a y : Fin m)
    (hz : Derives Γ (OmegaSyntax.empty a)) (hy : Derives Γ (layer a y)) : Derives Γ (OmegaSyntax.empty y) := by
  let W := witnesses a y
  let Ξ := Context.add W (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_layer a y _ hy
  have hzW : Derives Ξ (OmegaSyntax.empty a.castSucc.castSucc) := by
    simpa only [Formula.raise, OmegaSyntax.empty_rename] using OrderedPairElimination.under_two hz W
  have hW : Derives Ξ W := .hyp (Or.inl rfl)
  simpa only [Formula.raise, OmegaSyntax.empty_rename] using data_empty (Fin.last m).castSucc (Fin.last (m+1))
    a.castSucc.castSucc y.castSucc.castSucc hzW hW
end PPAC.Migration.HierarchyLayerZero
