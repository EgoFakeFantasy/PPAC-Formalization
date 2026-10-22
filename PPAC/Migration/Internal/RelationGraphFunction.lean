import PPAC.Migration.Internal.RelationGraphEdges

/-! 任意对象函数关系的精确像满足完整原functionOn；覆盖全部域内值和域外候选。 -/
namespace PPAC.Migration.Internal.RelationGraphFunction
open Source SourceAlgebra SourceLogic GraphSyntax ReplacementPredicates RelationGraphSyntax RelationGraphEdges

theorem value_from_relation {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (P : Formula (n+2)) (ρ : Fin n → Fin m)
    (d g x y : Fin m) (ht : Derives Γ (total P ρ d)) (hg : Derives Γ (pairGraph P ρ d g))
    (hx : Derives Γ (.mem x d)) (hy : Derives Γ (rel P ρ x y)) : Derives Γ (valueAt g x y) := by
  have he := build_edge hZ P ρ d g x y hg hx hy
  apply Derives.conjI he
  apply Derives.allI
  apply Derives.impI
  let E := edge g.castSucc x.castSucc (Fin.last m)
  let Δ := Context.add E (Context.image Formula.raise Γ)
  have hZ1 := ZFContext.under hZ E
  have ht1 : Derives Δ (total P (paramsUp ρ) d.castSucc) := by simpa only [Formula.raise, total_rename, paramsUp] using under ht E
  have hg1 : Derives Δ (pairGraph P (paramsUp ρ) d.castSucc g.castSucc) := by simpa only [Formula.raise, pairGraph_rename, paramsUp] using under hg E
  have hy1 : Derives Δ (rel P (paramsUp ρ) x.castSucc y.castSucc) := by simpa only [Formula.raise, rel_rename, paramsUp] using under hy E
  have hz := decode_edge hZ1 P _ _ _ _ _ hg1 (.hyp (Or.inl rfl))
  exact relation_unique P _ _ _ _ _ ht1 (under hx E) (.conjR hz) hy1

theorem value_exists {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (P : Formula (n+2)) (ρ : Fin n → Fin m)
    (d g x : Fin m) (ht : Derives Γ (total P ρ d)) (hg : Derives Γ (pairGraph P ρ d g))
    (hx : Derives Γ (.mem x d)) : Derives Γ (valueExists g x) := by
  have he := ReplacementFromCollection.fiber_value P ρ x (.impE (specialize_total P ρ d x ht) hx)
  let Y := rel P (paramsUp ρ) x.castSucc (Fin.last m)
  let Δ := Context.add Y (Context.image Formula.raise Γ)
  change Derives Γ (.ex Y) at he
  apply Derives.exE he
  have ht1 : Derives Δ (total P (paramsUp ρ) d.castSucc) := by simpa only [Formula.raise, total_rename, paramsUp] using under ht Y
  have hg1 : Derives Δ (pairGraph P (paramsUp ρ) d.castSucc g.castSucc) := by simpa only [Formula.raise, pairGraph_rename, paramsUp] using under hg Y
  have hY : Derives Δ Y := .hyp (Or.inl rfl)
  have hv := value_from_relation (ZFContext.under hZ Y) P _ _ _ _ _ ht1 hg1 (under hx Y) hY
  have ho := GraphLogic.value_exists _ _ _ hv
  simpa only [Formula.raise, valueExists_rename] using ho

theorem function_on {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (P : Formula (n+2)) (ρ : Fin n → Fin m)
    (d g : Fin m) (ht : Derives Γ (total P ρ d)) (hg : Derives Γ (pairGraph P ρ d g)) : Derives Γ (functionOn g d) := by
  apply Derives.conjI (entries P ρ d g hg)
  apply Derives.allI
  apply Derives.impI
  let M := Formula.mem (Fin.last m) d.castSucc
  let Δ := Context.add M (Context.image Formula.raise Γ)
  have ht1 : Derives Δ (total P (paramsUp ρ) d.castSucc) := by simpa only [Formula.raise, total_rename, paramsUp] using under ht M
  have hg1 : Derives Δ (pairGraph P (paramsUp ρ) d.castSucc g.castSucc) := by simpa only [Formula.raise, pairGraph_rename, paramsUp] using under hg M
  exact value_exists (ZFContext.under hZ M) P _ _ _ _ ht1 hg1 (.hyp (Or.inl rfl))

theorem complete {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (P : Formula (n+2)) (ρ : Fin n → Fin m)
    (d g : Fin m) (ht : Derives Γ (total P ρ d)) (hg : Derives Γ (pairGraph P ρ d g)) :
    Derives Γ (functionGraph P ρ d g) :=
  .conjI (function_on hZ P ρ d g ht hg) (full_law hZ P ρ d g hg)

theorem exists_graph {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (P : Formula (n+2)) (ρ : Fin n → Fin m)
    (d : Fin m) (ht : Derives Γ (total P ρ d)) : Derives Γ (existsGraph P ρ d) := by
  have he := RelationGraphPairs.exists_pair_graph hZ P ρ d ht
  let G := pairGraph P (paramsUp ρ) d.castSucc (Fin.last m)
  let Δ := Context.add G (Context.image Formula.raise Γ)
  change Derives Γ (.ex G) at he
  apply Derives.exE he
  have ht1 : Derives Δ (total P (paramsUp ρ) d.castSucc) := by simpa only [Formula.raise, total_rename, paramsUp] using under ht G
  have hG : Derives Δ G := .hyp (Or.inl rfl)
  have hc := complete (ZFContext.under hZ G) P _ _ _ ht1 hG
  have ho : Derives Δ (existsGraph P (paramsUp ρ) d.castSucc) := by
    apply Derives.exI (Fin.last m)
    simpa only [Formula.instantiate, functionGraph_rename, paramsUp, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hc
  simpa only [Formula.raise, existsGraph_rename, paramsUp] using ho
end PPAC.Migration.Internal.RelationGraphFunction
