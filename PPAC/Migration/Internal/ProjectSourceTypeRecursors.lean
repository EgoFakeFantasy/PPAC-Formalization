import PPAC.Migration.Internal.ProjectSourceTypeRecursionStep

/-! 具体上下文集合值算子的原递归图实际存在唯一，连同实际三层载体；不依赖宿主递归。 -/
namespace PPAC.Migration.Internal.ProjectSourceTypeRecursors
open Source SourceAlgebra SourceLogic SyntaxAtomSyntax ProjectSourceTypeRecursionSyntax SyntaxContextCarrierSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem all_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w c : Fin m) : Derives Γ (recursors w c) := by
  have hc := ZFContext.closed hZ (ObjectTransfiniteRecursion.source_uniqueness matrix)
  have hi := specialize_close
    ((OrdinalRecursionTotal.total matrix (id : Fin 2 → Fin 2)).imp
      ((OrdinalRecursionDeterminism.deterministic matrix id).imp (OrdinalRecursionExistenceSyntax.allUnique matrix id)))
    (two w c) hc
  have hh : Derives Γ ((OrdinalRecursionTotal.total matrix (two w c)).imp
      ((OrdinalRecursionDeterminism.deterministic matrix (two w c)).imp (recursors w c))) := by
    simpa only [Formula.rename, OrdinalRecursionTotal.total_rename, OrdinalRecursionDeterminism.deterministic_rename,
      OrdinalRecursionExistenceSyntax.allUnique_rename, id_eq, recursors] using hi
  exact .impE (.impE hh (ProjectSourceTypeRecursionStep.total hZ (two w c))) (ProjectSourceTypeRecursionStep.deterministic hZ (two w c))

theorem at_ordinal {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w c d : Fin m)
    (hd : Derives Γ (OrdinalSyntax.ordinal d)) : Derives Γ (OrdinalRecursionExistenceSyntax.fiber matrix (two w c) d) := by
  have hh : Derives Γ ((OrdinalSyntax.ordinal d).imp (OrdinalRecursionExistenceSyntax.fiber matrix (two w c) d)) := by
    simpa only [recursors, OrdinalRecursionExistenceSyntax.allUnique, Formula.instantiate, Formula.rename,
      OrdinalSyntax.ordinal_rename, OrdinalRecursionExistenceSyntax.fiber_rename, ReplacementPredicates.paramsUp,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.allE d (all_unique hZ w c)
  exact .impE hh hd

theorem exists_graph {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w c d : Fin m)
    (hd : Derives Γ (OrdinalSyntax.ordinal d)) : Derives Γ (graphExists w c d) := by
  have hf := at_ordinal hZ w c d hd
  let F := (graph w.castSucc c.castSucc (Fin.last m) d.castSucc).conj
    (OrdinalRecursionExistenceSyntax.uniqueAt matrix (two w.castSucc c.castSucc) d.castSucc (Fin.last m))
  let Δ := Context.add F (Context.image Formula.raise Γ)
  have hρ : ReplacementPredicates.paramsUp (two w c) = two w.castSucc c.castSucc := two_map w c Fin.castSucc
  have he : Derives Γ (.ex F) := by simpa only [F, OrdinalRecursionExistenceSyntax.fiber, graph, hρ] using hf
  apply Derives.exE (p := F) he
  have hF : Derives Δ F := .hyp (Or.inl rfl)
  have hout : Derives Δ (graphExists w.castSucc c.castSucc d.castSucc) := by
    apply Derives.exI (Fin.last m)
    simpa only [Formula.instantiate, graph_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.conjL hF
  simpa only [Formula.raise, graphExists_rename] using hout

theorem actual_carrier_recursors {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) : Derives Γ (actualRecursors w) := by
  have he := SyntaxContextCarrier.exists_tower hZ w
  let T := tower w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2))
  let Δ := Context.add T (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ)))
  apply Derives.exE he
  apply Derives.exE (.hyp (Or.inl rfl))
  apply Derives.exE (.hyp (Or.inl rfl))
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have hr := all_unique (SyntaxAtomLogic.zf_under_three hZ T) w.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc
  have hout : Derives Δ (actualRecursors w.castSucc.castSucc.castSucc) := by
    apply Derives.exI (Fin.last m).castSucc.castSucc
    apply Derives.exI (Fin.last (m+1)).castSucc
    apply Derives.exI (Fin.last (m+2))
    simp only [actualBody, Formula.instantiate, Formula.rename, tower_rename, recursors_rename,
      Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
    exact .conjI hT hr
  have hh : Derives Δ (actualRecursors w).raise.raise.raise := by
    simpa only [Formula.raise, actualRecursors_rename] using hout
  refine Derives.weaken ?_ hh
  rintro q (hq | ⟨s, ⟨t, ht, h1⟩, h2⟩)
  · exact Or.inl hq
  · exact Or.inr ⟨s, Or.inr ⟨t, Or.inr ht, h1⟩, h2⟩
end PPAC.Migration.Internal.ProjectSourceTypeRecursors
