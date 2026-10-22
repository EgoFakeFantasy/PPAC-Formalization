import PPAC.Migration.Internal.SyntaxIdentityMapSyntax

/-! 原Replacement实际构造全域恒等图；精确全边式、对角性及原IndexMap均在对象核中证明。 -/
namespace PPAC.Migration.Internal.SyntaxIdentityGraph
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax SyntaxRenameQuerySyntax SyntaxIdentityMapSyntax
open ReplacementPredicates RelationGraphSyntax SyntaxRenameTermIdentity
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem total {m} {Γ : Context m} (a : Fin m) : Derives Γ (ReplacementPredicates.total matrix (Fin.elim0 : Fin 0 → Fin m) a) := by
  simp only [ReplacementPredicates.total, ReplacementPredicates.fiber, ReplacementPredicates.unique, matrix_rel]
  apply Derives.allI
  apply Derives.impI
  apply Derives.exI (Fin.last m)
  simp only [Formula.instantiate, Formula.rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  apply Derives.conjI (.eqRefl _)
  apply Derives.allI
  apply Derives.impI
  exact eq_symm (.hyp (Or.inl rfl))

theorem outputs {m} {Γ : Context m} (a : Fin m) : Derives Γ (RelationGraph.outputsInto matrix (Fin.elim0 : Fin 0 → Fin m) a a) := by
  simp only [RelationGraph.outputsInto, matrix_rel]
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  have h : Derives (Context.add ((Formula.mem (Fin.last m).castSucc a.castSucc.castSucc).conj (.equal (Fin.last m).castSucc (Fin.last (m+1))))
      (Context.image Formula.raise (Context.image Formula.raise Γ)))
      ((Formula.mem (Fin.last m).castSucc a.castSucc.castSucc).conj (.equal (Fin.last m).castSucc (Fin.last (m+1)))) := .hyp (Or.inl rfl)
  exact mem_subst (.conjR h) (.conjL h)

theorem edge_iff {m} {Γ : Context m} (a r i j : Fin m) (hg : Derives Γ (graph a r)) :
    Derives Γ ((edge r i j).iff ((Formula.mem i a).conj (.equal i j))) :=
  of_eq (by simp only [matrix_rel]) (RelationGraphSyntax.law_at matrix (Fin.elim0 : Fin 0 → Fin m) a r i j (.conjR hg))

theorem diagonal {m} {Γ : Context m} (a r : Fin m) (hg : Derives Γ (graph a r)) : Derives Γ (SyntaxRenameTermIdentity.diagonal r) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let E := edge r.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
  let Δ := Context.add E (Context.image Formula.raise (Context.image Formula.raise Γ))
  have hg2 : Derives Δ (graph a.castSucc.castSucc r.castSucc.castSucc) := of_eq (by simp only [Formula.raise, graph_rename]) (SyntaxRenameBinders.under_2 hg E)
  exact .conjR (.impE (.conjL (edge_iff a.castSucc.castSucc r.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hg2)) (.hyp (Or.inl rfl)))

theorem index_map {m} {Γ : Context m} (w a r : Fin m) (ha : Derives Γ (.mem a w)) (hg : Derives Γ (graph a r)) :
    Derives Γ (SyntaxIndexMapSyntax.indexMap w r a a) :=
  .conjI (.conjI ha ha) (RelationGraph.sequence matrix (Fin.elim0 : Fin 0 → Fin m) a a r hg (outputs a))

theorem exists_graph {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (a : Fin m) :
    Derives Γ (.ex (graph a.castSucc (Fin.last m))) := by
  have he := RelationGraphFunction.exists_graph hZ matrix (Fin.elim0 : Fin 0 → Fin m) a (total a)
  have hρ : paramsUp (Fin.elim0 : Fin 0 → Fin m) = (Fin.elim0 : Fin 0 → Fin (m+1)) := funext (fun i => Fin.elim0 i)
  exact of_eq (by simp only [RelationGraphSyntax.existsGraph, graph, hρ]) he

theorem unique_graph {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (a r s : Fin m)
    (hr : Derives Γ (graph a r)) (hs : Derives Γ (graph a s)) : Derives Γ (.equal r s) :=
  RelationGraph.unique_graph hZ matrix (Fin.elim0 : Fin 0 → Fin m) a r s hr hs

theorem exists_map {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a : Fin m) (ha : Derives Γ (.mem a w)) :
    Derives Γ (existsMap w a) := by
  let G := graph a.castSucc (Fin.last m)
  let Δ := Context.add G (Context.image Formula.raise Γ)
  apply Derives.exE (p := G) (exists_graph hZ a)
  have hG : Derives Δ G := .hyp (Or.inl rfl)
  have hm := index_map w.castSucc a.castSucc (Fin.last m) (under ha G) hG
  have hd := diagonal a.castSucc (Fin.last m) hG
  have ho : Derives Δ (existsMap w.castSucc a.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [identityMap, Formula.instantiate, Formula.rename, SyntaxIndexMapSyntax.indexMap_rename, diagonal_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (Derives.conjI hm hd)
  exact of_eq (existsMap_rename w a Fin.castSucc).symm ho
end PPAC.Migration.Internal.SyntaxIdentityGraph
