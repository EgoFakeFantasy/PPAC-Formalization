import PPAC.Migration.Internal.SyntaxFreeShiftSyntax

/-! 原 Replacement 实际构造 i↦Succ(i) 的完整图，并证明原后继范围界。 -/
namespace PPAC.Migration.Internal.SyntaxFreeShiftGraph
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax ReplacementPredicates SyntaxRenameQuerySyntax
open SyntaxFreeShiftSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem point_fiber {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (ρ : Fin 0 → Fin m) (x : Fin m) :
    Derives Γ (fiber matrix ρ x) := by
  have he := InsertExistence.exists_insert x x (ZFContext.arithmetic hZ).base.pairing (ZFContext.arithmetic hZ).base.union
  let Y := successor (Fin.last m) x.castSucc
  let Ξ := Context.add Y (Context.image Formula.raise Γ)
  change Derives Γ (.ex Y) at he
  apply Derives.exE he
  have hY : Derives Ξ Y := .hyp (Or.inl rfl)
  have hu : Derives Ξ (unique matrix (paramsUp ρ) x.castSucc (Fin.last m)) := by
    simp only [unique, matrix_rel]
    apply Derives.allI
    apply Derives.impI
    let Z := successor (Fin.last (m+1)) x.castSucc.castSucc
    let Δ := Context.add Z (Context.image Formula.raise Ξ)
    have hy2 : Derives Δ (successor (Fin.last m).castSucc x.castSucc.castSucc) :=
      of_eq (by simp only [Y, Formula.raise, successor_rename]) (under hY Z)
    exact InsertLogic.unique _ _ _ _ (ZFContext.arithmetic (ZFContext.under (ZFContext.under hZ Y) Z)).base.extensionality
      (.hyp (Or.inl rfl)) hy2
  have ho : Derives Ξ (fiber matrix (paramsUp ρ) x.castSucc) := by
    apply Derives.exI (Fin.last m)
    simp only [Formula.instantiate, Formula.rename, rel_rename, unique_rename, paramsUp,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
    exact .conjI (of_eq (matrix_rel _ _ _).symm hY) hu
  exact of_eq (by simp only [Formula.raise, fiber_rename]) ho

theorem total {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (b : Fin m) :
    Derives Γ (ReplacementPredicates.total matrix (Fin.elim0 : Fin 0 → Fin m) b) := by
  apply Derives.allI
  apply Derives.impI
  exact point_fiber (ZFContext.under hZ _) _ _

theorem outputs {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b B : Fin m)
    (hw : Derives Γ (omega w)) (hb : Derives Γ (.mem b w)) (hB : Derives Γ (successor B b)) :
    Derives Γ (RelationGraph.outputsInto matrix (Fin.elim0 : Fin 0 → Fin m) b B) := by
  simp only [RelationGraph.outputsInto, matrix_rel]
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let A := (Formula.mem (Fin.last m).castSucc b.castSucc.castSucc).conj
    (successor (Fin.last (m+1)) (Fin.last m).castSucc)
  let Δ := Context.add A (Context.image Formula.raise (Context.image Formula.raise Γ))
  have hZ2 := ZFContext.under_two hZ A
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (OrderedPairElimination.under_two hw A)
  have hb2 : Derives Δ (.mem b.castSucc.castSucc w.castSucc.castSucc) := OrderedPairElimination.under_two hb A
  have hB2 : Derives Δ (successor B.castSucc.castSucc b.castSucc.castSucc) := of_eq (by simp only [Formula.raise, successor_rename]) (OrderedPairElimination.under_two hB A)
  have hA : Derives Δ A := .hyp (Or.inl rfl)
  have hi := StructuralListTraceOrder.member_member hZ2 _ _ _ hw2 hb2 (.conjL hA)
  exact SyntaxIndexLiftOrder.successor_member hZ2 _ _ _ _ _ hw2 hi hb2 (.conjL hA) (.conjR hA) hB2

theorem edge_iff {m} {Γ : Context m} (b r i j : Fin m) (hg : Derives Γ (graph b r)) :
    Derives Γ ((edge r i j).iff ((Formula.mem i b).conj (successor j i))) :=
  of_eq (by simp only [matrix_rel]) (RelationGraphSyntax.law_at matrix (Fin.elim0 : Fin 0 → Fin m) b r i j (.conjR hg))

theorem to_graph {m} {Γ : Context m} (w b B r : Fin m) (hm : Derives Γ (shiftMap w b B r)) :
    Derives Γ (graph b r) := .conjI (.conjL (.conjR (.conjL (.conjR hm)))) (.conjR (.conjR hm))

theorem index_map {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b B r : Fin m)
    (hw : Derives Γ (omega w)) (hb : Derives Γ (.mem b w)) (hB : Derives Γ (successor B b))
    (hg : Derives Γ (graph b r)) : Derives Γ (SyntaxIndexMapSyntax.indexMap w r b B) :=
  .conjI (.conjI hb (OmegaStructureAlgebra.successor_member w B b (ZFContext.arithmetic hZ).base.extensionality hw hb hB))
    (RelationGraph.sequence matrix (Fin.elim0 : Fin 0 → Fin m) b B r hg (outputs hZ w b B hw hb hB))

theorem from_graph {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b B r : Fin m)
    (hw : Derives Γ (omega w)) (hb : Derives Γ (.mem b w)) (hB : Derives Γ (successor B b))
    (hg : Derives Γ (graph b r)) : Derives Γ (shiftMap w b B r) :=
  .conjI hB (.conjI (index_map hZ w b B r hw hb hB hg) (.conjR hg))

theorem exists_graph {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (b : Fin m) :
    Derives Γ (.ex (graph b.castSucc (Fin.last m))) := by
  have he := RelationGraphFunction.exists_graph hZ matrix (Fin.elim0 : Fin 0 → Fin m) b (total hZ b)
  have hρ : paramsUp (Fin.elim0 : Fin 0 → Fin m) = (Fin.elim0 : Fin 0 → Fin (m+1)) := funext (fun i => Fin.elim0 i)
  exact of_eq (by simp only [RelationGraphSyntax.existsGraph, graph, hρ]) he

theorem unique_graph {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (b r s : Fin m)
    (hr : Derives Γ (graph b r)) (hs : Derives Γ (graph b s)) : Derives Γ (.equal r s) :=
  RelationGraph.unique_graph hZ matrix (Fin.elim0 : Fin 0 → Fin m) b r s hr hs

theorem unique_map {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b B r s : Fin m)
    (hr : Derives Γ (shiftMap w b B r)) (hs : Derives Γ (shiftMap w b B s)) : Derives Γ (.equal r s) :=
  unique_graph hZ b r s (to_graph w b B r hr) (to_graph w b B s hs)

theorem exists_map {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b B : Fin m)
    (hw : Derives Γ (omega w)) (hb : Derives Γ (.mem b w)) (hB : Derives Γ (successor B b)) :
    Derives Γ (existsMap w b B) := by
  let G := graph b.castSucc (Fin.last m)
  let Δ := Context.add G (Context.image Formula.raise Γ)
  apply Derives.exE (p := G) (exists_graph hZ b)
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw G)
  have hB1 : Derives Δ (successor B.castSucc b.castSucc) := of_eq (successor_rename B b Fin.castSucc) (under hB G)
  have hm := from_graph (ZFContext.under hZ G) _ _ _ _ hw1 (under hb G) hB1 (.hyp (Or.inl rfl))
  have ho : Derives Δ (existsMap w.castSucc b.castSucc B.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Formula.instantiate, shiftMap_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hm
  exact of_eq (existsMap_rename w b B Fin.castSucc).symm ho
end PPAC.Migration.Internal.SyntaxFreeShiftGraph
