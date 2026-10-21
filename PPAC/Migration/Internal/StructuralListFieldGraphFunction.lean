import PPAC.Migration.Internal.StructuralListFieldGraphEdges

/-! 字段精确像满足原完整functionOn、全边式和ω值域，包含实际域内值及全部候选单值性。 -/
namespace PPAC.Migration.Internal.StructuralListFieldGraphFunction
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax SequenceSyntax StructuralListFieldSyntax StructuralListFieldPairSyntax StructuralListFieldGraphSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem single_valued {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n l g i y z : Fin m)
    (hw : Derives Γ (omega w)) (hl : Derives Γ (.mem l w)) (hg : Derives Γ (graph w n l g))
    (hy : Derives Γ (edge g i y)) (hz : Derives Γ (edge g i z)) : Derives Γ (.equal y z) := by
  have hdy := StructuralListFieldGraphEdges.decode_edge hZ _ _ _ _ _ _ hg hy
  have hdz := StructuralListFieldGraphEdges.decode_edge hZ _ _ _ _ _ _ hg hz
  have hi := StructuralListTraceOrder.member_member hZ w i l hw hl (.conjL hdy)
  exact StructuralListFieldValues.unique hZ w n i y z hw hi (.conjR hdy) (.conjR hdz)

theorem value_from_field {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n l g i y : Fin m)
    (hw : Derives Γ (omega w)) (hl : Derives Γ (.mem l w)) (hg : Derives Γ (graph w n l g))
    (hi : Derives Γ (.mem i l)) (hy : Derives Γ (field w n i y)) : Derives Γ (valueAt g i y) := by
  have he := StructuralListFieldGraphEdges.build_edge hZ _ _ _ _ _ _ hg hi hy
  apply Derives.conjI he
  apply Derives.allI
  apply Derives.impI
  let M := edge g.castSucc i.castSucc (Fin.last m)
  let Δ := Context.add M (Context.image Formula.raise Γ)
  have hZ1 : ZFContext.Evidence Δ := ZFContext.under hZ M
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw M
  have hg1 : Derives Δ (graph w.castSucc n.castSucc l.castSucc g.castSucc) := by simpa only [Formula.raise, graph_rename] using under hg M
  have he1 : Derives Δ (edge g.castSucc i.castSucc y.castSucc) := by simpa only [Formula.raise, edge_rename] using under he M
  exact single_valued hZ1 _ _ _ _ _ _ _ hw1 (under hl M) hg1 (.hyp (Or.inl rfl)) he1

theorem value_for_input {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n l g i : Fin m)
    (hw : Derives Γ (omega w)) (hl : Derives Γ (.mem l w)) (hg : Derives Γ (graph w n l g))
    (hi : Derives Γ (.mem i l)) : Derives Γ (valueExists g i) := by
  have hiW := StructuralListTraceOrder.member_member hZ w i l hw hl hi
  have hy := StructuralListFieldValues.exists_value hZ w n i hw hiW
  let Y := (Formula.mem (Fin.last m) w.castSucc).conj (field w.castSucc n.castSucc i.castSucc (Fin.last m))
  let Δ := Context.add Y (Context.image Formula.raise Γ)
  change Derives Γ (.ex Y) at hy
  apply Derives.exE (p := Y) hy
  have hZ1 : ZFContext.Evidence Δ := ZFContext.under hZ Y
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw Y
  have hg1 : Derives Δ (graph w.castSucc n.castSucc l.castSucc g.castSucc) := by simpa only [Formula.raise, graph_rename] using under hg Y
  have hY : Derives Δ Y := .hyp (Or.inl rfl)
  have hv := value_from_field hZ1 _ _ _ _ _ _ hw1 (under hl Y) hg1 (under hi Y) (.conjR hY)
  have hout := GraphLogic.value_exists _ _ _ hv
  simpa only [Formula.raise, valueExists_rename] using hout

theorem function_on {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n l g : Fin m)
    (hw : Derives Γ (omega w)) (hl : Derives Γ (.mem l w)) (hg : Derives Γ (graph w n l g)) : Derives Γ (functionOn g l) := by
  apply Derives.conjI (StructuralListFieldGraphEntries.entries w n l g hg)
  apply Derives.allI
  apply Derives.impI
  let M := Formula.mem (Fin.last m) l.castSucc
  let Δ := Context.add M (Context.image Formula.raise Γ)
  have hZ1 : ZFContext.Evidence Δ := ZFContext.under hZ M
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw M
  have hg1 : Derives Δ (graph w.castSucc n.castSucc l.castSucc g.castSucc) := by simpa only [Formula.raise, graph_rename] using under hg M
  exact value_for_input hZ1 _ _ _ _ _ hw1 (under hl M) hg1 (.hyp (Or.inl rfl))

theorem sequence {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n l g : Fin m)
    (hw : Derives Γ (omega w)) (hl : Derives Γ (.mem l w)) (hg : Derives Γ (graph w n l g)) : Derives Γ (SequenceSyntax.sequence g l w) :=
  .conjI (function_on hZ w n l g hw hl hg) (StructuralListFieldGraphEdges.bounded hZ w n l g hw hg)

theorem complete {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n l g : Fin m)
    (hw : Derives Γ (omega w)) (hl : Derives Γ (.mem l w)) (hg : Derives Γ (graph w n l g)) : Derives Γ (fields w n l g) :=
  .conjI (sequence hZ w n l g hw hl hg) (.conjI hg (StructuralListFieldGraphEdges.full_law hZ w n l g hg))
end PPAC.Migration.Internal.StructuralListFieldGraphFunction
