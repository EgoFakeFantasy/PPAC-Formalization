import PPAC.Migration.Internal.StructuralListFieldGraphEntries

/-! 字段精确像的全边双条件和ω值域，覆盖所有内部输入和值对象。 -/
namespace PPAC.Migration.Internal.StructuralListFieldGraphEdges
open Source SourceAlgebra SourceLogic OmegaSyntax PairSyntax GraphSyntax SequenceSyntax StructuralListFieldSyntax StructuralListFieldPairSyntax StructuralListFieldGraphSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem decode_edge {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n l g i y : Fin m)
    (hg : Derives Γ (graph w n l g)) (hy : Derives Γ (edge g i y)) : Derives Γ ((Formula.mem i l).conj (field w n i y)) := by
  let P := (Formula.mem (Fin.last m) g.castSucc).conj (ordered (Fin.last m) i.castSucc y.castSucc)
  let Δ := Context.add P (Context.image Formula.raise Γ)
  apply GraphLogic.edge_elim g i y _ hy
  have hZ1 : ZFContext.Evidence Δ := ZFContext.under hZ P
  have hg1 : Derives Δ (graph w.castSucc n.castSucc l.castSucc g.castSucc) := by simpa only [Formula.raise, graph_rename] using under hg P
  have hP : Derives Δ P := .hyp (Or.inl rfl)
  have hout := StructuralListFieldGraphEntries.decode_entry hZ1 _ _ _ _ _ _ _ hg1 (.conjL hP) (.conjR hP)
  simpa only [Formula.raise, Formula.rename, field_rename] using hout

theorem build_edge {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n l g i y : Fin m)
    (hg : Derives Γ (graph w n l g)) (hi : Derives Γ (.mem i l)) (hy : Derives Γ (field w n i y)) : Derives Γ (edge g i y) := by
  have hp := OrderedPairExistence.exists_pair i y (ZFContext.arithmetic hZ).base.pairing
  let P := ordered (Fin.last m) i.castSucc y.castSucc
  let Δ := Context.add P (Context.image Formula.raise Γ)
  change Derives Γ (.ex P) at hp
  apply Derives.exE (p := P) hp
  have hg1 : Derives Δ (graph w.castSucc n.castSucc l.castSucc g.castSucc) := by simpa only [Formula.raise, graph_rename] using under hg P
  have hy1 : Derives Δ (field w.castSucc n.castSucc i.castSucc y.castSucc) := by simpa only [Formula.raise, field_rename] using under hy P
  have hP : Derives Δ P := .hyp (Or.inl rfl)
  have he := intro_entry _ _ _ _ _ hy1 hP
  have him := intro_image _ _ _ _ _ (under hi P) he
  have hmem := Derives.impE (.conjR (graph_at _ _ _ _ _ hg1)) him
  have hout := GraphLogic.edge_intro _ _ _ _ hmem hP
  simpa only [Formula.raise, edge_rename] using hout

theorem edge_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n l g i y : Fin m)
    (hg : Derives Γ (graph w n l g)) : Derives Γ ((edge g i y).iff ((Formula.mem i l).conj (field w n i y))) := by
  apply Derives.conjI
  · apply Derives.impI
    exact decode_edge (ZFContext.add hZ _) _ _ _ _ _ _ (add hg _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    have h : Derives (Context.add ((Formula.mem i l).conj (field w n i y)) Γ) ((Formula.mem i l).conj (field w n i y)) := .hyp (Or.inl rfl)
    exact build_edge (ZFContext.add hZ _) _ _ _ _ _ _ (add hg _) (.conjL h) (.conjR h)

theorem full_law {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n l g : Fin m)
    (hg : Derives Γ (graph w n l g)) : Derives Γ (edgeLaw w n l g) := by
  apply Derives.allI
  apply Derives.allI
  let Δ := Context.image Formula.raise (Context.image Formula.raise Γ)
  have hZ2 : ZFContext.Evidence Δ := ZFContext.rename (ZFContext.rename hZ Fin.castSucc) Fin.castSucc
  have hg2 : Derives Δ (graph w.castSucc.castSucc n.castSucc.castSucc l.castSucc.castSucc g.castSucc.castSucc) := by
    simpa only [Formula.raise, graph_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hg)
  exact edge_iff hZ2 _ _ _ _ _ _ hg2

theorem bounded {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n l g : Fin m)
    (hw : Derives Γ (omega w)) (hg : Derives Γ (graph w n l g)) : Derives Γ (SequenceSyntax.bounded g w) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let M := edge g.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
  let Δ := Context.add M (Context.image Formula.raise (Context.image Formula.raise Γ))
  have hZ2 : ZFContext.Evidence Δ := ZFContext.under_two hZ M
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using OrderedPairElimination.under_two hw M
  have hg2 : Derives Δ (graph w.castSucc.castSucc n.castSucc.castSucc l.castSucc.castSucc g.castSucc.castSucc) := by
    simpa only [Formula.raise, graph_rename] using OrderedPairElimination.under_two hg M
  have hd := decode_edge hZ2 _ _ _ _ _ _ hg2 (.hyp (Or.inl rfl))
  exact StructuralListFieldValues.range hZ2 _ _ _ _ hw2 (.conjR hd)
end PPAC.Migration.Internal.StructuralListFieldGraphEdges
