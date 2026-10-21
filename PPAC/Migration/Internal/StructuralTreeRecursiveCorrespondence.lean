import PPAC.Migration.Internal.StructuralTreeRecursiveSyntax

/-! 严格较小字段界及任意前段图求值对应，将局部Good精确转为真实递归子树条件。 -/
namespace PPAC.Migration.Internal.StructuralTreeRecursiveCorrespondence
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax OrdinalSyntax StructuralTreeEvaluationSyntax StructuralTreeRecursiveSyntax
open StructuralTreeOperatorSyntax (children children_at children_rename shape shape_rename good goodBody good_rename)
open StructuralListLengthSyntax (under_four zf_under_four)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem values_of_children {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z e n f h : Fin m)
    (hn : Derives Γ (ordinal n)) (hh : Derives Γ (graph w z e h n)) (hc : Derives Γ (children e n f h)) :
    Derives Γ (acceptedChildren w z e f) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let E := edge f.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
  let Δ := Context.add E (Context.image Formula.raise (Context.image Formula.raise Γ))
  have hZ2 : ZFContext.Evidence Δ := ZFContext.add (ZFContext.rename (ZFContext.rename hZ Fin.castSucc) Fin.castSucc) E
  have lift {p : Formula m} (hp : Derives Γ p) : Derives Δ p.raise.raise := add (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hp)) E
  have hn2 : Derives Δ (ordinal n.castSucc.castSucc) := by simpa only [Formula.raise, ordinal_rename] using lift hn
  have hh2 : Derives Δ (graph w.castSucc.castSucc z.castSucc.castSucc e.castSucc.castSucc h.castSucc.castSucc n.castSucc.castSucc) := by simpa only [Formula.raise, graph_rename] using lift hh
  have hc2 : Derives Δ (children e.castSucc.castSucc n.castSucc.castSucc f.castSucc.castSucc h.castSucc.castSucc) := by simpa only [Formula.raise, children_rename] using lift hc
  have hp := children_at _ _ _ _ _ _ hc2 (.hyp (Or.inl rfl))
  exact StructuralTreeGraphValues.value_of_edge hZ2 _ _ _ _ _ _ _ hn2 (.conjL hp) hh2 (.conjR hp)

theorem children_of_values {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z e n tag p l f h : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (ordinal n)) (hs : Derives Γ (shape w n tag p l f))
    (hh : Derives Γ (graph w z e h n)) (ha : Derives Γ (acceptedChildren w z e f)) : Derives Γ (children e n f h) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let E := edge f.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
  let Δ := Context.add E (Context.image Formula.raise (Context.image Formula.raise Γ))
  have hZ2 : ZFContext.Evidence Δ := ZFContext.add (ZFContext.rename (ZFContext.rename hZ Fin.castSucc) Fin.castSucc) E
  have lift {q : Formula m} (hq : Derives Γ q) : Derives Δ q.raise.raise := add (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hq)) E
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using lift hw
  have hn2 : Derives Δ (ordinal n.castSucc.castSucc) := by simpa only [Formula.raise, ordinal_rename] using lift hn
  have hs2 : Derives Δ (shape w.castSucc.castSucc n.castSucc.castSucc tag.castSucc.castSucc p.castSucc.castSucc l.castSucc.castSucc f.castSucc.castSucc) := by simpa only [Formula.raise, shape_rename] using lift hs
  have hh2 : Derives Δ (graph w.castSucc.castSucc z.castSucc.castSucc e.castSucc.castSucc h.castSucc.castSucc n.castSucc.castSucc) := by simpa only [Formula.raise, graph_rename] using lift hh
  have ha2 : Derives Δ (acceptedChildren w.castSucc.castSucc z.castSucc.castSucc e.castSucc.castSucc f.castSucc.castSucc) := by simpa only [Formula.raise, acceptedChildren_rename] using lift ha
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hb := StructuralTreeOperatorLogic.shape_edge_bound hZ2 _ _ _ _ _ _ _ _ hw2 hs2 hE
  have hv := accepted_at _ _ _ _ _ _ ha2 hE
  exact .conjI hb (StructuralTreeGraphValues.edge_of_value hZ2 _ _ _ _ _ _ _ hn2 hb hh2 hv)

theorem branch_of_good {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z e n h : Fin m)
    (hn : Derives Γ (ordinal n)) (hh : Derives Γ (graph w z e h n)) (hg : Derives Γ (good w e n h)) : Derives Γ (branch w z e n) := by
  let B := goodBody w e n h
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ))))
  apply StructuralTreeOperatorSyntax.eliminate_good w e n h _ hg
  have hZ4 : ZFContext.Evidence Δ := zf_under_four hZ B
  have hn4 : Derives Δ (ordinal n.castSucc.castSucc.castSucc.castSucc) := by simpa only [Formula.raise, ordinal_rename] using under_four hn B
  have hh4 : Derives Δ (graph w.castSucc.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc.castSucc e.castSucc.castSucc.castSucc.castSucc h.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc) := by simpa only [Formula.raise, graph_rename] using under_four hh B
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ha := values_of_children hZ4 _ _ _ _ _ _ hn4 hh4 (.conjR hB)
  have hout := intro_branch _ _ _ _ _ _ _ _ (.conjL hB) ha
  simpa only [Formula.raise, branch_rename] using hout

theorem good_of_branch {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z e n h : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (ordinal n)) (hh : Derives Γ (graph w z e h n))
    (hb : Derives Γ (branch w z e n)) : Derives Γ (good w e n h) := by
  let B := branchBody w z e n
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ))))
  apply eliminate_branch w z e n _ hb
  have hZ4 : ZFContext.Evidence Δ := zf_under_four hZ B
  have hw4 : Derives Δ (omega w.castSucc.castSucc.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using under_four hw B
  have hn4 : Derives Δ (ordinal n.castSucc.castSucc.castSucc.castSucc) := by simpa only [Formula.raise, ordinal_rename] using under_four hn B
  have hh4 : Derives Δ (graph w.castSucc.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc.castSucc e.castSucc.castSucc.castSucc.castSucc h.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc) := by simpa only [Formula.raise, graph_rename] using under_four hh B
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hc := children_of_values hZ4 _ _ _ _ _ _ _ _ _ hw4 hn4 (.conjL hB) hh4 (.conjR hB)
  have hout := StructuralTreeOperatorSyntax.intro_good _ _ _ _ _ _ _ _ (.conjL hB) hc
  simpa only [Formula.raise, good_rename] using hout

theorem good_iff_branch {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z e n h : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (ordinal n)) (hh : Derives Γ (graph w z e h n)) :
    Derives Γ ((good w e n h).iff (branch w z e n)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact branch_of_good (ZFContext.add hZ _) _ _ _ _ _ (add hn _) (add hh _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact good_of_branch (ZFContext.add hZ _) _ _ _ _ _ (add hw _) (add hn _) (add hh _) (.hyp (Or.inl rfl))
end PPAC.Migration.Internal.StructuralTreeRecursiveCorrespondence
