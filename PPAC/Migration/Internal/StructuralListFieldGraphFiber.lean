import PPAC.Migration.Internal.StructuralListFieldGraphFunction

/-! 原Extensionality给精确字段图唯一性；原Replacement见证给实际完整图的唯一纤维。 -/
namespace PPAC.Migration.Internal.StructuralListFieldGraphFiber
open Source SourceAlgebra SourceLogic OmegaSyntax PairSyntax StructuralListFieldPairSyntax StructuralListFieldGraphSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n l g h : Fin m)
    (hg : Derives Γ (graph w n l g)) (hh : Derives Γ (graph w n l h)) : Derives Γ (.equal g h) := by
  have hsame : Derives Γ (sameMembers g h) := by
    apply Derives.allI
    let Δ := Context.image Formula.raise Γ
    have hg1 : Derives Δ (graph w.castSucc n.castSucc l.castSucc g.castSucc) := by simpa only [Formula.raise, graph_rename] using Derives.rename Fin.castSucc hg
    have hh1 : Derives Δ (graph w.castSucc n.castSucc l.castSucc h.castSucc) := by simpa only [Formula.raise, graph_rename] using Derives.rename Fin.castSucc hh
    have hgl := graph_at _ _ _ _ (Fin.last m) hg1
    have hhl := graph_at _ _ _ _ (Fin.last m) hh1
    apply Derives.conjI
    · apply Derives.impI
      exact .impE (add (.conjR hhl) _) (.impE (add (.conjL hgl) _) (.hyp (Or.inl rfl)))
    · apply Derives.impI
      exact .impE (add (.conjR hgl) _) (.impE (add (.conjL hhl) _) (.hyp (Or.inl rfl)))
  exact .impE (extensionality_instance g h (ZFContext.arithmetic hZ).base.extensionality) hsame

theorem exists_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n l : Fin m)
    (hw : Derives Γ (omega w)) (hl : Derives Γ (.mem l w)) : Derives Γ (fieldsFiber w n l) := by
  have hg := StructuralListFieldPairs.exists_graph hZ w n l hw hl
  let G := graph w.castSucc n.castSucc l.castSucc (Fin.last m)
  let Ξ := Context.add G (Context.image Formula.raise Γ)
  change Derives Γ (.ex G) at hg
  apply Derives.exE (p := G) hg
  have hZ1 : ZFContext.Evidence Ξ := ZFContext.under hZ G
  have hw1 : Derives Ξ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw G
  have hG : Derives Ξ G := .hyp (Or.inl rfl)
  have hcomplete := StructuralListFieldGraphFunction.complete hZ1 _ _ _ _ hw1 (under hl G) hG
  have hu : Derives Ξ (.all ((graph w.castSucc.castSucc n.castSucc.castSucc l.castSucc.castSucc (Fin.last (m+1))).imp
      (.equal (Fin.last (m+1)) (Fin.last m).castSucc))) := by
    apply Derives.allI
    apply Derives.impI
    let H := graph w.castSucc.castSucc n.castSucc.castSucc l.castSucc.castSucc (Fin.last (m+1))
    let Δ := Context.add H (Context.image Formula.raise Ξ)
    have hZ2 : ZFContext.Evidence Δ := ZFContext.under hZ1 H
    have hOld : Derives Δ (graph w.castSucc.castSucc n.castSucc.castSucc l.castSucc.castSucc (Fin.last m).castSucc) := by
      simpa only [G, Formula.raise, graph_rename] using under hG H
    exact unique hZ2 _ _ _ _ _ (.hyp (Or.inl rfl)) hOld
  have hout : Derives Ξ (fieldsFiber w.castSucc n.castSucc l.castSucc) := by
    apply Derives.exI (Fin.last m)
    simp only [Formula.instantiate, Formula.rename, fields_rename, graph_rename,
      Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
    exact .conjI hcomplete hu
  simpa only [Formula.raise, fieldsFiber_rename] using hout
end PPAC.Migration.Internal.StructuralListFieldGraphFiber
