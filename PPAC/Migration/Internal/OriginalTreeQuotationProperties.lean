import PPAC.Migration.Internal.OriginalTreeQuotationSyntax

/-! 原结构quotation的实际内部自然码范围及等词传输；不把外部树当内部标准性假设。 -/
namespace PPAC.Migration.Internal.OriginalTreeQuotationProperties
open Source SourceAlgebra SourceLogic OmegaSyntax OriginalTreeQuotationSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket (Tree)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem tree_range {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (input : Tree) (w n : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (tree input w n)) : Derives Γ (.mem n w) := by
  cases input with
  | node tag children =>
    let C := nodeBody tag children w n
    let Δ := Context.add C (Context.image Formula.raise (Context.image Formula.raise Γ))
    rw [tree] at hn
    apply SyntaxRenameBinders.eliminate_2 C _ hn
    have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw C)
    have hC : Derives Δ C := .hyp (Or.inl rfl)
    exact StructuralNodeProperties.range (SyntaxRenameBinders.zf_under_2 hZ C) _ _ _ _ hw2 (.conjR (.conjR hC))

theorem forest_range {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (input : List Tree) (w n : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (forest input w n)) : Derives Γ (.mem n w) := by
  cases input with
  | nil => exact StructuralNil.range hZ w n hw (of_eq (by simp only [forest]) hn)
  | cons head tail =>
    let C := consBody head tail w n
    let Δ := Context.add C (Context.image Formula.raise (Context.image Formula.raise Γ))
    rw [forest] at hn
    apply SyntaxRenameBinders.eliminate_2 C _ hn
    have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw C)
    have hC : Derives Δ C := .hyp (Or.inl rfl)
    exact StructuralConsCore.range (SyntaxRenameBinders.zf_under_2 hZ C) _ _ _ _ hw2 (.conjR (.conjR hC))

theorem raw_tag_subst {m} {Γ : Context m} (w t u p n : Fin m) (he : Derives Γ (.equal t u))
    (hn : Derives Γ (StructuralNodeSyntax.raw w t p n)) : Derives Γ (StructuralNodeSyntax.raw w u p n) := by
  have hi : Derives Γ ((StructuralNodeSyntax.raw w.castSucc (Fin.last m) p.castSucc n.castSucc).instantiate t) :=
    of_eq (by simp only [Formula.instantiate, StructuralNodeSyntax.raw_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hn
  have ho := Derives.eqSubst (StructuralNodeSyntax.raw w.castSucc (Fin.last m) p.castSucc n.castSucc) he hi
  exact of_eq (by simp only [Formula.instantiate, StructuralNodeSyntax.raw_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) ho

theorem intro_tree_exists {m} {Γ : Context m} (input : Tree) (w n : Fin m)
    (hn : Derives Γ (.mem n w)) (hq : Derives Γ (tree input w n)) : Derives Γ (treeExists input w) := by
  apply Derives.exI n
  exact of_eq (by simp only [Formula.instantiate, Formula.rename, tree_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hn hq)

theorem intro_forest_exists {m} {Γ : Context m} (input : List Tree) (w n : Fin m)
    (hn : Derives Γ (.mem n w)) (hq : Derives Γ (forest input w n)) : Derives Γ (forestExists input w) := by
  apply Derives.exI n
  exact of_eq (by simp only [Formula.instantiate, Formula.rename, forest_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hn hq)

end PPAC.Migration.Internal.OriginalTreeQuotationProperties
