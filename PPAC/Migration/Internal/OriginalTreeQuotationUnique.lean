import PPAC.Migration.Internal.OriginalTreeQuotationExistence

/-! 同一原树/森林quotation的所有内部候选码唯一；隐藏子码由对象等词对齐。 -/
namespace PPAC.Migration.Internal.OriginalTreeQuotationUnique
open Source SourceAlgebra SourceLogic OmegaSyntax OriginalTreeQuotationSyntax OriginalTreeQuotationProperties
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket (Tree)
attribute [local irreducible] NaturalRecursionSyntax.matrix

mutual
theorem tree_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (input : Tree) (w n v : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (tree input w n)) (hv : Derives Γ (tree input w v)) : Derives Γ (.equal n v) := by
  cases input with
  | node tag children =>
    let C := nodeBody tag children w n
    let Δ := Context.add C (Context.image Formula.raise (Context.image Formula.raise Γ))
    rw [tree] at hn
    apply SyntaxRenameBinders.eliminate_2 C _ hn
    have hZ2 := SyntaxRenameBinders.zf_under_2 hZ C
    have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw C)
    have hv2 : Derives Δ (tree (.node tag children) w.castSucc.castSucc v.castSucc.castSucc) := of_eq (by simp only [Formula.raise, tree_rename]) (SyntaxRenameBinders.under_2 hv C)
    let D := nodeBody tag children w.castSucc.castSucc v.castSucc.castSucc
    let Ξ := Context.add D (Context.image Formula.raise (Context.image Formula.raise Δ))
    rw [tree] at hv2
    apply SyntaxRenameBinders.eliminate_2 D _ hv2
    have hZ4 := SyntaxRenameBinders.zf_under_2 hZ2 D
    have hw4 : Derives Ξ (omega w.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw2 D)
    have hC : Derives Δ C := .hyp (Or.inl rfl)
    have hC4 : Derives Ξ (nodeState tag children w.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc) :=
      of_eq (by simp only [C, nodeBody, Formula.raise, nodeState_rename]) (SyntaxRenameBinders.under_2 hC D)
    have hD : Derives Ξ D := .hyp (Or.inl rfl)
    have ht := SyntaxNumerals.unique hZ4 tag (Fin.last (m+1)).castSucc.castSucc (Fin.last (m+3)) (.conjL hC4) (.conjL hD)
    have hp := forest_unique hZ4 children w.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc hw4 (.conjL (.conjR hC4)) (.conjL (.conjR hD))
    have htW := SyntaxNumerals.range hZ4 tag w.castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)) hw4 (.conjL hD)
    have hpW := forest_range hZ4 children w.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc hw4 (.conjL (.conjR hD))
    have hr := raw_tag_subst w.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc (Fin.last (m+3)) (Fin.last m).castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc ht (.conjR (.conjR hC4))
    have hs := StructuralTreeEncode.raw_payload_subst w.castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)) (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc n.castSucc.castSucc.castSucc.castSucc hp hr
    exact StructuralNodeCore.unique hZ4 w.castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)) (Fin.last (m+2)).castSucc n.castSucc.castSucc.castSucc.castSucc v.castSucc.castSucc.castSucc.castSucc hw4 htW hpW hs (.conjR (.conjR hD))
termination_by sizeOf input

theorem forest_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (input : List Tree) (w n v : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (forest input w n)) (hv : Derives Γ (forest input w v)) : Derives Γ (.equal n v) := by
  cases input with
  | nil => exact StructuralNil.unique hZ w n v hw (of_eq (by simp only [forest]) hn) (of_eq (by simp only [forest]) hv)
  | cons head tail =>
    let C := consBody head tail w n
    let Δ := Context.add C (Context.image Formula.raise (Context.image Formula.raise Γ))
    rw [forest] at hn
    apply SyntaxRenameBinders.eliminate_2 C _ hn
    have hZ2 := SyntaxRenameBinders.zf_under_2 hZ C
    have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw C)
    have hv2 : Derives Δ (forest (head :: tail) w.castSucc.castSucc v.castSucc.castSucc) := of_eq (by simp only [Formula.raise, forest_rename]) (SyntaxRenameBinders.under_2 hv C)
    let D := consBody head tail w.castSucc.castSucc v.castSucc.castSucc
    let Ξ := Context.add D (Context.image Formula.raise (Context.image Formula.raise Δ))
    rw [forest] at hv2
    apply SyntaxRenameBinders.eliminate_2 D _ hv2
    have hZ4 := SyntaxRenameBinders.zf_under_2 hZ2 D
    have hw4 : Derives Ξ (omega w.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw2 D)
    have hC : Derives Δ C := .hyp (Or.inl rfl)
    have hC4 : Derives Ξ (consState head tail w.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc) :=
      of_eq (by simp only [C, consBody, Formula.raise, consState_rename]) (SyntaxRenameBinders.under_2 hC D)
    have hD : Derives Ξ D := .hyp (Or.inl rfl)
    have hh := tree_unique hZ4 head w.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc hw4 (.conjL hC4) (.conjL hD)
    have ht := forest_unique hZ4 tail w.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc (Fin.last (m+3)) hw4 (.conjL (.conjR hC4)) (.conjL (.conjR hD))
    have hhW := tree_range hZ4 head w.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc hw4 (.conjL hD)
    have htW := forest_range hZ4 tail w.castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)) hw4 (.conjL (.conjR hD))
    have hr := StructuralListCodeFields.head_subst w.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+1)).castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc hh (.conjR (.conjR hC4))
    have hs := StructuralListCodeFields.tail_subst w.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+1)).castSucc.castSucc (Fin.last (m+3)) n.castSucc.castSucc.castSucc.castSucc ht hr
    exact StructuralConsUnique.unique hZ4 w.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+3)) n.castSucc.castSucc.castSucc.castSucc v.castSucc.castSucc.castSucc.castSucc hw4 hhW htW hs (.conjR (.conjR hD))
termination_by sizeOf input

end

end PPAC.Migration.Internal.OriginalTreeQuotationUnique
