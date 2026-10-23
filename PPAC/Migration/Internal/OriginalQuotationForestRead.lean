import PPAC.Migration.Internal.OriginalQuotationValue

/-! 实际原quotation森林的每个合法模式位置精确读取子树quotation；所有候选码为内部对象。 -/
namespace PPAC.Migration.Internal.OriginalQuotationForestRead
open Source SourceAlgebra SourceLogic OmegaSyntax OriginalTreeQuotationSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket (Tree)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem field_at {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (children : List Tree) (w n : Fin m)
    (j : Fin children.length) (i q : Fin m) (hw : Derives Γ (omega w)) (hn : Derives Γ (forest children w n))
    (hi : Derives Γ (SyntaxNumeralSyntax.numeral j.val i)) :
    Derives Γ ((StructuralListFieldSyntax.field w n i q).iff (tree (children.get j) w q)) := by
  induction children generalizing m with
  | nil => exact Fin.elim0 j
  | cons head tail ih =>
    revert hi
    refine Fin.cases ?_ (fun j => ?_) j
    · intro hi
      let C := consBody head tail w n
      let Δ := Context.add C (Context.image Formula.raise (Context.image Formula.raise Γ))
      rw [forest] at hn
      apply SyntaxRenameBinders.eliminate_2 C _ hn
      have hZ2 := SyntaxRenameBinders.zf_under_2 hZ C
      have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw C)
      have hi2 : Derives Δ (empty i.castSucc.castSucc) := of_eq (by simp only [Formula.raise, Fin.val_zero, SyntaxNumeralSyntax.numeral, empty_rename]) (SyntaxRenameBinders.under_2 hi C)
      have hC : Derives Δ C := .hyp (Or.inl rfl)
      have hhW := OriginalTreeQuotationProperties.tree_range hZ2 head w.castSucc.castSucc (Fin.last m).castSucc hw2 (.conjL hC)
      have htW := OriginalTreeQuotationProperties.forest_range hZ2 tail w.castSucc.castSucc (Fin.last (m+1)) hw2 (.conjL (.conjR hC))
      have hF := StructuralListFieldCons.zero_iff hZ2 w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) n.castSucc.castSucc i.castSucc.castSucc q.castSucc.castSucc hw2 hhW htW (.conjR (.conjR hC)) hi2
      have hQ := OriginalQuotationValue.at_value hZ2 head w.castSucc.castSucc (Fin.last m).castSucc q.castSucc.castSucc hw2 (.conjL hC)
      have ho := SyntaxTypeLocalTransfer.iff_trans hF (.conjI (.conjR hQ) (.conjL hQ))
      exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, StructuralListFieldSyntax.field_rename, tree_rename, List.get_cons_zero]) ho
    · intro hi
      let C := consBody head tail w n
      let Δ := Context.add C (Context.image Formula.raise (Context.image Formula.raise Γ))
      rw [forest] at hn
      apply SyntaxRenameBinders.eliminate_2 C _ hn
      have hZ2 := SyntaxRenameBinders.zf_under_2 hZ C
      have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw C)
      have hi2 : Derives Δ (SyntaxNumeralSyntax.numeral (j.val+1) i.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename, Fin.val_succ]) (SyntaxRenameBinders.under_2 hi C)
      let I := (SyntaxNumeralSyntax.numeral j.val (Fin.last (m+2))).conj (successor i.castSucc.castSucc.castSucc (Fin.last (m+2)))
      let Ξ := Context.add I (Context.image Formula.raise Δ)
      apply SyntaxNumeralSyntax.eliminate_succ j.val i.castSucc.castSucc _ hi2
      have hZ3 := ZFContext.under hZ2 I
      have hw3 : Derives Ξ (omega w.castSucc.castSucc.castSucc) := of_eq (omega_rename w.castSucc.castSucc Fin.castSucc) (under hw2 I)
      have hC : Derives Δ C := .hyp (Or.inl rfl)
      have hC3 : Derives Ξ (consState head tail w.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc) :=
        of_eq (by simp only [C, consBody, Formula.raise, consState_rename]) (under hC I)
      have hI : Derives Ξ I := .hyp (Or.inl rfl)
      have hhW := OriginalTreeQuotationProperties.tree_range hZ3 head w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc hw3 (.conjL hC3)
      have htW := OriginalTreeQuotationProperties.forest_range hZ3 tail w.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc hw3 (.conjL (.conjR hC3))
      have hjW := SyntaxNumerals.range hZ3 j.val w.castSucc.castSucc.castSucc (Fin.last (m+2)) hw3 (.conjL hI)
      have hF := StructuralListFieldCons.successor_iff hZ3 w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc n.castSucc.castSucc.castSucc (Fin.last (m+2)) i.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc hw3 hhW htW hjW (.conjR hI) (.conjR (.conjR hC3))
      have hQ := ih hZ3 w.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc j (Fin.last (m+2)) q.castSucc.castSucc.castSucc hw3 (.conjL (.conjR hC3)) (.conjL hI)
      have ho := SyntaxTypeLocalTransfer.iff_trans hF hQ
      exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, StructuralListFieldSyntax.field_rename, tree_rename, List.get_cons_succ']) ho

end PPAC.Migration.Internal.OriginalQuotationForestRead
