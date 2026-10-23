import PPAC.Migration.Internal.OriginalQuotationForestRead

/-! 原quotation森林的实际内部长度与其有限模式长度一致。 -/
namespace PPAC.Migration.Internal.OriginalQuotationForestLength
open Source SourceAlgebra SourceLogic OmegaSyntax OriginalTreeQuotationSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket (Tree)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem at_numeral {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (children : List Tree) (w n l : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (forest children w n))
    (hl : Derives Γ (SyntaxNumeralSyntax.numeral children.length l)) : Derives Γ (StructuralListLengthSyntax.hasLength w n l) := by
  induction children generalizing m with
  | nil =>
    have hNil : Derives Γ (StructuralListSyntax.nilCode w n) := of_eq (by simp only [forest]) hn
    exact StructuralListLengthConstruct.nil_length hZ w n l hw hNil hl
  | cons head tail ih =>
    let C := consBody head tail w n
    let Δ := Context.add C (Context.image Formula.raise (Context.image Formula.raise Γ))
    rw [forest] at hn
    apply SyntaxRenameBinders.eliminate_2 C _ hn
    have hZ2 := SyntaxRenameBinders.zf_under_2 hZ C
    have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw C)
    have hl2 : Derives Δ (SyntaxNumeralSyntax.numeral (tail.length+1) l.castSucc.castSucc) :=
      of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename, List.length_cons]) (SyntaxRenameBinders.under_2 hl C)
    let L := (SyntaxNumeralSyntax.numeral tail.length (Fin.last (m+2))).conj (successor l.castSucc.castSucc.castSucc (Fin.last (m+2)))
    let Ξ := Context.add L (Context.image Formula.raise Δ)
    apply SyntaxNumeralSyntax.eliminate_succ tail.length l.castSucc.castSucc _ hl2
    have hZ3 := ZFContext.under hZ2 L
    have hw3 : Derives Ξ (omega w.castSucc.castSucc.castSucc) := of_eq (omega_rename w.castSucc.castSucc Fin.castSucc) (under hw2 L)
    have hC : Derives Δ C := .hyp (Or.inl rfl)
    have hC3 : Derives Ξ (consState head tail w.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc) :=
      of_eq (by simp only [C, consBody, Formula.raise, consState_rename]) (under hC L)
    have hL : Derives Ξ L := .hyp (Or.inl rfl)
    have hhW := OriginalTreeQuotationProperties.tree_range hZ3 head w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc hw3 (.conjL hC3)
    have ht := ih hZ3 w.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2)) hw3 (.conjL (.conjR hC3)) (.conjL hL)
    have ho := StructuralListLengthConstruct.cons_length hZ3 w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc n.castSucc.castSucc.castSucc (Fin.last (m+2)) l.castSucc.castSucc.castSucc hw3 hhW (.conjR (.conjR hC3)) ht (.conjR hL)
    exact of_eq (by simp only [Formula.raise, StructuralListLengthSyntax.hasLength_rename]) ho

end PPAC.Migration.Internal.OriginalQuotationForestLength
