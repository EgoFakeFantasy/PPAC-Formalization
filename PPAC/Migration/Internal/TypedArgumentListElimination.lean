import PPAC.Migration.Internal.OriginalNumericTermProgram

/-! 有类型原参数列表的实际Cons分解：内部前驱长度、头项合法性及完整尾列表类型。 -/
namespace PPAC.Migration.Internal.TypedArgumentListElimination
open Source SourceAlgebra SourceLogic OmegaSyntax
open SyntaxRenameQuerySyntax (of_eq)

def consParts {m} (w k a b h t : Fin m) : Formula m := .ex
  (((Formula.mem (Fin.last m) w.castSucc).conj (successor k.castSucc (Fin.last m))).conj
    ((SyntaxTermSyntax.term w.castSucc a.castSucc b.castSucc h.castSucc).conj
      (SyntaxMixedImageCodeSyntax.termList w.castSucc (Fin.last m) a.castSucc b.castSucc t.castSucc)))

theorem consParts_rename {m n} (w k a b h t : Fin m) (ρ : Fin m → Fin n) :
    (consParts w k a b h t).rename ρ = consParts (ρ w) (ρ k) (ρ a) (ρ b) (ρ h) (ρ t) := by
  simp only [consParts, Formula.rename, successor_rename, SyntaxTermSyntax.term_rename, SyntaxMixedImageCodeSyntax.termList_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem head_term {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w k a b h t n ell : Fin m)
    (hw : Derives Γ (omega w)) (hL : Derives Γ (SyntaxMixedImageCodeSyntax.termList w k a b n))
    (hh : Derives Γ (.mem h w)) (ht : Derives Γ (.mem t w))
    (hc : Derives Γ (StructuralListSyntax.consCode w h t n))
    (hell : Derives Γ (.mem ell w)) (hs : Derives Γ (successor k ell)) : Derives Γ (SyntaxTermSyntax.term w a b h) := by
  let Z := (Formula.mem (Fin.last m) w.castSucc).conj (empty (Fin.last m))
  let Δ := Context.add Z (Context.image Formula.raise Γ)
  apply Derives.exE (p := Z) (.conjL (.conjL hw))
  have hZ1 := ZFContext.under hZ Z
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw Z)
  have hL1 : Derives Δ (SyntaxMixedImageCodeSyntax.termList w.castSucc k.castSucc a.castSucc b.castSucc n.castSucc) := of_eq (SyntaxMixedImageCodeSyntax.termList_rename w k a b n Fin.castSucc) (under hL Z)
  have hc1 : Derives Δ (StructuralListSyntax.consCode w.castSucc h.castSucc t.castSucc n.castSucc) := of_eq (StructuralListSyntax.consCode_rename w h t n Fin.castSucc) (under hc Z)
  have hs1 : Derives Δ (successor k.castSucc ell.castSucc) := of_eq (successor_rename k ell Fin.castSucc) (under hs Z)
  have hZ : Derives Δ Z := .hyp (Or.inl rfl)
  have hi := SyntaxIndexLiftOrder.zero_member hZ1 w.castSucc ell.castSucc k.castSucc (Fin.last m) hw1 (under hell Z) hs1 (.conjR hZ)
  have hf := StructuralListFieldCons.zero_value hZ1 w.castSucc h.castSucc t.castSucc n.castSucc (Fin.last m) hw1 (under hh Z) (under ht Z) hc1 (.conjR hZ)
  exact of_eq (SyntaxTermSyntax.term_rename w a b h Fin.castSucc).symm (SyntaxMixedImageCodeFields.field_type _ _ _ _ _ _ _ hL1 hi hf)

theorem tail_typed_fields {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w k a b h t n ell : Fin m)
    (hw : Derives Γ (omega w)) (hL : Derives Γ (SyntaxMixedImageCodeSyntax.termList w k a b n))
    (hh : Derives Γ (.mem h w)) (ht : Derives Γ (.mem t w))
    (hc : Derives Γ (StructuralListSyntax.consCode w h t n))
    (hell : Derives Γ (.mem ell w)) (hs : Derives Γ (successor k ell)) :
    Derives Γ (SyntaxMixedImageCodeSyntax.typedFields w ell a b t) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let A := (Formula.mem (Fin.last m).castSucc ell.castSucc.castSucc).conj
    (StructuralListFieldSyntax.field w.castSucc.castSucc t.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)))
  let Δ := Context.add A (Context.image Formula.raise (Context.image Formula.raise Γ))
  have hZ2 := ZFContext.under_two hZ A
  have lift {p : Formula m} (hp : Derives Γ p) : Derives Δ p.raise.raise := OrderedPairElimination.under_two hp A
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (lift hw)
  have hL2 : Derives Δ (SyntaxMixedImageCodeSyntax.termList w.castSucc.castSucc k.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxMixedImageCodeSyntax.termList_rename]) (lift hL)
  have hc2 : Derives Δ (StructuralListSyntax.consCode w.castSucc.castSucc h.castSucc.castSucc t.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [Formula.raise, StructuralListSyntax.consCode_rename]) (lift hc)
  have hs2 : Derives Δ (successor k.castSucc.castSucc ell.castSucc.castSucc) := of_eq (by simp only [Formula.raise, successor_rename]) (lift hs)
  have hA : Derives Δ A := .hyp (Or.inl rfl)
  have hi := StructuralListTraceOrder.member_member hZ2 w.castSucc.castSucc (Fin.last m).castSucc ell.castSucc.castSucc hw2 (lift hell) (.conjL hA)
  have he := InsertExistence.exists_insert (Fin.last m).castSucc (Fin.last m).castSucc (ZFContext.arithmetic hZ2).base.pairing (ZFContext.arithmetic hZ2).base.union
  let S := successor (Fin.last (m+2)) (Fin.last m).castSucc.castSucc
  let Ξ := Context.add S (Context.image Formula.raise Δ)
  apply Derives.exE (p := S) he
  have hZ3 := ZFContext.under hZ2 S
  have hw3 : Derives Ξ (omega w.castSucc.castSucc.castSucc) := of_eq (omega_rename _ Fin.castSucc) (under hw2 S)
  have hL3 : Derives Ξ (SyntaxMixedImageCodeSyntax.termList w.castSucc.castSucc.castSucc k.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc) := of_eq (SyntaxMixedImageCodeSyntax.termList_rename _ _ _ _ _ Fin.castSucc) (under hL2 S)
  have hc3 : Derives Ξ (StructuralListSyntax.consCode w.castSucc.castSucc.castSucc h.castSucc.castSucc.castSucc t.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc) := of_eq (StructuralListSyntax.consCode_rename _ _ _ _ Fin.castSucc) (under hc2 S)
  have hs3 : Derives Ξ (successor k.castSucc.castSucc.castSucc ell.castSucc.castSucc.castSucc) := of_eq (successor_rename _ _ Fin.castSucc) (under hs2 S)
  have hf3 : Derives Ξ (StructuralListFieldSyntax.field w.castSucc.castSucc.castSucc t.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc) := of_eq (StructuralListFieldSyntax.field_rename _ _ _ _ Fin.castSucc) (under (.conjR hA) S)
  have hS : Derives Ξ S := .hyp (Or.inl rfl)
  have hj := SyntaxIndexLiftOrder.successor_member hZ3 w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc ell.castSucc.castSucc.castSucc (Fin.last (m+2)) k.castSucc.castSucc.castSucc hw3 (under hi S) (under (lift hell) S) (under (.conjL hA) S) hS hs3
  have hf := StructuralListFieldCons.successor_backward hZ3 w.castSucc.castSucc.castSucc h.castSucc.castSucc.castSucc t.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+2)) (Fin.last (m+1)).castSucc hw3 (under (lift hh) S) (under (lift ht) S) (under hi S) hS hc3 hf3
  have hout := SyntaxMixedImageCodeFields.field_type _ _ _ _ _ _ _ hL3 hj hf
  exact of_eq (SyntaxTermSyntax.term_rename w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc (Fin.last (m+1)) Fin.castSucc).symm hout

theorem tail_list {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w k a b h t n ell : Fin m)
    (hw : Derives Γ (omega w)) (hL : Derives Γ (SyntaxMixedImageCodeSyntax.termList w k a b n))
    (hh : Derives Γ (.mem h w)) (ht : Derives Γ (.mem t w))
    (hc : Derives Γ (StructuralListSyntax.consCode w h t n))
    (hell : Derives Γ (.mem ell w)) (hs : Derives Γ (successor k ell))
    (hlen : Derives Γ (StructuralListLengthSyntax.hasLength w t ell)) :
    Derives Γ (SyntaxMixedImageCodeSyntax.termList w ell a b t) :=
  .conjI hell (.conjI (.conjL (.conjR hL)) (.conjI (.conjI ht hlen) (tail_typed_fields hZ w k a b h t n ell hw hL hh ht hc hell hs)))

theorem cons_parts {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w k a b h t n : Fin m)
    (hw : Derives Γ (omega w)) (hL : Derives Γ (SyntaxMixedImageCodeSyntax.termList w k a b n))
    (hh : Derives Γ (.mem h w)) (ht : Derives Γ (.mem t w))
    (hc : Derives Γ (StructuralListSyntax.consCode w h t n)) : Derives Γ (consParts w k a b h t) := by
  have hex := StructuralListLengthRules.cons_predecessor hZ w h t n k hw hh ht hc (.conjR (.conjL (.conjR (.conjR hL))))
  let B := ((Formula.mem (Fin.last m) w.castSucc).conj (successor k.castSucc (Fin.last m))).conj (StructuralListLengthSyntax.hasLength w.castSucc t.castSucc (Fin.last m))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hex
  have hZ1 := ZFContext.under hZ B
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hL1 : Derives Δ (SyntaxMixedImageCodeSyntax.termList w.castSucc k.castSucc a.castSucc b.castSucc n.castSucc) := of_eq (SyntaxMixedImageCodeSyntax.termList_rename _ _ _ _ _ Fin.castSucc) (under hL B)
  have hc1 : Derives Δ (StructuralListSyntax.consCode w.castSucc h.castSucc t.castSucc n.castSucc) := of_eq (StructuralListSyntax.consCode_rename _ _ _ _ Fin.castSucc) (under hc B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hp := head_term hZ1 w.castSucc k.castSucc a.castSucc b.castSucc h.castSucc t.castSucc n.castSucc (Fin.last m) hw1 hL1 (under hh B) (under ht B) hc1 (.conjL (.conjL hB)) (.conjR (.conjL hB))
  have htail := tail_list hZ1 w.castSucc k.castSucc a.castSucc b.castSucc h.castSucc t.castSucc n.castSucc (Fin.last m) hw1 hL1 (under hh B) (under ht B) hc1 (.conjL (.conjL hB)) (.conjR (.conjL hB)) (.conjR hB)
  have hout : Derives Δ (consParts w.castSucc k.castSucc a.castSucc b.castSucc h.castSucc t.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Formula.instantiate, Formula.rename, successor_rename, SyntaxTermSyntax.term_rename, SyntaxMixedImageCodeSyntax.termList_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI (.conjL hB) (.conjI hp htail))
  exact of_eq (consParts_rename w k a b h t Fin.castSucc).symm hout

end PPAC.Migration.Internal.TypedArgumentListElimination
