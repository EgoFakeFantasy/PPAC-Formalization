import PPAC.Migration.Internal.FreeWeakenValueSyntax

/-! 所有内部自然索引的实际后继变量值存在、唯一、自然及精确域。 -/
namespace PPAC.Migration.Internal.FreeWeakenValue
open Source SourceAlgebra SourceLogic OmegaSyntax FreeWeakenValueSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem natural {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w idx y : Fin m)
    (hw : Derives Γ (omega w)) (hv : Derives Γ (shifted w idx y)) : Derives Γ (.mem y w) := by
  let B := (successor (Fin.last m) idx.castSucc).conj (SyntaxVariableSyntax.code false w.castSucc (Fin.last m) y.castSucc)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hv
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw B)
  exact HornVariableValue.code_natural (ZFContext.under hZ B) false _ _ _ hw1 (.conjR (.hyp (Or.inl rfl)))

theorem index_natural {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w idx y : Fin m)
    (hw : Derives Γ (omega w)) (hv : Derives Γ (shifted w idx y)) : Derives Γ (.mem idx w) := by
  let B := (successor (Fin.last m) idx.castSucc).conj (SyntaxVariableSyntax.code false w.castSucc (Fin.last m) y.castSucc)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hv
  have hZ1 := ZFContext.under hZ B
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hs := SyntaxVariableDecode.index_natural false _ _ _ (.conjR hB)
  exact StructuralListTraceOrder.member_member hZ1 w.castSucc idx.castSucc (Fin.last m) hw1 hs (InsertLogic.new_member _ _ _ (.conjL hB))

theorem exists_shifted {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w idx : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (.mem idx w)) : Derives Γ (hasShifted w idx) := by
  have he := InsertExistence.exists_insert idx idx (ZFContext.arithmetic hZ).base.pairing (ZFContext.arithmetic hZ).base.union
  let S := successor (Fin.last m) idx.castSucc
  let Δ := Context.add S (Context.image Formula.raise Γ)
  apply Derives.exE (p := S) he
  have hZ1 := ZFContext.under hZ S
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw S)
  have hi1 : Derives Δ (.mem idx.castSucc w.castSucc) := under hi S
  have hS : Derives Δ S := .hyp (Or.inl rfl)
  have hs := OmegaStructureAlgebra.successor_member _ _ _ (ZFContext.arithmetic hZ1).base.extensionality hw1 hi1 hS
  have hy := SyntaxVariables.exists_code hZ1 false w.castSucc (Fin.last m) hw1 hs
  let C := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj (SyntaxVariableSyntax.code false w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)))
  let Ξ := Context.add C (Context.image Formula.raise Δ)
  apply Derives.exE (p := C) hy
  have hS1 : Derives Ξ (successor (Fin.last m).castSucc idx.castSucc.castSucc) := of_eq (successor_rename _ _ Fin.castSucc) (under hS C)
  have hC : Derives Ξ C := .hyp (Or.inl rfl)
  have hv := intro_shifted _ _ _ _ hS1 (.conjR hC)
  have ho : Derives Ξ (hasShifted w.castSucc.castSucc idx.castSucc.castSucc) := by
    apply Derives.exI (Fin.last (m+1))
    exact of_eq (by simp only [Formula.instantiate, shifted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hv
  simpa only [Formula.raise, hasShifted_rename] using ho

theorem at_successor {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w idx y s : Fin m)
    (hs : Derives Γ (successor s idx)) :
    Derives Γ ((shifted w idx y).iff (SyntaxVariableSyntax.code false w s y)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := shifted w idx y
    let B := (successor (Fin.last m) idx.castSucc).conj (SyntaxVariableSyntax.code false w.castSucc (Fin.last m) y.castSucc)
    let Δ := Context.add B (Context.image Formula.raise (Context.add E Γ))
    apply Derives.exE (p := B) (.hyp (Or.inl rfl))
    have hs1 : Derives Δ (successor s.castSucc idx.castSucc) := of_eq (successor_rename s idx Fin.castSucc) (under (add hs E) B)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have heq := InsertLogic.unique _ _ _ _ (ZFContext.arithmetic (ZFContext.under (ZFContext.add hZ E) B)).base.extensionality (.conjL hB) hs1
    have ho := code_index_subst _ _ _ _ heq (.conjR hB)
    exact of_eq (SyntaxVariableSyntax.code_rename false w s y Fin.castSucc).symm ho
  · apply Derives.impI
    exact intro_shifted w idx y s (add hs _) (.hyp (Or.inl rfl))

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w idx y z : Fin m)
    (hw : Derives Γ (omega w)) (hy : Derives Γ (shifted w idx y)) (hz : Derives Γ (shifted w idx z)) : Derives Γ (.equal y z) := by
  let B := (successor (Fin.last m) idx.castSucc).conj (SyntaxVariableSyntax.code false w.castSucc (Fin.last m) y.castSucc)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hy
  have hZ1 := ZFContext.under hZ B
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hz1 : Derives Δ (shifted w.castSucc idx.castSucc z.castSucc) := of_eq (shifted_rename w idx z Fin.castSucc) (under hz B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hc := Derives.impE (.conjL (at_successor hZ1 _ _ _ _ (.conjL hB))) hz1
  exact SyntaxVariables.unique hZ1 false _ _ _ _ hw1 (.conjR hB) hc

theorem has_shifted_iff_natural {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w idx : Fin m)
    (hw : Derives Γ (omega w)) : Derives Γ ((hasShifted w idx).iff (.mem idx w)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := hasShifted w idx
    let B := shifted w.castSucc idx.castSucc (Fin.last m)
    let Δ := Context.add B (Context.image Formula.raise (Context.add E Γ))
    apply Derives.exE (p := B) (.hyp (Or.inl rfl))
    have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under (add hw E) B)
    exact index_natural (ZFContext.under (ZFContext.add hZ E) B) _ _ _ hw1 (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact exists_shifted (ZFContext.add hZ _) w idx (add hw _) (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.FreeWeakenValue
