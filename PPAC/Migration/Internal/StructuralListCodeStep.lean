import PPAC.Migration.Internal.StructuralListCodeFields

/-! 保留实际Cons分解见证的码单射后继步。归纳假设严格用于前驱长度。 -/
namespace PPAC.Migration.Internal.StructuralListCodeStep
open Source SourceAlgebra SourceLogic OmegaSyntax StructuralListSyntax StructuralListCodeSyntax
open StructuralListLengthSyntax (hasLength hasLength_rename)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s a b : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (.mem r w)) (hs : Derives Γ (successor s r))
    (hi : Derives Γ (property w r)) (ha : Derives Γ (hasLength w a s)) (hb : Derives Γ (hasLength w b s))
    (he : Derives Γ (agree w s a b)) : Derives Γ (.equal a b) := by
  have hva := StructuralListCodeLength.successor_view hZ w a r s hw hr hs ha
  have hvb := StructuralListCodeLength.successor_view hZ w b r s hw hr hs hb
  let A := consViewBody w a r
  let Ξ := Context.add A (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_view w a r _ hva
  have hA : Derives Ξ A := .hyp (Or.inl rfl)
  have hvb2 : Derives Ξ (consView w.castSucc.castSucc b.castSucc.castSucc r.castSucc.castSucc) := by
    simpa only [Formula.raise, consView_rename] using OrderedPairElimination.under_two hvb A
  let B := consViewBody w.castSucc.castSucc b.castSucc.castSucc r.castSucc.castSucc
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise Ξ))
  apply eliminate_view w.castSucc.castSucc b.castSucc.castSucc r.castSucc.castSucc _ hvb2
  have hZ4 : ZFContext.Evidence Δ := ZFContext.under_two (ZFContext.under_two hZ A) B
  have lift {p : Formula m} (hp : Derives Γ p) : Derives Δ p.raise.raise.raise.raise :=
    OrderedPairElimination.under_two (OrderedPairElimination.under_two hp A) B
  have hw4 : Derives Δ (omega w.castSucc.castSucc.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using lift hw
  have hs4 : Derives Δ (successor s.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc) := by simpa only [Formula.raise, successor_rename] using lift hs
  have hi4 : Derives Δ (property w.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc) := by simpa only [Formula.raise, property_rename] using lift hi
  have he4 : Derives Δ (agree w.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc) := by simpa only [Formula.raise, agree_rename] using lift he
  have hA4 : Derives Δ (((Formula.mem (Fin.last m).castSucc.castSucc.castSucc w.castSucc.castSucc.castSucc.castSucc).conj
      (hasLength w.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc)).conj
      (consCode w.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc)) := by
    simpa only [A, consViewBody, Formula.raise, Formula.rename, hasLength_rename, consCode_rename] using OrderedPairElimination.under_two hA B
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hTW := StructuralListLengthBasic.code_member _ _ _ (.conjR (.conjL hA4))
  have hUW := StructuralListLengthBasic.code_member _ _ _ (.conjR (.conjL hB))
  have hHeads := StructuralListCodeFields.heads_equal hZ4 _ _ _ _ _ _ _ _ _ hw4 (lift hr) hs4
    (.conjL (.conjL hA4)) hTW (.conjL (.conjL hB)) hUW (.conjR hA4) (.conjR hB) he4
  have hTails := StructuralListCodeFields.agree_tails hZ4 _ _ _ _ _ _ _ _ _ hw4 (lift hr) hs4
    (.conjL (.conjL hA4)) hTW (.conjL (.conjL hB)) hUW (.conjR hA4) (.conjR hB) he4
  have hTailEq := property_at _ _ _ _ hi4 (.conjR (.conjL hA4)) (.conjR (.conjL hB)) hTails
  have hBHead := StructuralListCodeFields.head_subst _ _ _ _ _ (eq_symm hHeads) (.conjR hB)
  have hBTail := StructuralListCodeFields.tail_subst _ _ _ _ _ (eq_symm hTailEq) hBHead
  exact StructuralConsUnique.unique hZ4 _ _ _ _ _ hw4 (.conjL (.conjL hA4)) hTW (.conjR hA4) hBTail

theorem property_successor {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (.mem r w)) (hs : Derives Γ (successor s r))
    (hi : Derives Γ (property w r)) : Derives Γ (property w s) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let A := hasLength w.castSucc.castSucc (Fin.last m).castSucc s.castSucc.castSucc
  let B := hasLength w.castSucc.castSucc (Fin.last (m+1)) s.castSucc.castSucc
  let E := agree w.castSucc.castSucc s.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
  let Δ := Context.add E (Context.add B (Context.add A (Context.image Formula.raise (Context.image Formula.raise Γ))))
  have hZ2 : ZFContext.Evidence Δ := ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.rename (ZFContext.rename hZ Fin.castSucc) Fin.castSucc) A) B) E
  have lift {p : Formula m} (hp : Derives Γ p) : Derives Δ p.raise.raise := add (add (add (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hp)) A) B) E
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using lift hw
  have hs2 : Derives Δ (successor s.castSucc.castSucc r.castSucc.castSucc) := by simpa only [Formula.raise, successor_rename] using lift hs
  have hi2 : Derives Δ (property w.castSucc.castSucc r.castSucc.castSucc) := by simpa only [Formula.raise, property_rename] using lift hi
  exact point hZ2 _ _ _ _ _ hw2 (lift hr) hs2 hi2 (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))
end PPAC.Migration.Internal.StructuralListCodeStep
