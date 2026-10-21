import PPAC.Migration.Internal.StructuralListPositionLogic

/-! 内部反向索引r+k=l的真实加法后继转换及严格旧索引界。 -/
namespace PPAC.Migration.Internal.StructuralListPositionArithmetic
open Source SourceAlgebra SourceLogic OmegaSyntax NaturalAdditionSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

def predecessorSum {m} (w r k l : Fin m) : Formula m := .ex
  (((Formula.mem (Fin.last m) w.castSucc).conj (sum w.castSucc r.castSucc k.castSucc (Fin.last m))).conj (successor l.castSucc (Fin.last m)))

theorem predecessor_sum {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s k l : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (.mem r w)) (hk : Derives Γ (.mem k w))
    (hs : Derives Γ (successor s r)) (hl : Derives Γ (sum w s k l)) : Derives Γ (predecessorSum w r k l) := by
  have hq := ZFArithmetic.add_exists hZ w r k hw hr hk
  let Q := (Formula.mem (Fin.last m) w.castSucc).conj (sum w.castSucc r.castSucc k.castSucc (Fin.last m))
  let Δ := Context.add Q (Context.image Formula.raise Γ)
  change Derives Γ (.ex Q) at hq
  apply Derives.exE (p := Q) hq
  have hZ1 : ZFContext.Evidence Δ := ZFContext.under hZ Q
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw Q
  have hs1 : Derives Δ (successor s.castSucc r.castSucc) := by simpa only [Formula.raise, successor_rename] using under hs Q
  have hl1 : Derives Δ (sum w.castSucc s.castSucc k.castSucc l.castSucc) := by simpa only [Formula.raise, sum_rename] using under hl Q
  have hQ : Derives Δ Q := .hyp (Or.inl rfl)
  have hsucc := NaturalAdditionAlgebraLaws.shift_forward (ZFContext.arithmetic hZ1) _ _ _ _ _ _ (ZFContext.recAdd hZ1)
    (ZFContext.separation hZ1 NaturalAdditionShift.matrix) hw1 (under hr Q) hs1 (under hk Q) (.conjR hQ) hl1
  apply Derives.exI (Fin.last m)
  simp only [Formula.rename, Formula.instantiate, sum_rename, successor_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI hQ hsucc

theorem old_index {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s k l : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (.mem r w)) (hk : Derives Γ (.mem k w))
    (hs : Derives Γ (successor s r)) (hl : Derives Γ (sum w s k l)) : Derives Γ (.mem k l) := by
  have hp := predecessor_sum hZ w r s k l hw hr hk hs hl
  let P := ((Formula.mem (Fin.last m) w.castSucc).conj (sum w.castSucc r.castSucc k.castSucc (Fin.last m))).conj (successor l.castSucc (Fin.last m))
  let Δ := Context.add P (Context.image Formula.raise Γ)
  change Derives Γ (.ex P) at hp
  apply Derives.exE (p := P) hp
  have hZ1 : ZFContext.Evidence Δ := ZFContext.under hZ P
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw P
  have hP : Derives Δ P := .hyp (Or.inl rfl)
  have hb := GodelPairArithmetic.sum_right_bound hZ1 _ _ _ _ hw1 (under hr P) (under hk P) (.conjR (.conjL hP))
  exact NaturalAdditionBounds.into_successor _ _ _ hb (.conjR hP)

theorem swap_successors {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s k j l : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (.mem r w)) (hk : Derives Γ (.mem k w))
    (hs : Derives Γ (successor s r)) (hj : Derives Γ (successor j k))
    (hl : Derives Γ (sum w s k l)) : Derives Γ (sum w r j l) := by
  have hp := predecessor_sum hZ w r s k l hw hr hk hs hl
  let P := ((Formula.mem (Fin.last m) w.castSucc).conj (sum w.castSucc r.castSucc k.castSucc (Fin.last m))).conj (successor l.castSucc (Fin.last m))
  let Δ := Context.add P (Context.image Formula.raise Γ)
  change Derives Γ (.ex P) at hp
  apply Derives.exE (p := P) hp
  have hZ1 : ZFContext.Evidence Δ := ZFContext.under hZ P
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw P
  have hj1 : Derives Δ (successor j.castSucc k.castSucc) := by simpa only [Formula.raise, successor_rename] using under hj P
  have hP : Derives Δ P := .hyp (Or.inl rfl)
  have hout := ZFArithmetic.add_succ_backward hZ1 _ _ _ _ _ _ hw1 (under hr P) (under hk P) hj1 (.conjR (.conjL hP)) (.conjR hP)
  simpa only [Formula.raise, sum_rename] using hout
end PPAC.Migration.Internal.StructuralListPositionArithmetic
