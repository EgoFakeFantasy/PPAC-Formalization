import PPAC.Migration.Internal.StructuralListEndSyntax

/-! 实际长度下的Nil终端：Nil零点，Cons通过精确前驱长度和真实tail移位对齐。 -/
namespace PPAC.Migration.Internal.StructuralListEndRules
open Source SourceAlgebra SourceLogic OmegaSyntax StructuralListSyntax StructuralListProjectionSyntax StructuralListLengthSyntax StructuralListEndSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem from_nil {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n l y : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (nilCode w n)) (hl : Derives Γ (hasLength w n l))
    (hy : Derives Γ (iteration false w n l y)) : Derives Γ (nilCode w y) := by
  have hz := StructuralListLengthRules.nil_empty hZ w n l hw hn hl
  have heq := StructuralListProjectionRecursion.iteration_zero false w n l y hz hy
  exact StructuralListTraceOrder.nil_output_subst w n y (eq_symm heq) hn

theorem from_cons {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h t n l y : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (.mem h w)) (ht : Derives Γ (.mem t w))
    (hc : Derives Γ (consCode w h t n)) (hl : Derives Γ (hasLength w n l))
    (hy : Derives Γ (iteration false w n l y)) (he : Derives Γ (ends w t)) : Derives Γ (nilCode w y) := by
  have hp := StructuralListLengthRules.cons_predecessor hZ w h t n l hw hh ht hc hl
  let P := ((Formula.mem (Fin.last m) w.castSucc).conj (successor l.castSucc (Fin.last m))).conj
    (hasLength w.castSucc t.castSucc (Fin.last m))
  let Δ := Context.add P (Context.image Formula.raise Γ)
  change Derives Γ (.ex P) at hp
  apply Derives.exE (p := P) hp
  have hZ1 : ZFContext.Evidence Δ := ZFContext.under hZ P
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw P
  have hc1 : Derives Δ (consCode w.castSucc h.castSucc t.castSucc n.castSucc) := by simpa only [Formula.raise, consCode_rename] using under hc P
  have hy1 : Derives Δ (iteration false w.castSucc n.castSucc l.castSucc y.castSucc) := by simpa only [Formula.raise, iteration_rename] using under hy P
  have he1 : Derives Δ (ends w.castSucc t.castSucc) := by simpa only [Formula.raise, ends_rename] using under he P
  have hP : Derives Δ P := .hyp (Or.inl rfl)
  have hst : Derives Δ (StructuralListProjectionSyntax.step false w.castSucc n.castSucc t.castSucc) :=
    .disjL (StructuralListProjection.selected_cons false _ _ _ _ (under hh P) (under ht P) hc1)
  have htail := StructuralListShift.shift_forward hZ1 false w.castSucc n.castSucc t.castSucc (Fin.last m) l.castSucc y.castSucc
    hw1 (.conjL (.conjL hP)) (.conjR (.conjL hP)) hst hy1
  have hout := StructuralListEndSyntax.at_values _ _ _ _ he1 (.conjR hP) htail
  simpa only [Formula.raise, nilCode_rename] using hout
end PPAC.Migration.Internal.StructuralListEndRules
