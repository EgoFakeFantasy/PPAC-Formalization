import PPAC.Migration.Internal.RawCodeShiftInduction

/-! 原投影一步种子后的真实迭代移位等值和双条件，索引为全部内部自然数。 -/
namespace PPAC.Migration.Internal.RawCodeShift
open Source SourceAlgebra SourceLogic OmegaSyntax RawCodeProjectionSyntax RawCodeIterationTransport RawCodeShiftSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem shift_equal {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (head : Bool) (w a b r s y z : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (.mem r w)) (hs : Derives Γ (successor s r))
    (hab : Derives Γ (step head w a b)) (hy : Derives Γ (iteration head w a s y))
    (hz : Derives Γ (iteration head w b r z)) : Derives Γ (.equal y z) := by
  have hu := exists_value hZ head w a r hw hr
  let U := iteration head w.castSucc a.castSucc r.castSucc (Fin.last m)
  let Δ := Context.add U (Context.image Formula.raise Γ)
  change Derives Γ (.ex U) at hu
  apply Derives.exE (p := U) hu
  have hZ1 : ZFContext.Evidence Δ := ZFContext.under hZ U
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw U
  have hr1 : Derives Δ (.mem r.castSucc w.castSucc) := under hr U
  have hs1 : Derives Δ (successor s.castSucc r.castSucc) := by simpa only [Formula.raise, successor_rename] using under hs U
  have hab1 : Derives Δ (step head w.castSucc a.castSucc b.castSucc) := by simpa only [Formula.raise, step_rename] using under hab U
  have hy1 : Derives Δ (iteration head w.castSucc a.castSucc s.castSucc y.castSucc) := by simpa only [Formula.raise, iteration_rename] using under hy U
  have hz1 : Derives Δ (iteration head w.castSucc b.castSucc r.castSucc z.castSucc) := by simpa only [Formula.raise, iteration_rename] using under hz U
  have hU : Derives Δ U := .hyp (Or.inl rfl)
  have hc := RawCodeShiftInduction.at_index hZ1 head _ _ _ _ hw1 hr1 hab1
  have hother := at_values head _ _ _ _ _ _ hc hU hz1
  have hnext := RawCodeProjectionRecursion.iteration_step hZ1 head _ _ _ _ _ _ hw1 hr1 hs1 hU hy1
  exact RawCodeProjection.functional_point hZ1 head _ _ _ _ hw1 hnext hother

theorem shift_forward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (head : Bool) (w a b r s y : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (.mem r w)) (hs : Derives Γ (successor s r))
    (hab : Derives Γ (step head w a b)) (hy : Derives Γ (iteration head w a s y)) : Derives Γ (iteration head w b r y) := by
  have hz := exists_value hZ head w b r hw hr
  let Z := iteration head w.castSucc b.castSucc r.castSucc (Fin.last m)
  let Δ := Context.add Z (Context.image Formula.raise Γ)
  change Derives Γ (.ex Z) at hz
  apply Derives.exE (p := Z) hz
  have hZ1 : ZFContext.Evidence Δ := ZFContext.under hZ Z
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw Z
  have hs1 : Derives Δ (successor s.castSucc r.castSucc) := by simpa only [Formula.raise, successor_rename] using under hs Z
  have hab1 : Derives Δ (step head w.castSucc a.castSucc b.castSucc) := by simpa only [Formula.raise, step_rename] using under hab Z
  have hy1 : Derives Δ (iteration head w.castSucc a.castSucc s.castSucc y.castSucc) := by simpa only [Formula.raise, iteration_rename] using under hy Z
  have hZval : Derives Δ Z := .hyp (Or.inl rfl)
  have heq := shift_equal hZ1 head _ _ _ _ _ _ _ hw1 (under hr Z) hs1 hab1 hy1 hZval
  have hout := value_subst head _ _ _ _ _ (eq_symm heq) hZval
  simpa only [Formula.raise, iteration_rename] using hout

theorem shift_backward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (head : Bool) (w a b r s y : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (.mem r w)) (hs : Derives Γ (successor s r))
    (hab : Derives Γ (step head w a b)) (hy : Derives Γ (iteration head w b r y)) : Derives Γ (iteration head w a s y) := by
  have hsW := OmegaStructureAlgebra.successor_member w s r (ZFContext.arithmetic hZ).base.extensionality hw hr hs
  have hz := exists_value hZ head w a s hw hsW
  let Z := iteration head w.castSucc a.castSucc s.castSucc (Fin.last m)
  let Δ := Context.add Z (Context.image Formula.raise Γ)
  change Derives Γ (.ex Z) at hz
  apply Derives.exE (p := Z) hz
  have hZ1 : ZFContext.Evidence Δ := ZFContext.under hZ Z
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw Z
  have hs1 : Derives Δ (successor s.castSucc r.castSucc) := by simpa only [Formula.raise, successor_rename] using under hs Z
  have hab1 : Derives Δ (step head w.castSucc a.castSucc b.castSucc) := by simpa only [Formula.raise, step_rename] using under hab Z
  have hy1 : Derives Δ (iteration head w.castSucc b.castSucc r.castSucc y.castSucc) := by simpa only [Formula.raise, iteration_rename] using under hy Z
  have hZval : Derives Δ Z := .hyp (Or.inl rfl)
  have heq := shift_equal hZ1 head _ _ _ _ _ _ _ hw1 (under hr Z) hs1 hab1 hZval hy1
  have hout := value_subst head _ _ _ _ _ heq hZval
  simpa only [Formula.raise, iteration_rename] using hout

theorem shift_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (head : Bool) (w a b r s y : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (.mem r w)) (hs : Derives Γ (successor s r))
    (hab : Derives Γ (step head w a b)) : Derives Γ ((iteration head w a s y).iff (iteration head w b r y)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact shift_forward (ZFContext.add hZ _) head _ _ _ _ _ _ (add hw _) (add hr _) (add hs _) (add hab _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact shift_backward (ZFContext.add hZ _) head _ _ _ _ _ _ (add hw _) (add hr _) (add hs _) (add hab _) (.hyp (Or.inl rfl))
end PPAC.Migration.Internal.RawCodeShift
