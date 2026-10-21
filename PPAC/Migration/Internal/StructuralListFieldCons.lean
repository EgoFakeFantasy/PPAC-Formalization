import PPAC.Migration.Internal.StructuralListFieldValues

/-! 字段读取严格保持原Cons的零点和后继尾递归式，覆盖全部内部自然索引。 -/
namespace PPAC.Migration.Internal.StructuralListFieldCons
open Source SourceAlgebra SourceLogic OmegaSyntax StructuralListSyntax StructuralListProjectionSyntax StructuralListFieldSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem zero_value {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h t n z : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (.mem h w)) (ht : Derives Γ (.mem t w))
    (hc : Derives Γ (consCode w h t n)) (hz : Derives Γ (empty z)) : Derives Γ (field w n z h) :=
  intro_field w n z h n (StructuralListPositionLogic.zero_value hZ false w n z hw hz)
    (.disjL (StructuralListProjection.selected_cons true w h t n hh ht hc))

theorem zero_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h t n z y : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (.mem h w)) (ht : Derives Γ (.mem t w))
    (hc : Derives Γ (consCode w h t n)) (hz : Derives Γ (empty z)) (hy : Derives Γ (field w n z y)) : Derives Γ (.equal y h) := by
  let T := (iteration false w.castSucc n.castSucc z.castSucc (Fin.last m)).conj (step true w.castSucc (Fin.last m) y.castSucc)
  let Δ := Context.add T (Context.image Formula.raise Γ)
  change Derives Γ (.ex T) at hy
  apply Derives.exE (p := T) hy
  have hZ1 : ZFContext.Evidence Δ := ZFContext.under hZ T
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw T
  have hc1 : Derives Δ (consCode w.castSucc h.castSucc t.castSucc n.castSucc) := by simpa only [Formula.raise, consCode_rename] using under hc T
  have hz1 : Derives Δ (empty z.castSucc) := by simpa only [Formula.raise, empty_rename] using under hz T
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have heq := StructuralListProjectionRecursion.iteration_zero false _ _ _ _ hz1 (.conjL hT)
  have hst := StructuralListIterationTransport.step_input_subst true _ _ _ _ heq (.conjR hT)
  exact StructuralListProjection.on_cons hZ1 true _ _ _ _ _ hw1 (under hh T) (under ht T) hc1 hst

theorem zero_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h t n z y : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (.mem h w)) (ht : Derives Γ (.mem t w))
    (hc : Derives Γ (consCode w h t n)) (hz : Derives Γ (empty z)) : Derives Γ ((field w n z y).iff (.equal y h)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact zero_point (ZFContext.add hZ _) _ _ _ _ _ _ (add hw _) (add hh _) (add ht _) (add hc _) (add hz _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact output_subst w n z h y (eq_symm (.hyp (Or.inl rfl))) (add (zero_value hZ w h t n z hw hh ht hc hz) _)

theorem successor_forward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h t n r s y : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (.mem h w)) (ht : Derives Γ (.mem t w))
    (hr : Derives Γ (.mem r w)) (hs : Derives Γ (successor s r))
    (hc : Derives Γ (consCode w h t n)) (hy : Derives Γ (field w n s y)) : Derives Γ (field w t r y) := by
  let T := (iteration false w.castSucc n.castSucc s.castSucc (Fin.last m)).conj (step true w.castSucc (Fin.last m) y.castSucc)
  let Δ := Context.add T (Context.image Formula.raise Γ)
  change Derives Γ (.ex T) at hy
  apply Derives.exE (p := T) hy
  have hZ1 : ZFContext.Evidence Δ := ZFContext.under hZ T
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw T
  have hs1 : Derives Δ (successor s.castSucc r.castSucc) := by simpa only [Formula.raise, successor_rename] using under hs T
  have hc1 : Derives Δ (consCode w.castSucc h.castSucc t.castSucc n.castSucc) := by simpa only [Formula.raise, consCode_rename] using under hc T
  have hst : Derives Δ (step false w.castSucc n.castSucc t.castSucc) := .disjL (StructuralListProjection.selected_cons false _ _ _ _ (under hh T) (under ht T) hc1)
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have htail := StructuralListShift.shift_forward hZ1 false _ _ _ _ _ _ hw1 (under hr T) hs1 hst (.conjL hT)
  have hout := intro_field _ _ _ _ _ htail (.conjR hT)
  simpa only [Formula.raise, field_rename] using hout

theorem successor_backward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h t n r s y : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (.mem h w)) (ht : Derives Γ (.mem t w))
    (hr : Derives Γ (.mem r w)) (hs : Derives Γ (successor s r))
    (hc : Derives Γ (consCode w h t n)) (hy : Derives Γ (field w t r y)) : Derives Γ (field w n s y) := by
  let T := (iteration false w.castSucc t.castSucc r.castSucc (Fin.last m)).conj (step true w.castSucc (Fin.last m) y.castSucc)
  let Δ := Context.add T (Context.image Formula.raise Γ)
  change Derives Γ (.ex T) at hy
  apply Derives.exE (p := T) hy
  have hZ1 : ZFContext.Evidence Δ := ZFContext.under hZ T
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw T
  have hs1 : Derives Δ (successor s.castSucc r.castSucc) := by simpa only [Formula.raise, successor_rename] using under hs T
  have hc1 : Derives Δ (consCode w.castSucc h.castSucc t.castSucc n.castSucc) := by simpa only [Formula.raise, consCode_rename] using under hc T
  have hst : Derives Δ (step false w.castSucc n.castSucc t.castSucc) := .disjL (StructuralListProjection.selected_cons false _ _ _ _ (under hh T) (under ht T) hc1)
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have htail := StructuralListShift.shift_backward hZ1 false _ _ _ _ _ _ hw1 (under hr T) hs1 hst (.conjL hT)
  have hout := intro_field _ _ _ _ _ htail (.conjR hT)
  simpa only [Formula.raise, field_rename] using hout

theorem successor_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h t n r s y : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (.mem h w)) (ht : Derives Γ (.mem t w))
    (hr : Derives Γ (.mem r w)) (hs : Derives Γ (successor s r)) (hc : Derives Γ (consCode w h t n)) :
    Derives Γ ((field w n s y).iff (field w t r y)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact successor_forward (ZFContext.add hZ _) _ _ _ _ _ _ _ (add hw _) (add hh _) (add ht _) (add hr _) (add hs _) (add hc _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact successor_backward (ZFContext.add hZ _) _ _ _ _ _ _ _ (add hw _) (add hh _) (add ht _) (add hr _) (add hs _) (add hc _) (.hyp (Or.inl rfl))
end PPAC.Migration.Internal.StructuralListFieldCons
