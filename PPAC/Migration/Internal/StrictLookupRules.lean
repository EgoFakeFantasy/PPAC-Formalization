import PPAC.Migration.Internal.StrictLookupSyntax

/-! 严格查表在零和原Cons后继上的准确操作方程，索引遍历全部内部ω。 -/
namespace PPAC.Migration.Internal.StrictLookupRules
open Source SourceAlgebra SourceLogic OmegaSyntax StructuralListSyntax StructuralListProjectionSyntax StrictLookupSyntax
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem zero_selected {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n z y : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) :
    Derives Γ ((returned w n z y).iff (selected true w n y)) := by
  apply Derives.conjI
  · apply Derives.impI
    let R := returned w n z y
    let T := body w n z y
    let Δ := Context.add T (Context.image Formula.raise (Context.add R Γ))
    apply Derives.exE (p := T) (.hyp (Or.inl rfl))
    have hz1 : Derives Δ (empty z.castSucc) := of_eq (empty_rename z Fin.castSucc) (under (add hz R) T)
    have hT : Derives Δ T := .hyp (Or.inl rfl)
    have heq := StructuralListProjectionRecursion.iteration_zero false w.castSucc n.castSucc z.castSucc (Fin.last m) hz1 (.conjL hT)
    exact of_eq (selected_rename true w n y Fin.castSucc).symm
      (selected_input_subst true w.castSucc (Fin.last m) n.castSucc y.castSucc heq (.conjR hT))
  · apply Derives.impI
    exact intro_returned w n z y n (add (StructuralListPositionLogic.zero_value hZ false w n z hw hz) _) (.hyp (Or.inl rfl))

theorem successor_forward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h t n r s y : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (.mem h w)) (ht : Derives Γ (.mem t w))
    (hr : Derives Γ (.mem r w)) (hs : Derives Γ (successor s r))
    (hc : Derives Γ (consCode w h t n)) (hy : Derives Γ (returned w n s y)) : Derives Γ (returned w t r y) := by
  let T := (iteration false w.castSucc n.castSucc s.castSucc (Fin.last m)).conj (selected true w.castSucc (Fin.last m) y.castSucc)
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
  have hout := intro_returned _ _ _ _ _ htail (.conjR hT)
  simpa only [Formula.raise, returned_rename] using hout

theorem successor_backward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h t n r s y : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (.mem h w)) (ht : Derives Γ (.mem t w))
    (hr : Derives Γ (.mem r w)) (hs : Derives Γ (successor s r))
    (hc : Derives Γ (consCode w h t n)) (hy : Derives Γ (returned w t r y)) : Derives Γ (returned w n s y) := by
  let T := (iteration false w.castSucc t.castSucc r.castSucc (Fin.last m)).conj (selected true w.castSucc (Fin.last m) y.castSucc)
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
  have hout := intro_returned _ _ _ _ _ htail (.conjR hT)
  simpa only [Formula.raise, returned_rename] using hout

theorem successor_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h t n r s y : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (.mem h w)) (ht : Derives Γ (.mem t w))
    (hr : Derives Γ (.mem r w)) (hs : Derives Γ (successor s r)) (hc : Derives Γ (consCode w h t n)) :
    Derives Γ ((returned w n s y).iff (returned w t r y)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact successor_forward (ZFContext.add hZ _) _ _ _ _ _ _ _ (add hw _) (add hh _) (add ht _) (add hr _) (add hs _) (add hc _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact successor_backward (ZFContext.add hZ _) _ _ _ _ _ _ _ (add hw _) (add hh _) (add ht _) (add hr _) (add hs _) (add hc _) (.hyp (Or.inl rfl))
end PPAC.Migration.Internal.StrictLookupRules
