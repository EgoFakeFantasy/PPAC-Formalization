import PPAC.Migration.Internal.RawCodeGetValues
import PPAC.Migration.Internal.RawCodeIterationLaws

/-! 任意外壳的get原递归方程；所有索引为内部自然数，head/tail均为实际关系。 -/
namespace PPAC.Migration.Internal.RawCodeGetLaws
open Source SourceAlgebra SourceLogic OmegaSyntax RawCodeProjectionSyntax RawCodeGetSyntax

theorem zero_forward {m} {Γ : Context m} (w x z y : Fin m)
    (hz : Derives Γ (empty z)) (hy : Derives Γ (get w x z y)) : Derives Γ (step true w x y) := by
  let B := (iteration false w.castSucc x.castSucc z.castSucc (Fin.last m)).conj (step true w.castSucc (Fin.last m) y.castSucc)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hy
  have hz1 : Derives Δ (empty z.castSucc) := by simpa only [Formula.raise, empty_rename] using under hz B
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have he := RawCodeProjectionRecursion.iteration_zero false _ _ _ _ hz1 (.conjL hB)
  have hout := RawCodeIterationTransport.step_input_subst true _ _ _ _ he (.conjR hB)
  simpa only [Formula.raise, step_rename] using hout

theorem zero_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w x z y : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) :
    Derives Γ ((get w x z y).iff (step true w x y)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact zero_forward w x z y (add hz _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact intro_get w x z y x (add (RawCodeIterationLaws.zero_value hZ false w x z hw hz) _) (.hyp (Or.inl rfl))

theorem successor_forward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w x t r s y : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (.mem r w)) (hs : Derives Γ (successor s r))
    (ht : Derives Γ (step false w x t)) (hy : Derives Γ (get w x s y)) : Derives Γ (get w t r y) := by
  let B := (iteration false w.castSucc x.castSucc s.castSucc (Fin.last m)).conj (step true w.castSucc (Fin.last m) y.castSucc)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hy
  have hZ1 := ZFContext.under hZ B
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw B
  have hs1 : Derives Δ (successor s.castSucc r.castSucc) := by simpa only [Formula.raise, successor_rename] using under hs B
  have ht1 : Derives Δ (step false w.castSucc x.castSucc t.castSucc) := by simpa only [Formula.raise, step_rename] using under ht B
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have htail := RawCodeShift.shift_forward hZ1 false _ _ _ _ _ _ hw1 (under hr B) hs1 ht1 (.conjL hB)
  have hout := intro_get _ _ _ _ _ htail (.conjR hB)
  simpa only [Formula.raise, get_rename] using hout

theorem successor_backward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w x t r s y : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (.mem r w)) (hs : Derives Γ (successor s r))
    (ht : Derives Γ (step false w x t)) (hy : Derives Γ (get w t r y)) : Derives Γ (get w x s y) := by
  let B := (iteration false w.castSucc t.castSucc r.castSucc (Fin.last m)).conj (step true w.castSucc (Fin.last m) y.castSucc)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hy
  have hZ1 := ZFContext.under hZ B
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw B
  have hs1 : Derives Δ (successor s.castSucc r.castSucc) := by simpa only [Formula.raise, successor_rename] using under hs B
  have ht1 : Derives Δ (step false w.castSucc x.castSucc t.castSucc) := by simpa only [Formula.raise, step_rename] using under ht B
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have htail := RawCodeShift.shift_backward hZ1 false _ _ _ _ _ _ hw1 (under hr B) hs1 ht1 (.conjL hB)
  have hout := intro_get _ _ _ _ _ htail (.conjR hB)
  simpa only [Formula.raise, get_rename] using hout

theorem successor_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w x t r s y : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (.mem r w)) (hs : Derives Γ (successor s r))
    (ht : Derives Γ (step false w x t)) : Derives Γ ((get w x s y).iff (get w t r y)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact successor_forward (ZFContext.add hZ _) _ _ _ _ _ _ (add hw _) (add hr _) (add hs _) (add ht _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact successor_backward (ZFContext.add hZ _) _ _ _ _ _ _ (add hw _) (add hr _) (add hs _) (add ht _) (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.RawCodeGetLaws
