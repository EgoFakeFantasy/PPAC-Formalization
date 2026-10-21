import PPAC.Migration.IterationRangeSeed

/-! 精确末值集合对取并递推封闭；全部索引和输出见证保留在对象层。 -/
namespace PPAC.Migration.IterationRangeClosed
open Source SourceAlgebra SourceLogic OmegaSyntax InsertSyntax IterationValueSyntax IterationRangeSyntax

theorem from_index {m} {Γ : Context m} (hA : IterationContext.Evidence Γ) (c w z a n r : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hc : Derives Γ (IterationValueSyntax.range c w z a))
    (hn : Derives Γ (.mem n w)) (hr : Derives Γ (value n z a r)) : Derives Γ (closedFiber c r) := by
  have hs := Derives.impE (step_at w n (.conjL hw)) hn
  let S := (Formula.mem (Fin.last m) w.castSucc).conj (successor (Fin.last m) n.castSucc)
  let Γs := Context.add S (Context.image Formula.raise Γ)
  change Derives Γ (.ex S) at hs
  apply Derives.exE (p := S) hs
  have hAS := IterationContext.under hA S
  have hwS : Derives Γs (omega w.castSucc) := by
    simpa only [Formula.raise, omega_rename] using under hw S
  have hzS : Derives Γs (empty z.castSucc) := by
    simpa only [Formula.raise, empty_rename] using under hz S
  have hcS : Derives Γs (IterationValueSyntax.range c.castSucc w.castSucc z.castSucc a.castSucc) := by
    simpa only [Formula.raise, range_rename] using under hc S
  have hnS : Derives Γs (.mem n.castSucc w.castSucc) := under hn S
  have hrS : Derives Γs (value n.castSucc z.castSucc a.castSucc r.castSucc) := by
    simpa only [Formula.raise, value_rename] using under hr S
  have hS : Derives Γs S := .hyp (Or.inl rfl)
  have he := IterationValueExistence.exists_at hAS (Fin.last m) z.castSucc a.castSucc w.castSucc hwS hzS (.conjL hS)
  let T := value (Fin.last m).castSucc z.castSucc.castSucc a.castSucc.castSucc (Fin.last (m+1))
  let Γt := Context.add T (Context.image Formula.raise Γs)
  change Derives Γs (.ex T) at he
  apply Derives.exE (p := T) he
  have hAT := IterationContext.under hAS T
  have hwT : Derives Γt (omega w.castSucc.castSucc) := by
    simpa only [Formula.raise, omega_rename] using under hwS T
  have hzT : Derives Γt (empty z.castSucc.castSucc) := by
    simpa only [Formula.raise, empty_rename] using under hzS T
  have hcT : Derives Γt (IterationValueSyntax.range c.castSucc.castSucc w.castSucc.castSucc z.castSucc.castSucc a.castSucc.castSucc) := by
    simpa only [Formula.raise, range_rename] using under hcS T
  have hnT : Derives Γt (.mem n.castSucc.castSucc w.castSucc.castSucc) := under hnS T
  have hrT : Derives Γt (value n.castSucc.castSucc z.castSucc.castSucc a.castSucc.castSucc r.castSucc.castSucc) := by
    simpa only [Formula.raise, value_rename] using under hrS T
  have hST : Derives Γt ((Formula.mem (Fin.last m).castSucc w.castSucc.castSucc).conj
      (successor (Fin.last m).castSucc n.castSucc.castSucc)) := by
    simpa only [Formula.raise, S, Formula.rename, successor_rename] using under hS T
  have hT : Derives Γt T := .hyp (Or.inl rfl)
  have hu := IterationValueStep.adjacent_values hAT n.castSucc.castSucc (Fin.last m).castSucc
    z.castSucc.castSucc a.castSucc.castSucc w.castSucc.castSucc r.castSucc.castSucc (Fin.last (m+1))
    hwT hzT hnT (.conjR hST) hrT hT
  have hm := member_from_value c.castSucc.castSucc w.castSucc.castSucc z.castSucc.castSucc a.castSucc.castSucc
    (Fin.last m).castSucc (Fin.last (m+1)) hcT (.conjL hST) hT
  have hres : Derives Γt (closedFiber c.castSucc.castSucc r.castSucc.castSucc) := by
    apply Derives.exI (Fin.last (m+1))
    simpa only [Formula.instantiate, Formula.rename, unionOf_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
      using Derives.conjI hm hu
  simpa only [Formula.raise, closedFiber_rename] using hres

theorem closed_range {m} {Γ : Context m} (hA : IterationContext.Evidence Γ) (c w z a : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hc : Derives Γ (IterationValueSyntax.range c w z a)) :
    Derives Γ (closedUnion c) := by
  apply Derives.allI
  have hA' := IterationContext.rename hA Fin.castSucc
  have hw' : Derives (Context.image Formula.raise Γ) (omega w.castSucc) := by
    simpa only [Formula.raise, omega_rename] using Derives.rename Fin.castSucc hw
  have hz' : Derives (Context.image Formula.raise Γ) (empty z.castSucc) := by
    simpa only [Formula.raise, empty_rename] using Derives.rename Fin.castSucc hz
  have hc' : Derives (Context.image Formula.raise Γ) (IterationValueSyntax.range c.castSucc w.castSucc z.castSucc a.castSucc) := by
    simpa only [Formula.raise, range_rename] using Derives.rename Fin.castSucc hc
  apply Derives.impI
  let M := Formula.mem (Fin.last m) c.castSucc
  let Δ := Context.add M (Context.image Formula.raise Γ)
  have hI : Derives Δ (imageValue w.castSucc z.castSucc a.castSucc (Fin.last m)) :=
    .impE (.conjL (range_at c.castSucc w.castSucc z.castSucc a.castSucc (Fin.last m) (add hc' M))) (.hyp (Or.inl rfl))
  let N := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj
    (value (Fin.last (m+1)) z.castSucc.castSucc a.castSucc.castSucc (Fin.last m).castSucc)
  let Γn := Context.add N (Context.image Formula.raise Δ)
  change Derives Δ (.ex N) at hI
  apply Derives.exE (p := N) hI
  have hAN := IterationContext.under (IterationContext.add hA' M) N
  have hwN : Derives Γn (omega w.castSucc.castSucc) := by
    simpa only [Formula.raise, omega_rename] using under (add hw' M) N
  have hzN : Derives Γn (empty z.castSucc.castSucc) := by
    simpa only [Formula.raise, empty_rename] using under (add hz' M) N
  have hcN : Derives Γn (IterationValueSyntax.range c.castSucc.castSucc w.castSucc.castSucc z.castSucc.castSucc a.castSucc.castSucc) := by
    simpa only [Formula.raise, range_rename] using under (add hc' M) N
  have hN : Derives Γn N := .hyp (Or.inl rfl)
  have hr := from_index hAN c.castSucc.castSucc w.castSucc.castSucc z.castSucc.castSucc a.castSucc.castSucc
    (Fin.last (m+1)) (Fin.last m).castSucc hwN hzN hcN (.conjL hN) (.conjR hN)
  simpa only [Formula.raise, closedFiber_rename] using hr
end PPAC.Migration.IterationRangeClosed
