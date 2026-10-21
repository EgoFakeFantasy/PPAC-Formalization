import PPAC.Migration.Internal.StructuralListCheckSyntax

/-! 实际终端执行的零点、原tail单步前置和严格较小尾码上的归纳步。 -/
namespace PPAC.Migration.Internal.StructuralListCheckTerminationPoint
open Source SourceAlgebra SourceLogic OmegaSyntax StructuralListSyntax StructuralListProjectionSyntax StructuralListCheckSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem at_terminal {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (terminal w n)) : Derives Γ (eventually w n) := by
  let Z := (Formula.mem (Fin.last m) w.castSucc).conj (empty (Fin.last m))
  let Δ := Context.add Z (Context.image Formula.raise Γ)
  have hz : Derives Γ (.ex Z) := .conjL (.conjL hw)
  apply Derives.exE (p := Z) hz
  have hZ1 : ZFContext.Evidence Δ := ZFContext.under hZ Z
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw Z
  have ht1 : Derives Δ (terminal w.castSucc n.castSucc) := by simpa only [Formula.raise, terminal_rename] using under ht Z
  have hZZ : Derives Δ Z := .hyp (Or.inl rfl)
  have hi := StructuralListPositionLogic.zero_value hZ1 false w.castSucc n.castSucc (Fin.last m) hw1 (.conjR hZZ)
  have hout := intro_eventually _ _ _ _ (.conjL hZZ) hi ht1
  simpa only [Formula.raise, eventually_rename] using hout

theorem step_extension {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n t : Fin m)
    (hw : Derives Γ (omega w)) (hs : Derives Γ (step false w n t)) (he : Derives Γ (eventually w t)) :
    Derives Γ (eventually w n) := by
  let R := (Formula.mem (Fin.last m) w.castSucc).conj (occurs w.castSucc t.castSucc (Fin.last m))
  let Ξ := Context.add R (Context.image Formula.raise Γ)
  change Derives Γ (.ex R) at he
  apply Derives.exE (p := R) he
  have hR : Derives Ξ R := .hyp (Or.inl rfl)
  let B := (iteration false w.castSucc.castSucc t.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).conj
    (terminal w.castSucc.castSucc (Fin.last (m+1)))
  let Ξ2 := Context.add B (Context.image Formula.raise Ξ)
  have hb : Derives Ξ (.ex B) := .conjR hR
  apply Derives.exE (p := B) hb
  have hw2 : Derives Ξ2 (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using under (under hw R) B
  have hr2 : Derives Ξ2 (.mem (Fin.last m).castSucc w.castSucc.castSucc) := under (.conjL hR) B
  have hx := Derives.impE (step_at _ _ (.conjL hw2)) hr2
  let S := (Formula.mem (Fin.last (m+2)) w.castSucc.castSucc.castSucc).conj (successor (Fin.last (m+2)) (Fin.last m).castSucc.castSucc)
  let Δ := Context.add S (Context.image Formula.raise Ξ2)
  change Derives Ξ2 (.ex S) at hx
  apply Derives.exE (p := S) hx
  have hZ3 : ZFContext.Evidence Δ := ZFContext.under (ZFContext.under (ZFContext.under hZ R) B) S
  have hw3 : Derives Δ (omega w.castSucc.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw2 S
  have hs3 : Derives Δ (step false w.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc t.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, step_rename] using under (under (under hs R) B) S
  have hB : Derives Ξ2 B := .hyp (Or.inl rfl)
  have hB3 : Derives Δ ((iteration false w.castSucc.castSucc.castSucc t.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc).conj
      (terminal w.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc)) := by
    simpa only [B, Formula.raise, Formula.rename, iteration_rename, terminal_rename] using under hB S
  have hS : Derives Δ S := .hyp (Or.inl rfl)
  have hi := StructuralListShift.shift_backward hZ3 false _ _ _ _ _ _ hw3 (under hr2 S) (.conjR hS) hs3 (.conjL hB3)
  have hout := intro_eventually _ _ _ _ (.conjL hS) hi (.conjR hB3)
  simpa only [Formula.raise, eventually_rename] using hout

theorem off_cons {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (hasCons false w n).neg) : Derives Γ (eventually w n) := by
  let Z := (Formula.mem (Fin.last m) w.castSucc).conj (empty (Fin.last m))
  let Δ := Context.add Z (Context.image Formula.raise Γ)
  have hz : Derives Γ (.ex Z) := .conjL (.conjL hw)
  apply Derives.exE (p := Z) hz
  have hZ1 : ZFContext.Evidence Δ := ZFContext.under hZ Z
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw Z
  have hc1 : Derives Δ (hasCons false w.castSucc n.castSucc).neg := by simpa only [Formula.raise, Formula.neg, Formula.rename, hasCons_rename] using under hc Z
  have hZZ : Derives Δ Z := .hyp (Or.inl rfl)
  have hstep : Derives Δ (step false w.castSucc n.castSucc (Fin.last m)) := .disjR (.conjI hc1 (.conjR hZZ))
  have he := at_terminal hZ1 _ _ hw1 (.disjL (.conjR hZZ))
  have hout := step_extension hZ1 _ _ _ hw1 hstep he
  simpa only [Formula.raise, eventually_rename] using hout

theorem from_earlier {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (earlier w n)) : Derives Γ (eventually w n) := by
  apply SourcePropositional.by_cases (hasCons false w n) (eventually w n)
  · let C := hasCons false w n
    let Γc := Context.add C Γ
    let T := selected false w.castSucc n.castSucc (Fin.last m)
    let Ξ := Context.add T (Context.image Formula.raise Γc)
    have ht : Derives Γc (.ex T) := .hyp (Or.inl rfl)
    apply Derives.exE (p := T) ht
    let H := body false w.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
    let Δ := Context.add H (Context.image Formula.raise Ξ)
    have hh : Derives Ξ (.ex H) := .hyp (Or.inl rfl)
    apply Derives.exE (p := H) hh
    have hZ2 : ZFContext.Evidence Δ := ZFContext.under (ZFContext.under (ZFContext.add hZ C) T) H
    have lift {p : Formula m} (hp : Derives Γ p) : Derives Δ p.raise.raise := under (under (add hp C) T) H
    have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using lift hw
    have hi2 : Derives Δ (earlier w.castSucc.castSucc n.castSucc.castSucc) := by simpa only [Formula.raise, earlier_rename] using lift hi
    have hH : Derives Δ H := .hyp (Or.inl rfl)
    have hb := StructuralConsCore.components hZ2 _ _ _ _ hw2 (.conjR (.conjL hH)) (.conjL (.conjL hH)) (.conjR hH)
    have he := earlier_at _ _ _ hi2 (.conjL (.conjL hH)) (.conjR hb)
    have hstep : Derives Δ (step false w.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc) :=
      .disjL (intro_selected false _ _ _ _ hH)
    have hout := step_extension hZ2 _ _ _ hw2 hstep he
    simpa only [Formula.raise, eventually_rename] using hout
  · exact off_cons (ZFContext.add hZ _) _ _ (add hw _) (.hyp (Or.inl rfl))
end PPAC.Migration.Internal.StructuralListCheckTerminationPoint
