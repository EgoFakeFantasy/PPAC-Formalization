import PPAC.Migration.Internal.GodelUnpairTransitions

/-! 两个分支的后继均实际取得自然解码；内部零见证和分量后继见证显式消去。 -/
namespace PPAC.Migration.Internal.GodelUnpairStep
open Source SourceAlgebra SourceLogic OmegaSyntax ZFArithmetic GodelPairSyntax GodelUnpairSyntax GodelUnpairArithmetic GodelUnpairTransitions
open NaturalAdditionBounds (below below_rename)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem lower_next {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b z p r : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w)) (hz : Derives Γ (empty z))
    (hab : Derives Γ (.mem a b)) (hp : Derives Γ (lower w a b p)) (hr : Derives Γ (successor r p)) : Derives Γ (preimage w r) := by
  have hzW := OmegaStructureAlgebra.zero_member w z (ZFContext.arithmetic hZ).base.extensionality hw hz
  have hs := Derives.impE (step_at w a (.conjL hw)) ha
  let S := (Formula.mem (Fin.last m) w.castSucc).conj (successor (Fin.last m) a.castSucc)
  let Ξ := Context.add S (Context.image Formula.raise Γ)
  change Derives Γ (.ex S) at hs
  apply Derives.exE (p := S) hs
  have hZ1 : ZFContext.Evidence Ξ := ZFContext.under hZ S
  have hw1 : Derives Ξ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw S
  have hz1 : Derives Ξ (empty z.castSucc) := by simpa only [Formula.raise, empty_rename] using under hz S
  have hp1 : Derives Ξ (lower w.castSucc a.castSucc b.castSucc p.castSucc) := by simpa only [Formula.raise, lower_rename] using under hp S
  have hr1 : Derives Ξ (successor r.castSucc p.castSucc) := by simpa only [Formula.raise, successor_rename] using under hr S
  have hS : Derives Ξ S := .hyp (Or.inl rfl)
  have htb := GodelPairArithmetic.successor_below hZ1 _ _ _ _ hw1 (under ha S) (under hb S) (.conjR hS) (under hab S)
  have hout : Derives Ξ (preimage w.castSucc r.castSucc) := by
    apply Derives.disjE htb
    · let E := Formula.equal (Fin.last m) b.castSucc
      let Δ := Context.add E Ξ
      have hZ2 : ZFContext.Evidence Δ := ZFContext.add hZ1 E
      have hsB := NaturalAdditionAlgebraLaws.successor_output_subst _ _ _ (Derives.hyp (Γ := Δ) (Or.inl rfl)) (add (.conjR hS) E)
      have hc := lower_turn hZ2 _ _ _ _ _ _ (add hw1 E) (add (under ha S) E) (add hz1 E) hsB (add hp1 E) (add hr1 E)
      exact intro_preimage _ _ _ _ (add (under hb S) E) (add (under hzW S) E) hc
    · let M := Formula.mem (Fin.last m) b.castSucc
      let Δ := Context.add M Ξ
      have hZ2 : ZFContext.Evidence Δ := ZFContext.add hZ1 M
      have hc := lower_inner hZ2 _ _ _ _ _ _ (add hw1 M) (add (under ha S) M) (add (.conjR hS) M) (Derives.hyp (Γ := Δ) (Or.inl rfl)) (add hp1 M) (add hr1 M)
      exact intro_preimage _ _ _ _ (add (.conjL hS) M) (add (under hb S) M) hc
  simpa only [Formula.raise, preimage_rename] using hout

theorem upper_next {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b z p r : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w)) (hz : Derives Γ (empty z))
    (hab : Derives Γ (Formula.mem a b).neg) (hp : Derives Γ (upper w a b p)) (hr : Derives Γ (successor r p)) : Derives Γ (preimage w r) := by
  have hzW := OmegaStructureAlgebra.zero_member w z (ZFContext.arithmetic hZ).base.extensionality hw hz
  have hba := GodelPairIntervals.reverse_below hZ _ _ _ hw ha hb hab
  have hs := Derives.impE (step_at w b (.conjL hw)) hb
  let S := (Formula.mem (Fin.last m) w.castSucc).conj (successor (Fin.last m) b.castSucc)
  let Ξ := Context.add S (Context.image Formula.raise Γ)
  change Derives Γ (.ex S) at hs
  apply Derives.exE (p := S) hs
  have hZ1 : ZFContext.Evidence Ξ := ZFContext.under hZ S
  have hw1 : Derives Ξ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw S
  have hz1 : Derives Ξ (empty z.castSucc) := by simpa only [Formula.raise, empty_rename] using under hz S
  have hp1 : Derives Ξ (upper w.castSucc a.castSucc b.castSucc p.castSucc) := by simpa only [Formula.raise, upper_rename] using under hp S
  have hr1 : Derives Ξ (successor r.castSucc p.castSucc) := by simpa only [Formula.raise, successor_rename] using under hr S
  have hba1 : Derives Ξ (below b.castSucc a.castSucc) := by simpa only [Formula.raise, below_rename] using under hba S
  have hS : Derives Ξ S := .hyp (Or.inl rfl)
  have hout : Derives Ξ (preimage w.castSucc r.castSucc) := by
    apply Derives.disjE hba1
    · let E := Formula.equal b.castSucc a.castSucc
      let Δ := Context.add E Ξ
      have hZ2 : ZFContext.Evidence Δ := ZFContext.add hZ1 E
      have hsA := successor_base_subst _ _ _ (Derives.hyp (Γ := Δ) (Or.inl rfl)) (add (.conjR hS) E)
      have hpA := upper_right_subst _ _ _ _ _ (Derives.hyp (Γ := Δ) (Or.inl rfl)) (add hp1 E)
      have hc := upper_turn hZ2 _ _ _ _ _ _ (add hw1 E) (add (under ha S) E) (add hz1 E) hsA hpA (add hr1 E)
      exact intro_preimage _ _ _ _ (add (under hzW S) E) (add (.conjL hS) E) hc
    · let M := Formula.mem b.castSucc a.castSucc
      let Δ := Context.add M Ξ
      have hZ2 : ZFContext.Evidence Δ := ZFContext.add hZ1 M
      have hta := GodelPairArithmetic.successor_below hZ2 _ _ _ _ (add hw1 M) (add (under hb S) M) (add (under ha S) M)
        (add (.conjR hS) M) (Derives.hyp (Γ := Δ) (Or.inl rfl))
      have hc := upper_inner hZ2 _ _ _ _ _ _ (add hw1 M) (add (under hb S) M) (add (.conjR hS) M) hta (add hp1 M) (add hr1 M)
      exact intro_preimage _ _ _ _ (add (under ha S) M) (add (.conjL hS) M) hc
  simpa only [Formula.raise, preimage_rename] using hout

theorem code_next {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b p r : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w))
    (hp : Derives Γ (code w a b p)) (hr : Derives Γ (successor r p)) : Derives Γ (preimage w r) := by
  let Z := (Formula.mem (Fin.last m) w.castSucc).conj (empty (Fin.last m))
  let Ξ := Context.add Z (Context.image Formula.raise Γ)
  have hz : Derives Γ (.ex Z) := .conjL (.conjL hw)
  apply Derives.exE (p := Z) hz
  have hZ1 : ZFContext.Evidence Ξ := ZFContext.under hZ Z
  have hw1 : Derives Ξ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw Z
  have hp1 : Derives Ξ (code w.castSucc a.castSucc b.castSucc p.castSucc) := by simpa only [Formula.raise, code_rename] using under hp Z
  have hr1 : Derives Ξ (successor r.castSucc p.castSucc) := by simpa only [Formula.raise, successor_rename] using under hr Z
  have hZ : Derives Ξ Z := .hyp (Or.inl rfl)
  have hout : Derives Ξ (preimage w.castSucc r.castSucc) := by
    apply Derives.disjE hp1
    · exact lower_next (ZFContext.add hZ1 _) _ _ _ _ _ _ (add hw1 _) (add (under ha Z) _) (add (under hb Z) _) (add (.conjR hZ) _)
        (.conjL (.hyp (Or.inl rfl))) (.conjR (.hyp (Or.inl rfl))) (add hr1 _)
    · exact upper_next (ZFContext.add hZ1 _) _ _ _ _ _ _ (add hw1 _) (add (under ha Z) _) (add (under hb Z) _) (add (.conjR hZ) _)
        (.conjL (.hyp (Or.inl rfl))) (.conjR (.hyp (Or.inl rfl))) (add hr1 _)
  simpa only [Formula.raise, preimage_rename] using hout

theorem successor_preimage {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w p r : Fin m)
    (hw : Derives Γ (omega w)) (hp : Derives Γ (preimage w p)) (hr : Derives Γ (successor r p)) : Derives Γ (preimage w r) := by
  let W := witness w.castSucc.castSucc p.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
  let Δ := Context.add W (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_preimage w p _ hp
  have hZ2 : ZFContext.Evidence Δ := ZFContext.under_two hZ W
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using OrderedPairElimination.under_two hw W
  have hr2 : Derives Δ (successor r.castSucc.castSucc p.castSucc.castSucc) := by simpa only [Formula.raise, successor_rename] using OrderedPairElimination.under_two hr W
  have hW : Derives Δ W := .hyp (Or.inl rfl)
  have hout := code_next hZ2 _ _ _ _ _ hw2 (.conjL (.conjL hW)) (.conjR (.conjL hW)) (.conjR hW) hr2
  simpa only [Formula.raise, preimage_rename] using hout
end PPAC.Migration.Internal.GodelUnpairStep
