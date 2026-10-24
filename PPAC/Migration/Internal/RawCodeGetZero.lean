import PPAC.Migration.Internal.RawCodeGetZeroSyntax

/-! 原Separation与对象ω归纳证明输入零码在全部内部自然索引精确返回零。 -/
namespace PPAC.Migration.Internal.RawCodeGetZero
open Source SourceAlgebra SourceLogic OmegaSyntax RawCodeGetSyntax RawCodeGetZeroSyntax
open ReplacementPredicates (paramsUp)

theorem correct_zero {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z i : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hi : Derives Γ (empty i)) : Derives Γ (correct w z i) := by
  apply Derives.allI
  apply Derives.impI
  let B := get w.castSucc z.castSucc i.castSucc (Fin.last m)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  have hZ1 := ZFContext.under hZ B
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw B
  have hz1 : Derives Δ (empty z.castSucc) := by simpa only [Formula.raise, empty_rename] using under hz B
  have hi1 : Derives Δ (empty i.castSucc) := by simpa only [Formula.raise, empty_rename] using under hi B
  have hhead := RawCodeGetLaws.zero_forward _ _ _ _ hi1 (.hyp (Or.inl rfl))
  exact RawCodeProjection.zero hZ1 true _ _ _ hw1 hz1 hhead

theorem correct_successor {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z r s : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hr : Derives Γ (.mem r w))
    (hs : Derives Γ (successor s r)) (hc : Derives Γ (correct w z r)) : Derives Γ (correct w z s) := by
  apply Derives.allI
  apply Derives.impI
  let B := get w.castSucc z.castSucc s.castSucc (Fin.last m)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  have hZ1 := ZFContext.under hZ B
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw B
  have hz1 : Derives Δ (empty z.castSucc) := by simpa only [Formula.raise, empty_rename] using under hz B
  have hr1 : Derives Δ (.mem r.castSucc w.castSucc) := under hr B
  have hs1 : Derives Δ (successor s.castSucc r.castSucc) := by simpa only [Formula.raise, successor_rename] using under hs B
  have hc1 : Derives Δ (correct w.castSucc z.castSucc r.castSucc) := by simpa only [Formula.raise, correct_rename] using under hc B
  have htail := RawCodeProjection.zero_value hZ1 false _ _ hw1 hz1
  have hprev := RawCodeGetLaws.successor_forward hZ1 _ _ _ _ _ _ hw1 hr1 hs1 htail (.hyp (Or.inl rfl))
  exact at_value _ _ _ _ hc1 hprev

theorem base {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (ρ : Fin 2 → Fin m)
    (hw : Derives Γ (omega (ρ 0))) (hz : Derives Γ (empty (ρ 1))) : Derives Γ (OmegaInductionSyntax.base RawCodeGetZeroSyntax.matrix ρ) := by
  simp only [OmegaInductionSyntax.base, RawCodeGetZeroSyntax.matrix_pred, paramsUp]
  apply Derives.allI
  apply Derives.impI
  let B := empty (Fin.last m)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  have hw1 : Derives Δ (omega (ρ 0).castSucc) := by simpa only [Formula.raise, omega_rename] using under hw B
  have hz1 : Derives Δ (empty (ρ 1).castSucc) := by simpa only [Formula.raise, empty_rename] using under hz B
  exact correct_zero (ZFContext.under hZ B) _ _ _ hw1 hz1 (.hyp (Or.inl rfl))

theorem step {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (ρ : Fin 2 → Fin m)
    (hw : Derives Γ (omega (ρ 0))) (hz : Derives Γ (empty (ρ 1))) : Derives Γ (OmegaInductionSyntax.step RawCodeGetZeroSyntax.matrix ρ (ρ 0)) := by
  simp only [OmegaInductionSyntax.step, RawCodeGetZeroSyntax.matrix_pred, paramsUp]
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let M := Formula.mem (Fin.last m).castSucc (ρ 0).castSucc.castSucc
  let C := correct (ρ 0).castSucc.castSucc (ρ 1).castSucc.castSucc (Fin.last m).castSucc
  let S := successor (Fin.last (m+1)) (Fin.last m).castSucc
  let Δ := Context.add S (Context.add C (Context.add M (Context.image Formula.raise (Context.image Formula.raise Γ))))
  have hZ2 := ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.rename (ZFContext.rename hZ Fin.castSucc) Fin.castSucc) M) C) S
  have lift {P : Formula m} (hp : Derives Γ P) : Derives Δ P.raise.raise := add (add (add (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hp)) M) C) S
  have hw2 : Derives Δ (omega (ρ 0).castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using lift hw
  have hz2 : Derives Δ (empty (ρ 1).castSucc.castSucc) := by simpa only [Formula.raise, empty_rename] using lift hz
  exact correct_successor hZ2 _ _ _ _ hw2 hz2 (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inl rfl)) (.hyp (Or.inr (Or.inl rfl)))

theorem all_correct {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (ρ : Fin 2 → Fin m)
    (hw : Derives Γ (omega (ρ 0))) (hz : Derives Γ (empty (ρ 1))) :
    Derives Γ (.all ((Formula.mem (Fin.last m) (ρ 0).castSucc).imp (correct (ρ 0).castSucc (ρ 1).castSucc (Fin.last m)))) := by
  have hh := OmegaInduction.induction_on_omega RawCodeGetZeroSyntax.matrix ρ (ρ 0) (ZFContext.separation hZ RawCodeGetZeroSyntax.matrix) hw (base hZ ρ hw hz) (step hZ ρ hw hz)
  simpa only [OmegaInductionSyntax.holds, RawCodeGetZeroSyntax.matrix_pred, paramsUp] using hh

theorem all_indices {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) :
    Derives Γ (.all ((Formula.mem (Fin.last m) w.castSucc).imp (correct w.castSucc z.castSucc (Fin.last m)))) := by
  have h0 : Source.SetLanguage.args2 w z (0 : Fin 2) = w := rfl
  have h1 : Source.SetLanguage.args2 w z (1 : Fin 2) = z := by
    change Fin.cases w (Source.SetLanguage.args1 z) (Fin.succ (0 : Fin 1)) = z
    rw [Fin.cases_succ]
    rfl
  simpa only [h0, h1] using all_correct hZ (Source.SetLanguage.args2 w z) hw hz

theorem at_index {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z i : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hi : Derives Γ (.mem i w)) : Derives Γ (correct w z i) := by
  have ht : Derives Γ ((Formula.mem i w).imp (correct w z i)) := by
    simpa only [Formula.instantiate, Formula.rename, correct_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.allE i (all_indices hZ w z hw hz)
  exact .impE ht hi

theorem sound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z i y : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hi : Derives Γ (.mem i w)) (hy : Derives Γ (get w z i y)) : Derives Γ (empty y) :=
  at_value w z i y (at_index hZ w z i hw hz hi) hy

theorem checked_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z i y : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hi : Derives Γ (.mem i w)) : Derives Γ ((get w z i y).iff (empty y)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact sound (ZFContext.add hZ _) w z i y (add hw _) (add hz _) (add hi _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    let E := empty y
    let B := (Formula.mem (Fin.last m) w.castSucc).conj (get w.castSucc z.castSucc i.castSucc (Fin.last m))
    let Δ := Context.add B (Context.image Formula.raise (Context.add E Γ))
    apply Derives.exE (p := B) (RawCodeGetValues.exists_value (ZFContext.add hZ E) w z i (add hw E) (add hi E))
    have hZ1 := ZFContext.under (ZFContext.add hZ E) B
    have lift {P : Formula m} (hp : Derives Γ P) : Derives Δ P.raise := under (add hp E) B
    have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using lift hw
    have hz1 : Derives Δ (empty z.castSucc) := by simpa only [Formula.raise, empty_rename] using lift hz
    have hy1 : Derives Δ (empty y.castSucc) := by simpa only [E, Formula.raise, empty_rename] using under (Derives.hyp (Γ := Context.add E Γ) (Or.inl rfl)) B
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hzero := sound hZ1 _ _ _ _ hw1 hz1 (lift hi) (.conjR hB)
    have he := OmegaUniversal.empty_unique (Fin.last m) y.castSucc (ZFContext.arithmetic hZ1).base.extensionality hzero hy1
    have hout := output_subst _ _ _ _ _ he (.conjR hB)
    simpa only [Formula.raise, get_rename] using hout

end PPAC.Migration.Internal.RawCodeGetZero
