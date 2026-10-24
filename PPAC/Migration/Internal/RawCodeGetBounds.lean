import PPAC.Migration.Internal.RawCodeGetBoundsSyntax

/-! 原完整Separation与内部omega归纳证明get值界，覆盖全部内部自然索引。 -/
namespace PPAC.Migration.Internal.RawCodeGetBounds
open Source SourceAlgebra SourceLogic OmegaSyntax RawCodeGetBoundsSyntax
open NaturalAdditionBounds (below below_rename)
open PairingProjectionBounds (of_eq)
open ReplacementPredicates (paramsUp)

theorem correct_zero {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) : Derives Γ (correct w z) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let E := (Formula.mem (Fin.last m).castSucc w.castSucc.castSucc).conj
    (RawCodeGetSyntax.get w.castSucc.castSucc (Fin.last m).castSucc z.castSucc.castSucc (Fin.last (m+1)))
  let Δ := Context.add E (Context.image Formula.raise (Context.image Formula.raise Γ))
  have hZ2 := ZFContext.add (ZFContext.rename (ZFContext.rename hZ Fin.castSucc) Fin.castSucc) E
  have lift {P : Formula m} (h : Derives Γ P) : Derives Δ P.raise.raise := add (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc h)) E
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (lift hw)
  have hz2 : Derives Δ (empty z.castSucc.castSucc) := of_eq (by simp only [Formula.raise, empty_rename]) (lift hz)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  exact RawCodeProjectionBounds.step_bound hZ2 true _ _ _ hw2 (.conjL hE)
    (RawCodeGetLaws.zero_forward _ _ _ _ hz2 (.conjR hE))

theorem correct_successor {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w i s : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (.mem i w)) (hs : Derives Γ (successor s i))
    (hc : Derives Γ (correct w i)) : Derives Γ (correct w s) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let E := (Formula.mem (Fin.last m).castSucc w.castSucc.castSucc).conj
    (RawCodeGetSyntax.get w.castSucc.castSucc (Fin.last m).castSucc s.castSucc.castSucc (Fin.last (m+1)))
  let Ξ := Context.add E (Context.image Formula.raise (Context.image Formula.raise Γ))
  have hZ2 := ZFContext.add (ZFContext.rename (ZFContext.rename hZ Fin.castSucc) Fin.castSucc) E
  have lift {P : Formula m} (h : Derives Γ P) : Derives Ξ P.raise.raise := add (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc h)) E
  have hw2 : Derives Ξ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (lift hw)
  have hi2 : Derives Ξ (.mem i.castSucc.castSucc w.castSucc.castSucc) := lift hi
  have hs2 : Derives Ξ (successor s.castSucc.castSucc i.castSucc.castSucc) := of_eq (by simp only [Formula.raise, successor_rename]) (lift hs)
  have hc2 : Derives Ξ (correct w.castSucc.castSucc i.castSucc.castSucc) := of_eq (by simp only [Formula.raise, correct_rename]) (lift hc)
  have hE : Derives Ξ E := .hyp (Or.inl rfl)
  let B := RawCodeProjectionSyntax.step false w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+2))
  let Δ := Context.add B (Context.image Formula.raise Ξ)
  apply Derives.exE (p := B) (RawCodeProjection.exists_step false w.castSucc.castSucc (Fin.last m).castSucc hw2)
  have hZ3 := ZFContext.under hZ2 B
  have hw3 := of_eq (omega_rename w.castSucc.castSucc Fin.castSucc) (under hw2 B)
  have hs3 := of_eq (successor_rename s.castSucc.castSucc i.castSucc.castSucc Fin.castSucc) (under hs2 B)
  have hc3 := of_eq (correct_rename w.castSucc.castSucc i.castSucc.castSucc Fin.castSucc) (under hc2 B)
  have hx3 : Derives Δ (.mem (Fin.last m).castSucc.castSucc w.castSucc.castSucc.castSucc) := under (.conjL hE) B
  have hy3 : Derives Δ (RawCodeGetSyntax.get w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc s.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc) :=
    of_eq (RawCodeGetSyntax.get_rename _ _ _ _ Fin.castSucc) (under (.conjR hE) B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ht := RawCodeProjection.range_point hZ3 false _ _ _ hw3 hB
  have hget := RawCodeGetLaws.successor_forward hZ3 _ _ _ _ _ _ hw3 (under hi2 B) hs3 hB hy3
  have hyb := Derives.impE (at_value _ _ (Fin.last (m+2)) (Fin.last (m+1)).castSucc hc3) (Derives.conjI ht hget)
  have htb := RawCodeProjectionBounds.step_bound hZ3 false _ _ _ hw3 hx3 hB
  have ho := NaturalOrderBasic.transitive hZ3 _ _ _ _ hw3 hx3 hyb htb
  exact of_eq (below_rename (Fin.last (m+1)) (Fin.last m).castSucc Fin.castSucc).symm ho

theorem base {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (ρ : Fin 1 → Fin m)
    (hw : Derives Γ (omega (ρ 0))) : Derives Γ (OmegaInductionSyntax.base RawCodeGetBoundsSyntax.matrix ρ) := by
  simp only [OmegaInductionSyntax.base, RawCodeGetBoundsSyntax.matrix_pred, paramsUp]
  apply Derives.allI
  apply Derives.impI
  let B := empty (Fin.last m)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  have hw1 : Derives Δ (omega (ρ 0).castSucc) := of_eq (omega_rename (ρ 0) Fin.castSucc) (under hw B)
  exact correct_zero (ZFContext.under hZ B) _ _ hw1 (.hyp (Or.inl rfl))

theorem step {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (ρ : Fin 1 → Fin m)
    (hw : Derives Γ (omega (ρ 0))) : Derives Γ (OmegaInductionSyntax.step RawCodeGetBoundsSyntax.matrix ρ (ρ 0)) := by
  simp only [OmegaInductionSyntax.step, RawCodeGetBoundsSyntax.matrix_pred, paramsUp]
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let M := Formula.mem (Fin.last m).castSucc (ρ 0).castSucc.castSucc
  let C := correct (ρ 0).castSucc.castSucc (Fin.last m).castSucc
  let S := successor (Fin.last (m+1)) (Fin.last m).castSucc
  let Δ := Context.add S (Context.add C (Context.add M (Context.image Formula.raise (Context.image Formula.raise Γ))))
  have hZ2 := ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.rename (ZFContext.rename hZ Fin.castSucc) Fin.castSucc) M) C) S
  have hw2 : Derives Δ (omega (ρ 0).castSucc.castSucc) := by
    simpa only [Formula.raise, omega_rename] using add (add (add (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hw)) M) C) S
  exact correct_successor hZ2 _ _ _ hw2 (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inl rfl)) (.hyp (Or.inr (Or.inl rfl)))

theorem all_correct {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) (hw : Derives Γ (omega w)) :
    Derives Γ (.all ((Formula.mem (Fin.last m) w.castSucc).imp (correct w.castSucc (Fin.last m)))) := by
  have hh := OmegaInduction.induction_on_omega RawCodeGetBoundsSyntax.matrix (fun _ : Fin 1 => w) w
    (ZFContext.separation hZ RawCodeGetBoundsSyntax.matrix) hw (base hZ (fun _ => w) hw) (step hZ (fun _ => w) hw)
  simpa only [OmegaInductionSyntax.holds, RawCodeGetBoundsSyntax.matrix_pred, paramsUp] using hh

theorem at_index {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w i : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (.mem i w)) : Derives Γ (correct w i) := by
  have ht : Derives Γ ((Formula.mem i w).imp (correct w i)) := by
    simpa only [Formula.instantiate, Formula.rename, correct_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.allE i (all_correct hZ w hw)
  exact .impE ht hi


theorem bound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w x i y : Fin m)
    (hw : Derives Γ (omega w)) (hx : Derives Γ (.mem x w)) (hi : Derives Γ (.mem i w))
    (hy : Derives Γ (RawCodeGetSyntax.get w x i y)) : Derives Γ (below y x) :=
  .impE (at_value w i x y (at_index hZ w i hw hi)) (.conjI hx hy)

end PPAC.Migration.Internal.RawCodeGetBounds
