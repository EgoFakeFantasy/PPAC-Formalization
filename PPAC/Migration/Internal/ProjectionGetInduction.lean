import PPAC.Migration.Internal.ProjectionGetSuccessor

/-! 原Separation和内部ω归纳消去get全部正确性IH；全候选查询双条件保留自然输入／索引域。 -/
namespace PPAC.Migration.Internal.ProjectionGetInduction
open Source SourceAlgebra SourceLogic OmegaSyntax ProjectionGetInductionSyntax
open SyntaxRenameQuerySyntax (of_eq)
open ReplacementPredicates (paramsUp)

theorem correct_zero {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) : Derives Γ (correct w z) := by
  apply Derives.allI
  apply Derives.allI
  let Δ := Context.image Formula.raise (Context.image Formula.raise Γ)
  have lift {P : Formula m} (h : Derives Γ P) : Derives Δ P.raise.raise := Derives.rename Fin.castSucc (Derives.rename Fin.castSucc h)
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (lift hw)
  have hz2 : Derives Δ (empty z.castSucc.castSucc) := of_eq (by simp only [Formula.raise, empty_rename]) (lift hz)
  exact ProjectionGetZeroIndex.checked_iff (ZFContext.rename (ZFContext.rename hZ Fin.castSucc) Fin.castSucc)
    w.castSucc.castSucc (Fin.last m).castSucc z.castSucc.castSucc (Fin.last (m+1)) hw2 hz2

theorem base {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (ρ : Fin 1 → Fin m)
    (hw : Derives Γ (omega (ρ 0))) : Derives Γ (OmegaInductionSyntax.base ProjectionGetInductionSyntax.matrix ρ) := by
  simp only [OmegaInductionSyntax.base, ProjectionGetInductionSyntax.matrix_pred, paramsUp]
  apply Derives.allI
  apply Derives.impI
  let B := empty (Fin.last m)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  have hw1 : Derives Δ (omega (ρ 0).castSucc) := of_eq (omega_rename (ρ 0) Fin.castSucc) (under hw B)
  exact correct_zero (ZFContext.under hZ B) _ _ hw1 (.hyp (Or.inl rfl))

theorem step {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (ρ : Fin 1 → Fin m)
    (hw : Derives Γ (omega (ρ 0))) : Derives Γ (OmegaInductionSyntax.step ProjectionGetInductionSyntax.matrix ρ (ρ 0)) := by
  simp only [OmegaInductionSyntax.step, ProjectionGetInductionSyntax.matrix_pred, paramsUp]
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
  exact ProjectionGetSuccessor.correct_successor hZ2 _ _ _ hw2 (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (.hyp (Or.inl rfl)) (.hyp (Or.inr (Or.inl rfl)))

theorem all_correct {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) (hw : Derives Γ (omega w)) :
    Derives Γ (.all ((Formula.mem (Fin.last m) w.castSucc).imp (correct w.castSucc (Fin.last m)))) := by
  have hh := OmegaInduction.induction_on_omega ProjectionGetInductionSyntax.matrix (fun _ : Fin 1 => w) w
    (ZFContext.separation hZ ProjectionGetInductionSyntax.matrix) hw (base hZ (fun _ => w) hw) (step hZ (fun _ => w) hw)
  simpa only [OmegaInductionSyntax.holds, ProjectionGetInductionSyntax.matrix_pred, paramsUp] using hh

theorem at_index {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w i : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (.mem i w)) : Derives Γ (correct w i) := by
  have ht : Derives Γ ((Formula.mem i w).imp (correct w i)) := by
    simpa only [Formula.instantiate, Formula.rename, correct_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.allE i (all_correct hZ w hw)
  exact .impE ht hi

theorem checked_at_index {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w x i y : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (.mem i w)) : Derives Γ (point w x i y) := at_value w i x y (at_index hZ w i hw hi)

theorem checked_sound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w x i y : Fin m)
    (hw : Derives Γ (omega w)) (hq : Derives Γ (ProjectionTraceSyntax.get w x i y)) : Derives Γ (RawCodeGetSyntax.get w x i y) := by
  have hi := ProjectionNodeFields.get_natural_at hZ w x i y 1 hw hq
  exact .conjR (.impE (.conjL (checked_at_index hZ w x i y hw hi)) hq)

theorem checked_complete {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w x i y : Fin m)
    (hw : Derives Γ (omega w)) (hx : Derives Γ (.mem x w)) (hi : Derives Γ (.mem i w))
    (hy : Derives Γ (RawCodeGetSyntax.get w x i y)) : Derives Γ (ProjectionTraceSyntax.get w x i y) :=
  .impE (.conjR (checked_at_index hZ w x i y hw hi)) (.conjI hx hy)

theorem checked_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w x i y : Fin m) (hw : Derives Γ (omega w)) :
    Derives Γ ((ProjectionTraceSyntax.get w x i y).iff
      ((Formula.mem x w).conj ((Formula.mem i w).conj (RawCodeGetSyntax.get w x i y)))) := by
  apply Derives.conjI
  · apply Derives.impI
    have hq : Derives (Context.add (ProjectionTraceSyntax.get w x i y) Γ) (ProjectionTraceSyntax.get w x i y) := .hyp (Or.inl rfl)
    exact .conjI (ProjectionNodeFields.get_natural_at (ZFContext.add hZ _) w x i y 0 (add hw _) hq)
      (.conjI (ProjectionNodeFields.get_natural_at (ZFContext.add hZ _) w x i y 1 (add hw _) hq) (checked_sound (ZFContext.add hZ _) w x i y (add hw _) hq))
  · apply Derives.impI
    have hB : Derives (Context.add ((Formula.mem x w).conj ((Formula.mem i w).conj (RawCodeGetSyntax.get w x i y))) Γ)
        ((Formula.mem x w).conj ((Formula.mem i w).conj (RawCodeGetSyntax.get w x i y))) := .hyp (Or.inl rfl)
    exact checked_complete (ZFContext.add hZ _) w x i y (add hw _) (.conjL hB) (.conjL (.conjR hB)) (.conjR (.conjR hB))

theorem checked_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w x i y z : Fin m)
    (hw : Derives Γ (omega w)) (hy : Derives Γ (ProjectionTraceSyntax.get w x i y))
    (hz : Derives Γ (ProjectionTraceSyntax.get w x i z)) : Derives Γ (.equal y z) :=
  RawCodeGetValues.unique hZ w x i y z hw (ProjectionNodeFields.get_natural_at hZ w x i y 1 hw hy)
    (checked_sound hZ w x i y hw hy) (checked_sound hZ w x i z hw hz)

end PPAC.Migration.Internal.ProjectionGetInduction
