import PPAC.Migration.Internal.FreeWeakenResult

/-! 原mode0自由加强的全部内部有输出精确域、无输出、拒绝与单值性。 -/
namespace PPAC.Migration.Internal.FreeWeakenOutcome
open Source SourceAlgebra SourceLogic OmegaSyntax FreeWeakenResultSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem intro_has_output {m} {Γ : Context m} (w d p x idx y : Fin m)
    (hr : Derives Γ (returned w d p x idx y)) : Derives Γ (hasOutput w d p x idx) := by
  apply Derives.exI y
  exact of_eq (by simp only [Formula.instantiate, returned_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hr

theorem has_output_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w d p x idx : Fin m)
    (hw : Derives Γ (omega w)) : Derives Γ ((hasOutput w d p x idx).iff (guard w d p x idx)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := hasOutput w d p x idx
    let B := returned w.castSucc d.castSucc p.castSucc x.castSucc idx.castSucc (Fin.last m)
    let Δ := Context.add B (Context.image Formula.raise (Context.add E Γ))
    apply Derives.exE (p := B) (.hyp (Or.inl rfl))
    have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under (add hw E) B)
    have ho := FreeWeakenResult.returned_guard (ZFContext.under (ZFContext.add hZ E) B) _ _ _ _ _ _ hw1 (.hyp (Or.inl rfl))
    exact of_eq (guard_rename w d p x idx Fin.castSucc).symm ho
  · apply Derives.impI
    let E := guard w d p x idx
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have hi := SyntaxVariableDecode.index_natural false w idx x (.conjR (.conjR hE))
    have he := FreeWeakenValue.exists_shifted (ZFContext.add hZ E) w idx (add hw E) hi
    let B := FreeWeakenValueSyntax.shifted w.castSucc idx.castSucc (Fin.last m)
    let Δ := Context.add B (Context.image Formula.raise (Context.add E Γ))
    apply Derives.exE (p := B) he
    have hZ1 := ZFContext.under (ZFContext.add hZ E) B
    have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under (add hw E) B)
    have hg1 : Derives Δ (guard w.castSucc d.castSucc p.castSucc x.castSucc idx.castSucc) := of_eq (guard_rename w d p x idx Fin.castSucc) (under hE B)
    have hr := FreeWeakenResult.shifted_returned hZ1 _ _ _ _ _ _ hw1 hg1 (.hyp (Or.inl rfl))
    exact of_eq (hasOutput_rename w d p x idx Fin.castSucc).symm (intro_has_output _ _ _ _ _ _ hr)

theorem no_output_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w d p x idx : Fin m)
    (hw : Derives Γ (omega w)) : Derives Γ ((noOutput w d p x idx).iff (guard w d p x idx).neg) :=
  FormulaTransformCongruence.imp_congr (has_output_iff hZ w d p x idx hw) (SyntaxTypeLocalTransfer.iff_refl .bot)

theorem total_on_guard {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w d p x idx : Fin m)
    (hw : Derives Γ (omega w)) (hg : Derives Γ (guard w d p x idx)) : Derives Γ (hasOutput w d p x idx) :=
  .impE (.conjR (has_output_iff hZ w d p x idx hw)) hg

theorem invalid_guard_no_output {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w d p x idx : Fin m)
    (hw : Derives Γ (omega w)) (hg : Derives Γ (guard w d p x idx).neg) : Derives Γ (noOutput w d p x idx) :=
  .impE (.conjR (no_output_iff hZ w d p x idx hw)) hg

theorem invalid_parameter_no_output {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w d p x idx : Fin m)
    (hw : Derives Γ (omega w)) (hp : Derives Γ (Formula.mem p w).neg) : Derives Γ (noOutput w d p x idx) := by
  apply invalid_guard_no_output hZ w d p x idx hw
  apply Derives.impI
  exact .impE (add hp _) (.conjL (.conjR (.hyp (Or.inl rfl))))

theorem invalid_depth_no_output {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w d p x idx : Fin m)
    (hw : Derives Γ (omega w)) (hd : Derives Γ (Formula.mem d w).neg) : Derives Γ (noOutput w d p x idx) := by
  apply invalid_guard_no_output hZ w d p x idx hw
  apply Derives.impI
  exact .impE (add hd _) (.conjL (.hyp (Or.inl rfl)))

theorem invalid_input_no_output {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w d p x idx : Fin m)
    (hw : Derives Γ (omega w)) (hx : Derives Γ (SyntaxVariableSyntax.code false w idx x).neg) : Derives Γ (noOutput w d p x idx) := by
  apply invalid_guard_no_output hZ w d p x idx hw
  apply Derives.impI
  exact .impE (add hx _) (.conjR (.conjR (.hyp (Or.inl rfl))))

theorem output_natural {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w d p x idx y : Fin m)
    (hw : Derives Γ (omega w)) (hy : Derives Γ (returned w d p x idx y)) : Derives Γ (.mem y w) :=
  FreeWeakenValue.natural hZ w idx y hw (FreeWeakenResult.returned_shifted hZ w d p x idx y hw hy)

theorem invalid_output_rejected {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w d p x idx y : Fin m)
    (hw : Derives Γ (omega w)) (hy : Derives Γ (Formula.mem y w).neg) : Derives Γ (returned w d p x idx y).neg := by
  apply Derives.impI
  exact .impE (add hy _) (output_natural (ZFContext.add hZ _) w d p x idx y (add hw _) (.hyp (Or.inl rfl)))

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w d p x idx y z : Fin m)
    (hw : Derives Γ (omega w)) (hy : Derives Γ (returned w d p x idx y)) (hz : Derives Γ (returned w d p x idx z)) : Derives Γ (.equal y z) :=
  FreeWeakenValue.unique hZ w idx y z hw (FreeWeakenResult.returned_shifted hZ w d p x idx y hw hy) (FreeWeakenResult.returned_shifted hZ w d p x idx z hw hz)

end PPAC.Migration.Internal.FreeWeakenOutcome
