import PPAC.Migration.Internal.FreeWeakenResultRows

/-! mode0自由变量原成功图的精确域；保留原arity要求的参数自然性。 -/
namespace PPAC.Migration.Internal.FreeWeakenResult
open Source SourceAlgebra SourceLogic OmegaSyntax FreeWeakenResultSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem returned_guard {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w d p x idx y : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (returned w d p x idx y)) : Derives Γ (guard w d p x idx) := by
  let B := (root w.castSucc d.castSucc p.castSucc x.castSucc y.castSucc (Fin.last m)).conj (HornLookupConditionSyntax.condition w.castSucc (Fin.last m))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) (.conjR hr)
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hv1 : Derives Δ (SyntaxVariableSyntax.code false w.castSucc idx.castSucc x.castSucc) := of_eq (SyntaxVariableSyntax.code_rename false w idx x Fin.castSucc) (under (.conjL hr) B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ B
  have hd := FreeWeakenResultRows.depth_natural hZ1 _ _ _ _ _ _ hw1 (.conjL hB)
  have hp := FreeWeakenResultRows.parameter_natural hZ1 _ _ _ _ _ _ hw1 (.conjL hB)
  exact of_eq (guard_rename w d p x idx Fin.castSucc).symm (.conjI hd (.conjI hp hv1))

theorem returned_shifted {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w d p x idx y : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (returned w d p x idx y)) :
    Derives Γ (FreeWeakenValueSyntax.shifted w idx y) := by
  let B := (root w.castSucc d.castSucc p.castSucc x.castSucc y.castSucc (Fin.last m)).conj (HornLookupConditionSyntax.condition w.castSucc (Fin.last m))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) (.conjR hr)
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hv1 : Derives Δ (SyntaxVariableSyntax.code false w.castSucc idx.castSucc x.castSucc) := of_eq (SyntaxVariableSyntax.code_rename false w idx x Fin.castSucc) (under (.conjL hr) B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := Derives.impE (.conjL (FreeWeakenResultRows.trace_iff_shifted (ZFContext.under hZ B) _ _ _ _ _ _ _ hw1 hv1 (.conjL hB))) (.conjR hB)
  exact of_eq (FreeWeakenValueSyntax.shifted_rename w idx y Fin.castSucc).symm ho

theorem shifted_returned {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w d p x idx y : Fin m)
    (hw : Derives Γ (omega w)) (hg : Derives Γ (guard w d p x idx))
    (he : Derives Γ (FreeWeakenValueSyntax.shifted w idx y)) : Derives Γ (returned w d p x idx y) := by
  have hvar := Derives.conjR (Derives.conjR hg)
  have hx := HornVariableValue.code_natural hZ false w idx x hw hvar
  have hy := FreeWeakenValue.natural hZ w idx y hw he
  have hex := FreeWeakenResultRows.exists_root hZ w d p x y hw (.conjL hg) (.conjL (.conjR hg)) hx hy
  let B := (Formula.mem (Fin.last m) w.castSucc).conj (root w.castSucc d.castSucc p.castSucc x.castSucc y.castSucc (Fin.last m))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hex
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hv1 : Derives Δ (SyntaxVariableSyntax.code false w.castSucc idx.castSucc x.castSucc) := of_eq (SyntaxVariableSyntax.code_rename false w idx x Fin.castSucc) (under hvar B)
  have he1 : Derives Δ (FreeWeakenValueSyntax.shifted w.castSucc idx.castSucc y.castSucc) := of_eq (FreeWeakenValueSyntax.shifted_rename w idx y Fin.castSucc) (under he B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ht := Derives.impE (.conjR (FreeWeakenResultRows.trace_iff_shifted (ZFContext.under hZ B) _ _ _ _ _ _ _ hw1 hv1 (.conjR hB))) he1
  have ho := Derives.conjI hv1 (intro_run _ _ _ _ _ _ (.conjR hB) ht)
  exact of_eq (returned_rename w d p x idx y Fin.castSucc).symm ho

theorem returned_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w d p x idx y : Fin m)
    (hw : Derives Γ (omega w)) :
    Derives Γ ((returned w d p x idx y).iff ((guard w d p x idx).conj (FreeWeakenValueSyntax.shifted w idx y))) := by
  apply Derives.conjI
  · apply Derives.impI
    exact .conjI (returned_guard (ZFContext.add hZ _) w d p x idx y (add hw _) (.hyp (Or.inl rfl)))
      (returned_shifted (ZFContext.add hZ _) w d p x idx y (add hw _) (.hyp (Or.inl rfl)))
  · apply Derives.impI
    exact shifted_returned (ZFContext.add hZ _) w d p x idx y (add hw _) (.conjL (.hyp (Or.inl rfl))) (.conjR (.hyp (Or.inl rfl)))

theorem under_guard_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w d p x idx y : Fin m)
    (hw : Derives Γ (omega w)) (hg : Derives Γ (guard w d p x idx)) :
    Derives Γ ((returned w d p x idx y).iff (FreeWeakenValueSyntax.shifted w idx y)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact returned_shifted (ZFContext.add hZ _) w d p x idx y (add hw _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact shifted_returned (ZFContext.add hZ _) w d p x idx y (add hw _) (add hg _) (.hyp (Or.inl rfl))

theorem at_successor_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w d p x idx y s : Fin m)
    (hw : Derives Γ (omega w)) (hg : Derives Γ (guard w d p x idx)) (hs : Derives Γ (successor s idx)) :
    Derives Γ ((returned w d p x idx y).iff (SyntaxVariableSyntax.code false w s y)) :=
  SyntaxTypeLocalTransfer.iff_trans (under_guard_iff hZ w d p x idx y hw hg) (FreeWeakenValue.at_successor hZ w idx y s hs)

theorem rejected_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w d p x idx y : Fin m)
    (hw : Derives Γ (omega w)) :
    Derives Γ ((returned w d p x idx y).neg.iff ((guard w d p x idx).conj (FreeWeakenValueSyntax.shifted w idx y)).neg) :=
  FormulaTransformCongruence.imp_congr (returned_iff hZ w d p x idx y hw) (SyntaxTypeLocalTransfer.iff_refl .bot)

end PPAC.Migration.Internal.FreeWeakenResult
