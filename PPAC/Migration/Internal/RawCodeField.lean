import PPAC.Migration.Internal.RawCodeFieldSyntax

/-! 原field的全部内部自然索引值实际存在唯一、载荷双条件及输入零码精确行为。 -/
namespace PPAC.Migration.Internal.RawCodeField
open Source SourceAlgebra SourceLogic OmegaSyntax RawCodeFieldSyntax

theorem range {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w x i y : Fin m)
    (hw : Derives Γ (omega w)) (hy : Derives Γ (field w x i y)) : Derives Γ (.mem y w) := by
  let B := body w.castSucc x.castSucc i.castSucc y.castSucc (Fin.last m)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hy
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw B
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  exact RawCodeGetValues.range (ZFContext.under hZ B) _ _ _ _ hw1 (.conjR hB)

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w x i y z : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (.mem i w))
    (hy : Derives Γ (field w x i y)) (hz : Derives Γ (field w x i z)) : Derives Γ (.equal y z) := by
  let P := body w.castSucc x.castSucc i.castSucc y.castSucc (Fin.last m)
  let Ξ := Context.add P (Context.image Formula.raise Γ)
  apply Derives.exE (p := P) hy
  have hz1 : Derives Ξ (field w.castSucc x.castSucc i.castSucc z.castSucc) := by simpa only [Formula.raise, field_rename] using under hz P
  let Q := body w.castSucc.castSucc x.castSucc.castSucc i.castSucc.castSucc z.castSucc.castSucc (Fin.last (m+1))
  let Δ := Context.add Q (Context.image Formula.raise Ξ)
  apply Derives.exE (p := Q) hz1
  have hZ2 := ZFContext.under (ZFContext.under hZ P) Q
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using under (under hw P) Q
  have hP : Derives Ξ P := .hyp (Or.inl rfl)
  have hP2 : Derives Δ (body w.castSucc.castSucc x.castSucc.castSucc i.castSucc.castSucc y.castSucc.castSucc (Fin.last m).castSucc) := by
    simpa only [P, Formula.raise, body_rename] using under hP Q
  have hQ : Derives Δ Q := .hyp (Or.inl rfl)
  have he := PairingProjection.functional_point hZ2 true false _ _ _ _ hw2 (.conjL hP2) (.conjL hQ)
  have hget := get_input_subst _ _ _ _ _ he (.conjR hP2)
  exact RawCodeGetValues.unique hZ2 _ _ _ _ _ hw2 (under (under hi P) Q) hget (.conjR hQ)

theorem exists_value {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w x i : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (.mem i w)) : Derives Γ (existsField w x i) := by
  let P := PairingProjectionSyntax.step true false w.castSucc x.castSucc (Fin.last m)
  let Ξ := Context.add P (Context.image Formula.raise Γ)
  apply Derives.exE (p := P) (PairingProjection.exists_step true false w x hw)
  have hZ1 := ZFContext.under hZ P
  have hw1 : Derives Ξ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw P
  let Y := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj (RawCodeGetSyntax.get w.castSucc.castSucc (Fin.last m).castSucc i.castSucc.castSucc (Fin.last (m+1)))
  let Δ := Context.add Y (Context.image Formula.raise Ξ)
  apply Derives.exE (p := Y) (RawCodeGetValues.exists_value hZ1 _ _ _ hw1 (under hi P))
  have hP : Derives Ξ P := .hyp (Or.inl rfl)
  have hP2 : Derives Δ (PairingProjectionSyntax.step true false w.castSucc.castSucc x.castSucc.castSucc (Fin.last m).castSucc) := by
    simpa only [P, Formula.raise, PairingProjectionSyntax.step_rename] using under hP Y
  have hY : Derives Δ Y := .hyp (Or.inl rfl)
  have hout := intro_exists _ _ _ _ (.conjL hY) (intro_field _ _ _ _ _ hP2 (.conjR hY))
  simpa only [Formula.raise, existsField_rename] using hout

theorem exists_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n i : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (.mem i w)) : Derives Γ (fiber w n i) := by
  have hy := exists_value hZ w n i hw hi
  let Y := (Formula.mem (Fin.last m) w.castSucc).conj (field w.castSucc n.castSucc i.castSucc (Fin.last m))
  let Ξ := Context.add Y (Context.image Formula.raise Γ)
  change Derives Γ (.ex Y) at hy
  apply Derives.exE (p := Y) hy
  have hZ1 : ZFContext.Evidence Ξ := ZFContext.under hZ Y
  have hw1 : Derives Ξ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw Y
  have hY : Derives Ξ Y := .hyp (Or.inl rfl)
  have hu : Derives Ξ (.all ((field w.castSucc.castSucc n.castSucc.castSucc i.castSucc.castSucc (Fin.last (m+1))).imp
      (.equal (Fin.last (m+1)) (Fin.last m).castSucc))) := by
    apply Derives.allI
    apply Derives.impI
    let Z := field w.castSucc.castSucc n.castSucc.castSucc i.castSucc.castSucc (Fin.last (m+1))
    let Δ := Context.add Z (Context.image Formula.raise Ξ)
    have hZ2 : ZFContext.Evidence Δ := ZFContext.under hZ1 Z
    have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw1 Z
    have hOld : Derives Δ (field w.castSucc.castSucc n.castSucc.castSucc i.castSucc.castSucc (Fin.last m).castSucc) := by
      simpa only [Formula.raise, field_rename] using under (.conjR hY) Z
    exact unique hZ2 _ _ _ _ _ hw2 (under (under hi Y) Z) (.hyp (Or.inl rfl)) hOld
  have hout : Derives Ξ (fiber w.castSucc n.castSucc i.castSucc) := by
    apply Derives.exI (Fin.last m)
    simp only [Formula.instantiate, Formula.rename, field_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
    exact .conjI hY hu
  simpa only [Formula.raise, fiber_rename] using hout
theorem at_payload_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w x p i y : Fin m)
    (hw : Derives Γ (omega w)) (hp : Derives Γ (PairingProjectionSyntax.step true false w x p)) :
    Derives Γ ((field w x i y).iff (RawCodeGetSyntax.get w p i y)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := field w x i y
    let B := body w.castSucc x.castSucc i.castSucc y.castSucc (Fin.last m)
    let Δ := Context.add B (Context.image Formula.raise (Context.add E Γ))
    apply Derives.exE (p := B) (.hyp (Or.inl rfl))
    have hZ1 := ZFContext.under (ZFContext.add hZ E) B
    have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under (add hw E) B
    have hp1 : Derives Δ (PairingProjectionSyntax.step true false w.castSucc x.castSucc p.castSucc) := by
      simpa only [Formula.raise, PairingProjectionSyntax.step_rename] using under (add hp E) B
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have he := PairingProjection.functional_point hZ1 true false _ _ _ _ hw1 (.conjL hB) hp1
    have hout := get_input_subst _ _ _ _ _ he (.conjR hB)
    simpa only [Formula.raise, RawCodeGetSyntax.get_rename] using hout
  · apply Derives.impI
    exact intro_field w x i y p (add hp _) (.hyp (Or.inl rfl))

theorem on_raw_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w tag p x i y : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (.mem tag w)) (hp : Derives Γ (.mem p w))
    (hr : Derives Γ (StructuralNodeSyntax.raw w tag p x)) :
    Derives Γ ((field w x i y).iff (RawCodeGetSyntax.get w p i y)) :=
  at_payload_iff hZ w x p i y hw (.disjL (PairingProjection.selected_code true false w tag p x ht hp hr))

theorem zero_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w x i y : Fin m)
    (hw : Derives Γ (omega w)) (hx : Derives Γ (empty x)) (hi : Derives Γ (.mem i w)) :
    Derives Γ ((field w x i y).iff (empty y)) := by
  have hp : Derives Γ (PairingProjectionSyntax.step true false w x x) := .disjR (.conjI (PairingProjectionNatural.raw_zero_unselected false w x hx) hx)
  have hf := at_payload_iff hZ w x x i y hw hp
  have hz := RawCodeGetZero.checked_iff hZ w x i y hw hx hi
  apply Derives.conjI
  · apply Derives.impI
    exact .impE (add (.conjL hz) _) (.impE (add (.conjL hf) _) (.hyp (Or.inl rfl)))
  · apply Derives.impI
    exact .impE (add (.conjR hf) _) (.impE (add (.conjR hz) _) (.hyp (Or.inl rfl)))

end PPAC.Migration.Internal.RawCodeField
