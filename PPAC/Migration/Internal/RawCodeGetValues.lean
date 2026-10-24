import PPAC.Migration.Internal.RawCodeGetSyntax

/-! 全内部自然索引的实际原get值存在、ω值域及全候选唯一性；种子可为任意内部集合。 -/
namespace PPAC.Migration.Internal.RawCodeGetValues
open Source SourceAlgebra SourceLogic OmegaSyntax RawCodeProjectionSyntax RawCodeGetSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem range {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n i y : Fin m)
    (hw : Derives Γ (omega w)) (hy : Derives Γ (get w n i y)) : Derives Γ (.mem y w) := by
  let T := (iteration false w.castSucc n.castSucc i.castSucc (Fin.last m)).conj (step true w.castSucc (Fin.last m) y.castSucc)
  let Δ := Context.add T (Context.image Formula.raise Γ)
  change Derives Γ (.ex T) at hy
  apply Derives.exE (p := T) hy
  have hZ1 : ZFContext.Evidence Δ := ZFContext.under hZ T
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw T
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  exact RawCodeProjection.range_point hZ1 true _ _ _ hw1 (.conjR hT)

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n i y z : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (.mem i w))
    (hy : Derives Γ (get w n i y)) (hz : Derives Γ (get w n i z)) : Derives Γ (.equal y z) := by
  let T := (iteration false w.castSucc n.castSucc i.castSucc (Fin.last m)).conj (step true w.castSucc (Fin.last m) y.castSucc)
  let Ξ := Context.add T (Context.image Formula.raise Γ)
  change Derives Γ (.ex T) at hy
  apply Derives.exE (p := T) hy
  have hz1 : Derives Ξ (get w.castSucc n.castSucc i.castSucc z.castSucc) := by simpa only [Formula.raise, get_rename] using under hz T
  let U := (iteration false w.castSucc.castSucc n.castSucc.castSucc i.castSucc.castSucc (Fin.last (m+1))).conj
    (step true w.castSucc.castSucc (Fin.last (m+1)) z.castSucc.castSucc)
  let Δ := Context.add U (Context.image Formula.raise Ξ)
  change Derives Ξ (.ex U) at hz1
  apply Derives.exE (p := U) hz1
  have hZ2 : ZFContext.Evidence Δ := ZFContext.under (ZFContext.under hZ T) U
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using under (under hw T) U
  have hT : Derives Ξ T := .hyp (Or.inl rfl)
  have hT2 : Derives Δ ((iteration false w.castSucc.castSucc n.castSucc.castSucc i.castSucc.castSucc (Fin.last m).castSucc).conj
      (step true w.castSucc.castSucc (Fin.last m).castSucc y.castSucc.castSucc)) := by
    simpa only [T, Formula.raise, Formula.rename, iteration_rename, step_rename] using under hT U
  have hU : Derives Δ U := .hyp (Or.inl rfl)
  have heq := RawCodeIterationTransport.unique hZ2 false _ _ _ _ _ hw2 (under (under hi T) U) (.conjL hT2) (.conjL hU)
  have hStep := RawCodeIterationTransport.step_input_subst true _ _ _ _ heq (.conjR hT2)
  exact RawCodeProjection.functional_point hZ2 true _ _ _ _ hw2 hStep (.conjR hU)

theorem exists_value {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n i : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (.mem i w)) : Derives Γ (existsGet w n i) := by
  have ht := RawCodeIterationTransport.exists_value hZ false w n i hw hi
  let T := iteration false w.castSucc n.castSucc i.castSucc (Fin.last m)
  let Ξ := Context.add T (Context.image Formula.raise Γ)
  change Derives Γ (.ex T) at ht
  apply Derives.exE (p := T) ht
  have hZ1 : ZFContext.Evidence Ξ := ZFContext.under hZ T
  have hw1 : Derives Ξ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw T
  have hy := RawCodeProjection.exists_step true w.castSucc (Fin.last m) hw1
  let Y := step true w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
  let Δ := Context.add Y (Context.image Formula.raise Ξ)
  change Derives Ξ (.ex Y) at hy
  apply Derives.exE (p := Y) hy
  have hZ2 : ZFContext.Evidence Δ := ZFContext.under hZ1 Y
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw1 Y
  have hT : Derives Ξ T := .hyp (Or.inl rfl)
  have hT2 : Derives Δ (iteration false w.castSucc.castSucc n.castSucc.castSucc i.castSucc.castSucc (Fin.last m).castSucc) := by
    simpa only [T, Formula.raise, iteration_rename] using under hT Y
  have hY : Derives Δ Y := .hyp (Or.inl rfl)
  have hnat := RawCodeProjection.range_point hZ2 true _ _ _ hw2 hY
  have hf := intro_get _ _ _ _ _ hT2 hY
  have hout := intro_exists _ _ _ _ hnat hf
  simpa only [Formula.raise, existsGet_rename] using hout

theorem exists_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n i : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (.mem i w)) : Derives Γ (fiber w n i) := by
  have hy := exists_value hZ w n i hw hi
  let Y := (Formula.mem (Fin.last m) w.castSucc).conj (get w.castSucc n.castSucc i.castSucc (Fin.last m))
  let Ξ := Context.add Y (Context.image Formula.raise Γ)
  change Derives Γ (.ex Y) at hy
  apply Derives.exE (p := Y) hy
  have hZ1 : ZFContext.Evidence Ξ := ZFContext.under hZ Y
  have hw1 : Derives Ξ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw Y
  have hY : Derives Ξ Y := .hyp (Or.inl rfl)
  have hu : Derives Ξ (.all ((get w.castSucc.castSucc n.castSucc.castSucc i.castSucc.castSucc (Fin.last (m+1))).imp
      (.equal (Fin.last (m+1)) (Fin.last m).castSucc))) := by
    apply Derives.allI
    apply Derives.impI
    let Z := get w.castSucc.castSucc n.castSucc.castSucc i.castSucc.castSucc (Fin.last (m+1))
    let Δ := Context.add Z (Context.image Formula.raise Ξ)
    have hZ2 : ZFContext.Evidence Δ := ZFContext.under hZ1 Z
    have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw1 Z
    have hOld : Derives Δ (get w.castSucc.castSucc n.castSucc.castSucc i.castSucc.castSucc (Fin.last m).castSucc) := by
      simpa only [Formula.raise, get_rename] using under (.conjR hY) Z
    exact unique hZ2 _ _ _ _ _ hw2 (under (under hi Y) Z) (.hyp (Or.inl rfl)) hOld
  have hout : Derives Ξ (fiber w.castSucc n.castSucc i.castSucc) := by
    apply Derives.exI (Fin.last m)
    simp only [Formula.instantiate, Formula.rename, get_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
    exact .conjI hY hu
  simpa only [Formula.raise, fiber_rename] using hout
end PPAC.Migration.Internal.RawCodeGetValues
