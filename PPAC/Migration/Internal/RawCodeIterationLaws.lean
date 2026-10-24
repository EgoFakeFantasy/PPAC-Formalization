import PPAC.Migration.Internal.RawCodeShift

/-! 任意原始外壳投影递归的实际零点和后继构造。 -/
namespace PPAC.Migration.Internal.RawCodeIterationLaws
open Source SourceAlgebra SourceLogic OmegaSyntax RawCodeProjectionSyntax RawCodeIterationTransport
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem zero_value {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (head : Bool) (w a z : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) : Derives Γ (iteration head w a z a) := by
  have hzW := OmegaStructureAlgebra.zero_member w z (ZFContext.arithmetic hZ).base.extensionality hw hz
  have hy := exists_value hZ head w a z hw hzW
  let Y := iteration head w.castSucc a.castSucc z.castSucc (Fin.last m)
  let Δ := Context.add Y (Context.image Formula.raise Γ)
  change Derives Γ (.ex Y) at hy
  apply Derives.exE (p := Y) hy
  have hz1 : Derives Δ (empty z.castSucc) := by simpa only [Formula.raise, empty_rename] using under hz Y
  have hY : Derives Δ Y := .hyp (Or.inl rfl)
  have heq := RawCodeProjectionRecursion.iteration_zero head _ _ _ _ hz1 hY
  have hout := value_subst head _ _ _ _ _ heq hY
  simpa only [Formula.raise, iteration_rename] using hout

theorem advance {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (head : Bool) (w a r s u v : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (.mem r w)) (hs : Derives Γ (successor s r))
    (hu : Derives Γ (iteration head w a r u)) (hv : Derives Γ (step head w u v)) : Derives Γ (iteration head w a s v) := by
  have hsW := OmegaStructureAlgebra.successor_member w s r (ZFContext.arithmetic hZ).base.extensionality hw hr hs
  have hy := exists_value hZ head w a s hw hsW
  let Y := iteration head w.castSucc a.castSucc s.castSucc (Fin.last m)
  let Δ := Context.add Y (Context.image Formula.raise Γ)
  change Derives Γ (.ex Y) at hy
  apply Derives.exE (p := Y) hy
  have hZ1 : ZFContext.Evidence Δ := ZFContext.under hZ Y
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw Y
  have hs1 : Derives Δ (successor s.castSucc r.castSucc) := by simpa only [Formula.raise, successor_rename] using under hs Y
  have hu1 : Derives Δ (iteration head w.castSucc a.castSucc r.castSucc u.castSucc) := by simpa only [Formula.raise, iteration_rename] using under hu Y
  have hv1 : Derives Δ (step head w.castSucc u.castSucc v.castSucc) := by simpa only [Formula.raise, step_rename] using under hv Y
  have hY : Derives Δ Y := .hyp (Or.inl rfl)
  have hnext := RawCodeProjectionRecursion.iteration_step hZ1 head _ _ _ _ _ _ hw1 (under hr Y) hs1 hu1 hY
  have heq := RawCodeProjection.functional_point hZ1 head _ _ _ _ hw1 hnext hv1
  have hout := value_subst head _ _ _ _ _ heq hY
  simpa only [Formula.raise, iteration_rename] using hout

end PPAC.Migration.Internal.RawCodeIterationLaws
