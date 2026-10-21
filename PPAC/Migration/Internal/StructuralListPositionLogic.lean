import PPAC.Migration.Internal.ObjectStructuralListEnd

/-! 原列表迹反向位置对应所需真实递归零点、后继构造及Cons行反向投影。 -/
namespace PPAC.Migration.Internal.StructuralListPositionLogic
open Source SourceAlgebra SourceLogic OmegaSyntax StructuralListProjectionSyntax StructuralListIterationTransport
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
  have heq := StructuralListProjectionRecursion.iteration_zero head _ _ _ _ hz1 hY
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
  have hnext := StructuralListProjectionRecursion.iteration_step hZ1 head _ _ _ _ _ _ hw1 (under hr Y) hs1 hu1 hY
  have heq := StructuralListProjection.functional_point hZ1 head _ _ _ _ hw1 hnext hv1
  have hout := value_subst head _ _ _ _ _ heq hY
  simpa only [Formula.raise, iteration_rename] using hout

theorem reverse_cons_step {m} {Γ : Context m} (w a b : Fin m)
    (ha : Derives Γ (.mem a w)) (hs : Derives Γ (StructuralListTraceSyntax.step w a b)) : Derives Γ (step false w b a) := by
  let H := (Formula.mem (Fin.last m) w.castSucc).conj (StructuralListSyntax.consCode w.castSucc (Fin.last m) a.castSucc b.castSucc)
  let Δ := Context.add H (Context.image Formula.raise Γ)
  change Derives Γ (.ex H) at hs
  apply Derives.exE (p := H) hs
  have hH : Derives Δ H := .hyp (Or.inl rfl)
  have hout : Derives Δ (step false w.castSucc b.castSucc a.castSucc) :=
    .disjL (intro_selected false w.castSucc b.castSucc a.castSucc (Fin.last m) (.conjI (.conjI (under ha H) (.conjL hH)) (.conjR hH)))
  simpa only [Formula.raise, step_rename] using hout
end PPAC.Migration.Internal.StructuralListPositionLogic
