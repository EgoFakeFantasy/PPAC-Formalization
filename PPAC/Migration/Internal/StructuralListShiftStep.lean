import PPAC.Migration.Internal.StructuralListShiftSyntax

/-! 对象ω移位归纳的零点和后继步；前驱值均由实际内部递归图存在性取得。 -/
namespace PPAC.Migration.Internal.StructuralListShiftStep
open Source SourceAlgebra SourceLogic OmegaSyntax StructuralListProjectionSyntax StructuralListShiftSyntax StructuralListIterationTransport
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem empty_point {m} {Γ : Context m} (head : Bool) (w a b r u v : Fin m)
    (hr : Derives Γ (empty r)) (hab : Derives Γ (step head w a b))
    (hu : Derives Γ (iteration head w a r u)) (hv : Derives Γ (iteration head w b r v)) : Derives Γ (step head w u v) := by
  have hua := StructuralListProjectionRecursion.iteration_zero head w a r u hr hu
  have hvb := StructuralListProjectionRecursion.iteration_zero head w b r v hr hv
  exact step_output_subst head w u b v (eq_symm hvb) (step_input_subst head w a u b (eq_symm hua) hab)

theorem coupled_empty {m} {Γ : Context m} (head : Bool) (w a b r : Fin m)
    (hr : Derives Γ (empty r)) (hab : Derives Γ (step head w a b)) : Derives Γ (coupled head w a b r) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  apply Derives.impI
  let P := iteration head w.castSucc.castSucc a.castSucc.castSucc r.castSucc.castSucc (Fin.last m).castSucc
  let Q := iteration head w.castSucc.castSucc b.castSucc.castSucc r.castSucc.castSucc (Fin.last (m+1))
  let Δ := Context.add Q (Context.add P (Context.image Formula.raise (Context.image Formula.raise Γ)))
  have lift {q : Formula m} (hq : Derives Γ q) : Derives Δ q.raise.raise :=
    add (add (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hq)) P) Q
  have hr2 : Derives Δ (empty r.castSucc.castSucc) := by simpa only [Formula.raise, empty_rename] using lift hr
  have hab2 : Derives Δ (step head w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc) := by
    simpa only [Formula.raise, step_rename] using lift hab
  exact empty_point head _ _ _ _ _ _ hr2 hab2 (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem successor_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (head : Bool) (w a b r s y z : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (.mem r w)) (hs : Derives Γ (successor s r))
    (hc : Derives Γ (coupled head w a b r)) (hy : Derives Γ (iteration head w a s y))
    (hz : Derives Γ (iteration head w b s z)) : Derives Γ (step head w y z) := by
  have hu := exists_value hZ head w a r hw hr
  let U := iteration head w.castSucc a.castSucc r.castSucc (Fin.last m)
  let Ξ := Context.add U (Context.image Formula.raise Γ)
  change Derives Γ (.ex U) at hu
  apply Derives.exE (p := U) hu
  have hZ1 : ZFContext.Evidence Ξ := ZFContext.under hZ U
  have hw1 : Derives Ξ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw U
  have hv := exists_value hZ1 head w.castSucc b.castSucc r.castSucc hw1 (under hr U)
  let V := iteration head w.castSucc.castSucc b.castSucc.castSucc r.castSucc.castSucc (Fin.last (m+1))
  let Δ := Context.add V (Context.image Formula.raise Ξ)
  change Derives Ξ (.ex V) at hv
  apply Derives.exE (p := V) hv
  have hZ2 : ZFContext.Evidence Δ := ZFContext.under hZ1 V
  have lift {q : Formula m} (hq : Derives Γ q) : Derives Δ q.raise.raise := under (under hq U) V
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using lift hw
  have hr2 : Derives Δ (.mem r.castSucc.castSucc w.castSucc.castSucc) := lift hr
  have hs2 : Derives Δ (successor s.castSucc.castSucc r.castSucc.castSucc) := by simpa only [Formula.raise, successor_rename] using lift hs
  have hc2 : Derives Δ (coupled head w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc r.castSucc.castSucc) := by
    simpa only [Formula.raise, coupled_rename] using lift hc
  have hy2 : Derives Δ (iteration head w.castSucc.castSucc a.castSucc.castSucc s.castSucc.castSucc y.castSucc.castSucc) := by
    simpa only [Formula.raise, iteration_rename] using lift hy
  have hz2 : Derives Δ (iteration head w.castSucc.castSucc b.castSucc.castSucc s.castSucc.castSucc z.castSucc.castSucc) := by
    simpa only [Formula.raise, iteration_rename] using lift hz
  have hU : Derives Ξ U := .hyp (Or.inl rfl)
  have hU2 : Derives Δ (iteration head w.castSucc.castSucc a.castSucc.castSucc r.castSucc.castSucc (Fin.last m).castSucc) := by
    simpa only [U, Formula.raise, iteration_rename] using under hU V
  have hV : Derives Δ V := .hyp (Or.inl rfl)
  have hprev := at_values head _ _ _ _ _ _ hc2 hU2 hV
  have hnextA := StructuralListProjectionRecursion.iteration_step hZ2 head _ _ _ _ _ _ hw2 hr2 hs2 hU2 hy2
  have hnextB := StructuralListProjectionRecursion.iteration_step hZ2 head _ _ _ _ _ _ hw2 hr2 hs2 hV hz2
  have heq := StructuralListProjection.functional_point hZ2 head _ _ _ _ hw2 hnextA hprev
  have hout := step_input_subst head _ _ _ _ (eq_symm heq) hnextB
  simpa only [Formula.raise, step_rename] using hout

theorem coupled_successor {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (head : Bool) (w a b r s : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (.mem r w)) (hs : Derives Γ (successor s r))
    (hc : Derives Γ (coupled head w a b r)) : Derives Γ (coupled head w a b s) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  apply Derives.impI
  let P := iteration head w.castSucc.castSucc a.castSucc.castSucc s.castSucc.castSucc (Fin.last m).castSucc
  let Q := iteration head w.castSucc.castSucc b.castSucc.castSucc s.castSucc.castSucc (Fin.last (m+1))
  let Δ := Context.add Q (Context.add P (Context.image Formula.raise (Context.image Formula.raise Γ)))
  have hZ2 : ZFContext.Evidence Δ := ZFContext.add (ZFContext.add (ZFContext.rename (ZFContext.rename hZ Fin.castSucc) Fin.castSucc) P) Q
  have lift {q : Formula m} (hq : Derives Γ q) : Derives Δ q.raise.raise :=
    add (add (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hq)) P) Q
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using lift hw
  have hr2 : Derives Δ (.mem r.castSucc.castSucc w.castSucc.castSucc) := lift hr
  have hs2 : Derives Δ (successor s.castSucc.castSucc r.castSucc.castSucc) := by simpa only [Formula.raise, successor_rename] using lift hs
  have hc2 : Derives Δ (coupled head w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc r.castSucc.castSucc) := by
    simpa only [Formula.raise, coupled_rename] using lift hc
  exact successor_point hZ2 head _ _ _ _ _ _ _ hw2 hr2 hs2 hc2 (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))
end PPAC.Migration.Internal.StructuralListShiftStep
