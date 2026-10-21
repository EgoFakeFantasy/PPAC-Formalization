import PPAC.Migration.Internal.StructuralListCheckInvariantSyntax

/-! 首次终端前不变量的零点与实际后继；每步取得真实前驱求值。 -/
namespace PPAC.Migration.Internal.StructuralListCheckInvariantStep
open Source SourceAlgebra SourceLogic OmegaSyntax StructuralListProjectionSyntax StructuralListCheckSyntax StructuralListCheckInvariantSyntax
open StructuralListTraceSyntax (valid valid_rename)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem before_predecessor {m} {Γ : Context m} (w n r s : Fin m) (hs : Derives Γ (successor s r))
    (hb : Derives Γ (before w n s)) : Derives Γ (before w n r) := by
  apply Derives.allI
  apply Derives.impI
  let M := Formula.mem (Fin.last m) r.castSucc
  let Δ := Context.add M (Context.image Formula.raise Γ)
  have hs1 : Derives Δ (successor s.castSucc r.castSucc) := by simpa only [Formula.raise, successor_rename] using under hs M
  have hb1 : Derives Δ (before w.castSucc n.castSucc s.castSucc) := by simpa only [Formula.raise, before_rename] using under hb M
  exact before_at _ _ _ _ hb1 (InsertLogic.old_member _ _ _ _ hs1 (.hyp (Or.inl rfl)))

theorem nonterminal_at {m} {Γ : Context m} (w n r s b : Fin m) (hs : Derives Γ (successor s r))
    (hf : Derives Γ (before w n s)) (hb : Derives Γ (iteration false w n r b)) : Derives Γ (terminal w b).neg := by
  have hno := before_at w n s r hf (InsertLogic.new_member s r r hs)
  apply Derives.impI
  exact .impE (add hno _) (intro_occurs _ _ _ _ (add hb _) (.hyp (Or.inl rfl)))

theorem empty_invariant {m} {Γ : Context m} (w n r : Fin m) (hz : Derives Γ (empty r)) : Derives Γ (invariant w n r) := by
  apply Derives.impI
  apply Derives.allI
  apply Derives.impI
  let B := before w n r
  let Y := iteration false w.castSucc n.castSucc r.castSucc (Fin.last m)
  let Δ := Context.add Y (Context.image Formula.raise (Context.add B Γ))
  have hz1 : Derives Δ (empty r.castSucc) := by simpa only [Formula.raise, empty_rename] using under (add hz B) Y
  have hY : Derives Δ Y := .hyp (Or.inl rfl)
  have he := StructuralListProjectionRecursion.iteration_zero false _ _ _ _ hz1 hY
  exact StructuralListCheckPreservationStep.valid_equal_iff _ _ _ (eq_symm he)

theorem point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n r s b : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (.mem r w)) (hs : Derives Γ (successor s r))
    (hi : Derives Γ (invariant w n r)) (hf : Derives Γ (before w n s)) (hb : Derives Γ (iteration false w n s b)) :
    Derives Γ ((valid w n).iff (valid w b)) := by
  have hu := StructuralListIterationTransport.exists_value hZ false w n r hw hr
  let U := iteration false w.castSucc n.castSucc r.castSucc (Fin.last m)
  let Δ := Context.add U (Context.image Formula.raise Γ)
  change Derives Γ (.ex U) at hu
  apply Derives.exE (p := U) hu
  have hZ1 : ZFContext.Evidence Δ := ZFContext.under hZ U
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw U
  have hs1 : Derives Δ (successor s.castSucc r.castSucc) := by simpa only [Formula.raise, successor_rename] using under hs U
  have hi1 : Derives Δ (invariant w.castSucc n.castSucc r.castSucc) := by simpa only [Formula.raise, invariant_rename] using under hi U
  have hf1 : Derives Δ (before w.castSucc n.castSucc s.castSucc) := by simpa only [Formula.raise, before_rename] using under hf U
  have hb1 : Derives Δ (iteration false w.castSucc n.castSucc s.castSucc b.castSucc) := by simpa only [Formula.raise, iteration_rename] using under hb U
  have hU : Derives Δ U := .hyp (Or.inl rfl)
  have hnv := nonterminal_at _ _ _ _ _ hs1 hf1 hU
  have hprev := at_value _ _ _ _ hi1 (before_predecessor _ _ _ _ hs1 hf1) hU
  have hstep := StructuralListProjectionRecursion.iteration_step hZ1 false _ _ _ _ _ _ hw1 (under hr U) hs1 hU hb1
  have hout := StructuralListSuffixArithmetic.iff_trans hprev (StructuralListCheckPreservationStep.preserve hZ1 _ _ _ hw1 hnv hstep)
  simpa only [Formula.raise, Formula.rename, Formula.iff, valid_rename] using hout

theorem invariant_successor {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n r s : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (.mem r w)) (hs : Derives Γ (successor s r))
    (hi : Derives Γ (invariant w n r)) : Derives Γ (invariant w n s) := by
  apply Derives.impI
  apply Derives.allI
  apply Derives.impI
  let B := before w n s
  let Y := iteration false w.castSucc n.castSucc s.castSucc (Fin.last m)
  let Δ := Context.add Y (Context.image Formula.raise (Context.add B Γ))
  have hZ1 : ZFContext.Evidence Δ := ZFContext.under (ZFContext.add hZ B) Y
  have lift {p : Formula m} (hp : Derives Γ p) : Derives Δ p.raise := under (add hp B) Y
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using lift hw
  have hs1 : Derives Δ (successor s.castSucc r.castSucc) := by simpa only [Formula.raise, successor_rename] using lift hs
  have hi1 : Derives Δ (invariant w.castSucc n.castSucc r.castSucc) := by simpa only [Formula.raise, invariant_rename] using lift hi
  have hf1 : Derives Δ (before w.castSucc n.castSucc s.castSucc) := by
    simpa only [B, Formula.raise, before_rename] using under (Derives.hyp (Γ := Context.add B Γ) (Or.inl rfl)) Y
  exact point hZ1 _ _ _ _ _ hw1 (lift hr) hs1 hi1 hf1 (.hyp (Or.inl rfl))
end PPAC.Migration.Internal.StructuralListCheckInvariantStep
