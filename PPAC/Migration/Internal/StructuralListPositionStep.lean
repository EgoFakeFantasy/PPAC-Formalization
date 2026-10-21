import PPAC.Migration.Internal.StructuralListPositionBase

/-! 原相邻Cons行沿r+k=l反向推进一次真实tail求值，原图见证全部保留。 -/
namespace PPAC.Migration.Internal.StructuralListPositionStep
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax SequenceSyntax NaturalAdditionSyntax StructuralListProjectionSyntax StructuralListPositionSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem successor_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w l d f n r s k y : Fin m)
    (hw : Derives Γ (omega w)) (hf : Derives Γ (sequence f d w))
    (hl : Derives Γ (StructuralListTraceSyntax.links w l f)) (hr : Derives Γ (.mem r w))
    (hs : Derives Γ (successor s r)) (hi : Derives Γ (positions w l f n r))
    (hk : Derives Γ (.mem k w)) (ha : Derives Γ (sum w s k l))
    (hy : Derives Γ (edge f k y)) : Derives Γ (iteration false w n s y) := by
  have hkl := StructuralListPositionArithmetic.old_index hZ w r s k l hw hr hk hs ha
  have hrow := StructuralListTraceSyntax.links_at w l f k hl hkl
  let W := StructuralListTraceSyntax.rowWitness w f k
  let Δ := Context.add W (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ)))
  apply StructuralListTraceSyntax.eliminate_row w f k _ hrow
  have hZ3 : ZFContext.Evidence Δ := ZFContext.add (ZFContext.rename (ZFContext.rename (ZFContext.rename hZ Fin.castSucc) Fin.castSucc) Fin.castSucc) W
  have lift {q : Formula m} (hq : Derives Γ q) : Derives Δ q.raise.raise.raise := add (OrdinalRestriction.raise_three hq) W
  have hw3 : Derives Δ (omega w.castSucc.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using lift hw
  have hf3 : Derives Δ (sequence f.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc w.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, sequence_rename] using lift hf
  have hs3 : Derives Δ (successor s.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, successor_rename] using lift hs
  have hi3 : Derives Δ (positions w.castSucc.castSucc.castSucc l.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, positions_rename] using lift hi
  have ha3 : Derives Δ (sum w.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc k.castSucc.castSucc.castSucc l.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, sum_rename] using lift ha
  have hy3 : Derives Δ (edge f.castSucc.castSucc.castSucc k.castSucc.castSucc.castSucc y.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, edge_rename] using lift hy
  have hW : Derives Δ W := .hyp (Or.inl rfl)
  have hjW := OmegaStructureAlgebra.successor_member _ _ _ (ZFContext.arithmetic hZ3).base.extensionality hw3 (lift hk) (.conjL hW)
  have hsum := StructuralListPositionArithmetic.swap_successors hZ3 _ _ _ _ _ _ hw3 (lift hr) (lift hk) hs3 (.conjL hW) ha3
  have hprev := at_position _ _ _ _ _ _ _ hi3 hjW hsum (.conjL (.conjR (.conjR hW)))
  have hnat := Derives.impE (SequenceSyntax.bounded_at _ _ _ _ (.conjR hf3)) (.conjL (.conjR hW))
  have hstep := StructuralListPositionLogic.reverse_cons_step _ _ _ hnat (.conjR (.conjR (.conjR hW)))
  have heq := GraphProperties.single_valued _ _ _ _ _ (ZFContext.arithmetic hZ3).base.extensionality (.conjL hf3) (.conjL (.conjR hW)) hy3
  have hstepY := StructuralListIterationTransport.step_output_subst false _ _ _ _ heq hstep
  have hout := StructuralListPositionLogic.advance hZ3 false _ _ _ _ _ _ hw3 (lift hr) hs3 hprev hstepY
  simpa only [Formula.raise, iteration_rename] using hout

theorem positions_successor {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w l d f n r s : Fin m)
    (hw : Derives Γ (omega w)) (hf : Derives Γ (sequence f d w))
    (hl : Derives Γ (StructuralListTraceSyntax.links w l f)) (hr : Derives Γ (.mem r w))
    (hs : Derives Γ (successor s r)) (hi : Derives Γ (positions w l f n r)) : Derives Γ (positions w l f n s) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let A := (((Formula.mem (Fin.last m).castSucc w.castSucc.castSucc).conj
    (sum w.castSucc.castSucc s.castSucc.castSucc (Fin.last m).castSucc l.castSucc.castSucc)).conj
    (edge f.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))))
  let Δ := Context.add A (Context.image Formula.raise (Context.image Formula.raise Γ))
  have hZ2 : ZFContext.Evidence Δ := ZFContext.under_two hZ A
  have lift {q : Formula m} (hq : Derives Γ q) : Derives Δ q.raise.raise := OrderedPairElimination.under_two hq A
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using lift hw
  have hf2 : Derives Δ (sequence f.castSucc.castSucc d.castSucc.castSucc w.castSucc.castSucc) := by simpa only [Formula.raise, sequence_rename] using lift hf
  have hl2 : Derives Δ (StructuralListTraceSyntax.links w.castSucc.castSucc l.castSucc.castSucc f.castSucc.castSucc) := by
    simpa only [Formula.raise, StructuralListTraceSyntax.links_rename] using lift hl
  have hs2 : Derives Δ (successor s.castSucc.castSucc r.castSucc.castSucc) := by simpa only [Formula.raise, successor_rename] using lift hs
  have hi2 : Derives Δ (positions w.castSucc.castSucc l.castSucc.castSucc f.castSucc.castSucc n.castSucc.castSucc r.castSucc.castSucc) := by
    simpa only [Formula.raise, positions_rename] using lift hi
  have hA : Derives Δ A := .hyp (Or.inl rfl)
  exact successor_point hZ2 _ _ _ _ _ _ _ _ _ hw2 hf2 hl2 (lift hr) hs2 hi2 (.conjL (.conjL hA)) (.conjR (.conjL hA)) (.conjR hA)
end PPAC.Migration.Internal.StructuralListPositionStep
