import PPAC.Migration.Internal.StructuralListPositionInduction

/-! 原完整迹每个域内位置实际取得自然反向索引，原边与真实tail求值精确双条件。 -/
namespace PPAC.Migration.Internal.StructuralListPositions
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax SequenceSyntax NaturalAdditionSyntax StructuralListProjectionSyntax StructuralListPositionSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem forward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w l d f n r k y : Fin m)
    (hw : Derives Γ (omega w)) (hf : Derives Γ (sequence f d w)) (hl : Derives Γ (StructuralListTraceSyntax.links w l f))
    (hn : Derives Γ (edge f l n)) (hr : Derives Γ (.mem r w)) (hk : Derives Γ (.mem k w))
    (hs : Derives Γ (sum w r k l)) (hy : Derives Γ (edge f k y)) : Derives Γ (iteration false w n r y) :=
  at_position w l f n r k y (StructuralListPositionInduction.at_index hZ w l d f n r hw hf hl hn hr) hk hs hy

theorem backward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w l d f n r k y : Fin m)
    (hw : Derives Γ (omega w)) (hf : Derives Γ (sequence f d w)) (hl : Derives Γ (StructuralListTraceSyntax.links w l f))
    (hd : Derives Γ (successor d l)) (hn : Derives Γ (edge f l n)) (hr : Derives Γ (.mem r w)) (hk : Derives Γ (.mem k w))
    (hs : Derives Γ (sum w r k l)) (hy : Derives Γ (iteration false w n r y)) : Derives Γ (edge f k y) := by
  have hb := GodelPairArithmetic.sum_right_bound hZ w r k l hw hr hk hs
  have hkd := NaturalAdditionBounds.into_successor k l d hb hd
  have hv := SequenceLogic.value_at f d w k hf hkd
  let V := (Formula.mem (Fin.last m) w.castSucc).conj (valueAt f.castSucc k.castSucc (Fin.last m))
  let Δ := Context.add V (Context.image Formula.raise Γ)
  change Derives Γ (.ex V) at hv
  apply Derives.exE (p := V) hv
  have hZ1 : ZFContext.Evidence Δ := ZFContext.under hZ V
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw V
  have hf1 : Derives Δ (sequence f.castSucc d.castSucc w.castSucc) := by simpa only [Formula.raise, sequence_rename] using under hf V
  have hl1 : Derives Δ (StructuralListTraceSyntax.links w.castSucc l.castSucc f.castSucc) := by simpa only [Formula.raise, StructuralListTraceSyntax.links_rename] using under hl V
  have hn1 : Derives Δ (edge f.castSucc l.castSucc n.castSucc) := by simpa only [Formula.raise, edge_rename] using under hn V
  have hs1 : Derives Δ (sum w.castSucc r.castSucc k.castSucc l.castSucc) := by simpa only [Formula.raise, sum_rename] using under hs V
  have hy1 : Derives Δ (iteration false w.castSucc n.castSucc r.castSucc y.castSucc) := by simpa only [Formula.raise, iteration_rename] using under hy V
  have hV : Derives Δ V := .hyp (Or.inl rfl)
  have hprev := forward hZ1 _ _ _ _ _ _ _ _ hw1 hf1 hl1 hn1 (under hr V) (under hk V) hs1 (.conjL (.conjR hV))
  have heq := StructuralListIterationTransport.unique hZ1 false _ _ _ _ _ hw1 (under hr V) hprev hy1
  have hout := GraphPointwiseSyntax.edge_subst_output _ _ _ _ heq (.conjL (.conjR hV))
  simpa only [Formula.raise, edge_rename] using hout

theorem edge_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w l d f n r k y : Fin m)
    (hw : Derives Γ (omega w)) (hf : Derives Γ (sequence f d w)) (hl : Derives Γ (StructuralListTraceSyntax.links w l f))
    (hd : Derives Γ (successor d l)) (hn : Derives Γ (edge f l n)) (hr : Derives Γ (.mem r w)) (hk : Derives Γ (.mem k w))
    (hs : Derives Γ (sum w r k l)) : Derives Γ ((edge f k y).iff (iteration false w n r y)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact forward (ZFContext.add hZ _) _ _ _ _ _ _ _ _ (add hw _) (add hf _) (add hl _) (add hn _) (add hr _) (add hk _) (add hs _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact backward (ZFContext.add hZ _) _ _ _ _ _ _ _ _ (add hw _) (add hf _) (add hl _) (add hd _) (add hn _) (add hr _) (add hk _) (add hs _) (.hyp (Or.inl rfl))

theorem from_trace {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z e l d f n r k y : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (StructuralListTraceSyntax.trace w z e l d f n))
    (hr : Derives Γ (.mem r w)) (hk : Derives Γ (.mem k w)) (hs : Derives Γ (sum w r k l))
    (hy : Derives Γ (edge f k y)) : Derives Γ (iteration false w n r y) :=
  forward hZ _ _ _ _ _ _ _ _ hw (StructuralListTraceProperties.sequence_at _ _ _ _ _ _ _ ht)
    (StructuralListTraceProperties.links_at_trace _ _ _ _ _ _ _ ht) (StructuralListTraceProperties.last_at _ _ _ _ _ _ _ ht) hr hk hs hy

theorem trace_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z e l d f n r k y : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (StructuralListTraceSyntax.trace w z e l d f n))
    (hr : Derives Γ (.mem r w)) (hk : Derives Γ (.mem k w)) (hs : Derives Γ (sum w r k l)) :
    Derives Γ ((edge f k y).iff (iteration false w n r y)) :=
  edge_iff hZ _ _ _ _ _ _ _ _ hw (StructuralListTraceProperties.sequence_at _ _ _ _ _ _ _ ht)
    (StructuralListTraceProperties.links_at_trace _ _ _ _ _ _ _ ht) (StructuralListTraceProperties.successor_at _ _ _ _ _ _ _ ht)
    (StructuralListTraceProperties.last_at _ _ _ _ _ _ _ ht) hr hk hs

theorem trace_reverse_exists {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z e l d f n k : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (StructuralListTraceSyntax.trace w z e l d f n))
    (hk : Derives Γ (.mem k d)) : Derives Γ (reverseExists w l f n k) := by
  have hlW := StructuralListTraceProperties.length_at _ _ _ _ _ _ _ ht
  have hd := StructuralListTraceProperties.successor_at _ _ _ _ _ _ _ ht
  have hdW := StructuralListTraceProperties.domain_member hZ _ _ _ _ _ _ _ hw ht
  have hkW := StructuralListTraceOrder.member_member hZ w k d hw hdW hk
  have hb := NaturalOrderBasic.member_successor k l d hd hk
  have hr := NaturalDifference.exists_of_below hZ w k l hw hkW hlW hb
  let R := (Formula.mem (Fin.last m) w.castSucc).conj (sum w.castSucc k.castSucc (Fin.last m) l.castSucc)
  let Ξ := Context.add R (Context.image Formula.raise Γ)
  change Derives Γ (.ex R) at hr
  apply Derives.exE (p := R) hr
  have hZ1 : ZFContext.Evidence Ξ := ZFContext.under hZ R
  have hw1 : Derives Ξ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw R
  have ht1 : Derives Ξ (StructuralListTraceSyntax.trace w.castSucc z.castSucc e.castSucc l.castSucc d.castSucc f.castSucc n.castSucc) := by
    simpa only [Formula.raise, StructuralListTraceSyntax.trace_rename] using under ht R
  have hR : Derives Ξ R := .hyp (Or.inl rfl)
  have hsum := ZFArithmetic.add_commute hZ1 _ _ _ _ hw1 (under hkW R) (.conjL hR) (.conjR hR)
  have hall : Derives Ξ (.all ((edge f.castSucc.castSucc k.castSucc.castSucc (Fin.last (m+1))).iff
      (iteration false w.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))))) := by
    apply Derives.allI
    have hZ2 := ZFContext.rename hZ1 Fin.castSucc
    have hw2 : Derives (Context.image Formula.raise Ξ) (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using Derives.rename Fin.castSucc hw1
    have ht2 : Derives (Context.image Formula.raise Ξ) (StructuralListTraceSyntax.trace w.castSucc.castSucc z.castSucc.castSucc e.castSucc.castSucc l.castSucc.castSucc d.castSucc.castSucc f.castSucc.castSucc n.castSucc.castSucc) := by
      simpa only [Formula.raise, StructuralListTraceSyntax.trace_rename] using Derives.rename Fin.castSucc ht1
    have hsum2 : Derives (Context.image Formula.raise Ξ) (sum w.castSucc.castSucc (Fin.last m).castSucc k.castSucc.castSucc l.castSucc.castSucc) := by
      simpa only [Formula.raise, sum_rename] using Derives.rename Fin.castSucc hsum
    exact trace_iff hZ2 _ _ _ _ _ _ _ _ _ _ hw2 ht2 (Derives.rename Fin.castSucc (.conjL hR))
      (Derives.rename Fin.castSucc (under hkW R)) hsum2
  have hout := intro_reverse _ _ _ _ _ _ (.conjL hR) hsum hall
  simpa only [Formula.raise, reverseExists_rename] using hout
end PPAC.Migration.Internal.StructuralListPositions
