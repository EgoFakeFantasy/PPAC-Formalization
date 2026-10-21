import PPAC.Migration.Internal.StructuralListSuffixBase

/-! 原Cons前置保持源序列偏移字段；零点与后继字段逐内部索引核对。 -/
namespace PPAC.Migration.Internal.StructuralListSuffixMatch
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax SequenceSyntax NaturalAdditionSyntax StructuralListSyntax StructuralListFieldSyntax StructuralListSuffixSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem zero_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w f l k h t n i q y : Fin m)
    (hw : Derives Γ (omega w)) (hf : Derives Γ (sequence f l w)) (hh : Derives Γ (.mem h w)) (ht : Derives Γ (.mem t w))
    (hc : Derives Γ (consCode w h t n)) (he : Derives Γ (edge f k h)) (hi : Derives Γ (empty i))
    (hs : Derives Γ (sum w k i q)) : Derives Γ ((field w n i y).iff (edge f q y)) := by
  have hqk := NaturalRecursionLaws.evaluation_zero NaturalSuccessorStep.matrix (NaturalAdditionSyntax.params w) w k i q hi hs
  have hzero := StructuralListFieldCons.zero_iff hZ w h t n i y hw hh ht hc hi
  have hread : Derives Γ ((Formula.equal y h).iff (edge f q y)) := by
    apply Derives.conjI
    · apply Derives.impI
      have hey := GraphPointwiseSyntax.edge_subst_output f k h y (eq_symm (.hyp (Or.inl rfl))) (add he _)
      exact StructuralListTraceOrder.edge_input_subst f k q y (eq_symm (add hqk _)) hey
    · apply Derives.impI
      have hey := StructuralListTraceOrder.edge_input_subst f q k y (add hqk _) (.hyp (Or.inl rfl))
      exact GraphProperties.single_valued f l k y h (add (ZFContext.arithmetic hZ).base.extensionality _) (add (.conjL hf) _) hey (add he _)
  exact StructuralListSuffixArithmetic.iff_trans hzero hread

theorem point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w f l k j r s h t n i q y : Fin m)
    (hw : Derives Γ (omega w)) (hf : Derives Γ (sequence f l w)) (hr : Derives Γ (.mem r w)) (hk : Derives Γ (.mem k w))
    (hs : Derives Γ (successor s r)) (hj : Derives Γ (successor j k)) (hh : Derives Γ (.mem h w)) (ht : Derives Γ (.mem t w))
    (hc : Derives Γ (consCode w h t n)) (he : Derives Γ (edge f k h)) (ha : Derives Γ (aligned w f j r t))
    (hm : Derives Γ (.mem i s)) (hq : Derives Γ (sum w k i q)) : Derives Γ ((field w n i y).iff (edge f q y)) := by
  have hsW := OmegaStructureAlgebra.successor_member w s r (ZFContext.arithmetic hZ).base.extensionality hw hr hs
  have hiW := StructuralListTraceOrder.member_member hZ w i s hw hsW hm
  have hd := OmegaStructureAlgebra.decomposition_at w i (OmegaStructureInduction.decomposition w
    (ZFContext.separation hZ OmegaStructureSyntax.splitMatrix) hw) hiW
  apply Derives.disjE hd
  · exact zero_point (ZFContext.add hZ _) _ _ _ _ _ _ _ _ _ _ (add hw _) (add hf _) (add hh _) (add ht _) (add hc _) (add he _) (.hyp (Or.inl rfl)) (add hq _)
  · let P := OmegaStructureSyntax.predecessor w i
    let Γp := Context.add P Γ
    let Q := (Formula.mem (Fin.last m) w.castSucc).conj (successor i.castSucc (Fin.last m))
    let Δ := Context.add Q (Context.image Formula.raise Γp)
    have hqEx : Derives Γp (.ex Q) := .hyp (Or.inl rfl)
    apply Derives.exE (p := Q) hqEx
    have hZ1 : ZFContext.Evidence Δ := ZFContext.under (ZFContext.add hZ P) Q
    have lift {a : Formula m} (ha : Derives Γ a) : Derives Δ a.raise := under (add ha P) Q
    have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using lift hw
    have hs1 : Derives Δ (successor s.castSucc r.castSucc) := by simpa only [Formula.raise, successor_rename] using lift hs
    have hj1 : Derives Δ (successor j.castSucc k.castSucc) := by simpa only [Formula.raise, successor_rename] using lift hj
    have hc1 : Derives Δ (consCode w.castSucc h.castSucc t.castSucc n.castSucc) := by simpa only [Formula.raise, consCode_rename] using lift hc
    have ha1 : Derives Δ (aligned w.castSucc f.castSucc j.castSucc r.castSucc t.castSucc) := by simpa only [Formula.raise, aligned_rename] using lift ha
    have hq1 : Derives Δ (sum w.castSucc k.castSucc i.castSucc q.castSucc) := by simpa only [Formula.raise, sum_rename] using lift hq
    have hQ : Derives Δ Q := .hyp (Or.inl rfl)
    have hpr := StructuralListSuffixArithmetic.predecessor_inside hZ1 _ _ _ _ _ hw1 (lift hr) hs1 (.conjR hQ) (lift hm)
    have hoff := StructuralListSuffixArithmetic.offset_successor hZ1 _ _ _ _ _ _ hw1 (lift hk) (.conjL hQ) hj1 (.conjR hQ) hq1
    have hold := aligned_at _ _ _ _ _ _ _ y.castSucc ha1 hpr hoff
    have hnew := StructuralListFieldCons.successor_iff hZ1 _ _ _ _ _ _ y.castSucc hw1 (lift hh) (lift ht) (.conjL hQ) (.conjR hQ) hc1
    have hout := StructuralListSuffixArithmetic.iff_trans hnew hold
    simpa only [Formula.raise, Formula.rename, Formula.iff, field_rename, edge_rename] using hout

theorem aligned_cons {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w f l k j r s h t n : Fin m)
    (hw : Derives Γ (omega w)) (hf : Derives Γ (sequence f l w)) (hr : Derives Γ (.mem r w)) (hk : Derives Γ (.mem k w))
    (hs : Derives Γ (successor s r)) (hj : Derives Γ (successor j k)) (hh : Derives Γ (.mem h w)) (ht : Derives Γ (.mem t w))
    (hc : Derives Γ (consCode w h t n)) (he : Derives Γ (edge f k h)) (ha : Derives Γ (aligned w f j r t)) : Derives Γ (aligned w f k s n) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let A := (Formula.mem (Fin.last m).castSucc.castSucc s.castSucc.castSucc.castSucc).conj
    (sum w.castSucc.castSucc.castSucc k.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc)
  let Δ := Context.add A (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ)))
  have hZ3 : ZFContext.Evidence Δ := ZFContext.add (ZFContext.rename (ZFContext.rename (ZFContext.rename hZ Fin.castSucc) Fin.castSucc) Fin.castSucc) A
  have lift {a : Formula m} (ha : Derives Γ a) : Derives Δ a.raise.raise.raise := add (OrdinalRestriction.raise_three ha) A
  have hw3 : Derives Δ (omega w.castSucc.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using lift hw
  have hf3 : Derives Δ (sequence f.castSucc.castSucc.castSucc l.castSucc.castSucc.castSucc w.castSucc.castSucc.castSucc) := by simpa only [Formula.raise, sequence_rename] using lift hf
  have hs3 : Derives Δ (successor s.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc) := by simpa only [Formula.raise, successor_rename] using lift hs
  have hj3 : Derives Δ (successor j.castSucc.castSucc.castSucc k.castSucc.castSucc.castSucc) := by simpa only [Formula.raise, successor_rename] using lift hj
  have hc3 : Derives Δ (consCode w.castSucc.castSucc.castSucc h.castSucc.castSucc.castSucc t.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc) := by simpa only [Formula.raise, consCode_rename] using lift hc
  have he3 : Derives Δ (edge f.castSucc.castSucc.castSucc k.castSucc.castSucc.castSucc h.castSucc.castSucc.castSucc) := by simpa only [Formula.raise, edge_rename] using lift he
  have ha3 : Derives Δ (aligned w.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc j.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc t.castSucc.castSucc.castSucc) := by simpa only [Formula.raise, aligned_rename] using lift ha
  have hA : Derives Δ A := .hyp (Or.inl rfl)
  exact point hZ3 _ _ _ _ _ _ _ _ _ _ _ _ _ hw3 hf3 (lift hr) (lift hk) hs3 hj3 (lift hh) (lift ht) hc3 he3 ha3 (.conjL hA) (.conjR hA)
end PPAC.Migration.Internal.StructuralListSuffixMatch
