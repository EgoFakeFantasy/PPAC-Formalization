import PPAC.Migration.Internal.GodelPairCore

/-! 原配数多项式所需的和界、平方后继式及真实自然顺序引理。 -/
namespace PPAC.Migration.Internal.GodelPairArithmetic
open Source SourceAlgebra SourceLogic OmegaSyntax ZFArithmetic
open NaturalAdditionSyntax (sum)
open NaturalMultiplicationSyntax (product)
open NaturalAdditionBounds (below)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem sum_left_bound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b p : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w))
    (hp : Derives Γ (sum w a b p)) : Derives Γ (below a p) :=
  NaturalAdditionBounds.lower_bound (ZFContext.arithmetic hZ) w a b p (ZFContext.recAdd hZ)
    (ZFContext.separation hZ NaturalAdditionBounds.matrix) hw ha hb hp

theorem sum_right_bound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b p : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w))
    (hp : Derives Γ (sum w a b p)) : Derives Γ (below b p) :=
  sum_left_bound hZ w b a p hw hb ha (add_commute hZ w a b p hw ha hb hp)

theorem cancel_sum_left {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w t a b p : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (.mem t w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w))
    (hp : Derives Γ (sum w t a p)) (hq : Derives Γ (sum w t b p)) : Derives Γ (.equal a b) :=
  NaturalDifference.unique hZ w t p a b hw ht ha hb hp hq

theorem square_subst {m} {Γ : Context m} (w a b q : Fin m) (he : Derives Γ (.equal a b))
    (hq : Derives Γ (product w a a q)) : Derives Γ (product w b b q) :=
  NaturalMultiplicationTransport.index_subst w b a b q he (NaturalMultiplicationTransport.left_subst w a b a q he hq)

theorem square_monotone {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b p q : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w))
    (hp : Derives Γ (product w a a p)) (hq : Derives Γ (product w b b q)) (hl : Derives Γ (below a b)) :
    Derives Γ (below p q) := by
  apply Derives.disjE hl
  · let E := Formula.equal a b
    let Δ := Context.add E Γ
    have hZ1 : ZFContext.Evidence Δ := ZFContext.add hZ E
    have hsq := square_subst w a b p (Derives.hyp (Γ := Δ) (Or.inl rfl)) (add hp E)
    exact .disjL (mul_unique hZ1 w b b p q (add hw E) (add hb E) (add hb E) hsq (add hq E))
  · exact .disjR (NaturalArithmeticBounds.square_strict (ZFContext.add hZ _) w a b p q (add hw _) (add ha _) (add hb _) (add hp _) (add hq _) (.hyp (Or.inl rfl)))

theorem successor_below {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b s : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w))
    (hs : Derives Γ (successor s a)) (hab : Derives Γ (.mem a b)) : Derives Γ (below s b) := by
  have hsW := OmegaStructureAlgebra.successor_member w s a (ZFContext.arithmetic hZ).base.extensionality hw ha hs
  apply Derives.disjE (NaturalOrderBasic.compare hZ w s b hw hsW hb)
  · exact .disjL (.hyp (Or.inl rfl))
  · apply Derives.disjE (.hyp (Or.inl rfl))
    · exact .disjR (.hyp (Or.inl rfl))
    · let C := (Formula.mem s b).disj (.mem b s)
      let Δ := Context.add (Formula.mem b s) (Context.add C Γ)
      have hZ2 : ZFContext.Evidence Δ := ZFContext.add (ZFContext.add hZ C) _
      have hba := NaturalOrderBasic.member_successor b a s (add (add hs C) _) (Derives.hyp (Γ := Δ) (Or.inl rfl))
      exact .botE (NaturalOrderBasic.below_not_reverse hZ2 w b a (add (add hw C) _) (add (add hb C) _) hba (add (add hab C) _))

theorem square_step {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a s q t u v : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hs : Derives Γ (successor s a))
    (hq : Derives Γ (product w a a q)) (hv : Derives Γ (product w s s v))
    (ht : Derives Γ (sum w q a t)) (hu : Derives Γ (sum w t a u)) : Derives Γ (successor v u) := by
  have hsW := OmegaStructureAlgebra.successor_member w s a (ZFContext.arithmetic hZ).base.extensionality hw ha hs
  have hqW := mul_range hZ _ _ _ _ hw hq
  have htW := add_range hZ _ _ _ _ hw hqW ht
  have hsa := NaturalMultiplicationShift.shift_at hZ w a s a q t hw ha hs ha hq ht
  have hts := mul_succ_forward hZ w s a s t v hw hsW ha hs hsa hv
  exact add_succ_forward hZ w t a s u v hw htW ha hs hu hts
end PPAC.Migration.Internal.GodelPairArithmetic
