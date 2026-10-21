import PPAC.Migration.Internal.NaturalDifferencePositive

/-! 以实际内部差值重排加法，证明加法保持并反映真实自然顺序。 -/
namespace PPAC.Migration.Internal.NaturalAdditionMonotone
open Source SourceAlgebra SourceLogic OmegaSyntax ZFArithmetic
open NaturalAdditionSyntax (sum sum_rename)
open NaturalAdditionBounds (below below_rename)
open NaturalDifferenceSyntax (witness existsDifference positiveWitness positiveExists)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem translate_difference {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b n d x y : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hn : Derives Γ (.mem n w)) (hd : Derives Γ (.mem d w))
    (hs : Derives Γ (sum w a d b)) (hx : Derives Γ (sum w a n x)) (hy : Derives Γ (sum w b n y)) : Derives Γ (sum w x d y) :=
  NaturalAdditionReassociation.swap_middle hZ w a d n b x y hw ha hd hn hs hx hy

theorem monotone {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b n x y : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w)) (hn : Derives Γ (.mem n w))
    (hx : Derives Γ (sum w a n x)) (hy : Derives Γ (sum w b n y)) (hl : Derives Γ (below a b)) : Derives Γ (below x y) := by
  have hd := NaturalDifference.exists_of_below hZ w a b hw ha hb hl
  let D := witness w.castSucc a.castSucc b.castSucc (Fin.last m)
  let Ξ := Context.add D (Context.image Formula.raise Γ)
  change Derives Γ (.ex D) at hd
  apply Derives.exE (p := D) hd
  have hZ1 : ZFContext.Evidence Ξ := ZFContext.under hZ D
  have hw1 : Derives Ξ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw D
  have hx1 : Derives Ξ (sum w.castSucc a.castSucc n.castSucc x.castSucc) := by simpa only [Formula.raise, sum_rename] using under hx D
  have hy1 : Derives Ξ (sum w.castSucc b.castSucc n.castSucc y.castSucc) := by simpa only [Formula.raise, sum_rename] using under hy D
  have hD : Derives Ξ D := .hyp (Or.inl rfl)
  have hxy := translate_difference hZ1 _ _ _ _ _ _ _ hw1 (under ha D) (under hn D) (.conjL hD) (.conjR hD) hx1 hy1
  have hxW := add_range hZ1 _ _ _ _ hw1 (under ha D) hx1
  have hlo := NaturalAdditionBounds.lower_bound (ZFContext.arithmetic hZ1) _ _ _ _ (ZFContext.recAdd hZ1)
    (ZFContext.separation hZ1 NaturalAdditionBounds.matrix) hw1 hxW (.conjL hD) hxy
  simpa only [Formula.raise, below_rename] using hlo

theorem strict_monotone {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b n x y : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w)) (hn : Derives Γ (.mem n w))
    (hx : Derives Γ (sum w a n x)) (hy : Derives Γ (sum w b n y)) (hl : Derives Γ (.mem a b)) : Derives Γ (.mem x y) := by
  have hd := NaturalDifferencePositive.positive_of_member hZ w a b hw ha hb hl
  let D := positiveWitness w.castSucc a.castSucc b.castSucc (Fin.last m)
  let Ξ := Context.add D (Context.image Formula.raise Γ)
  change Derives Γ (.ex D) at hd
  apply Derives.exE (p := D) hd
  have hZ1 : ZFContext.Evidence Ξ := ZFContext.under hZ D
  have hw1 : Derives Ξ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw D
  have hx1 : Derives Ξ (sum w.castSucc a.castSucc n.castSucc x.castSucc) := by simpa only [Formula.raise, sum_rename] using under hx D
  have hy1 : Derives Ξ (sum w.castSucc b.castSucc n.castSucc y.castSucc) := by simpa only [Formula.raise, sum_rename] using under hy D
  have hD : Derives Ξ D := .hyp (Or.inl rfl)
  have hxy := translate_difference hZ1 _ _ _ _ _ _ _ hw1 (under ha D) (under hn D) (.conjL (.conjL hD)) (.conjR hD) hx1 hy1
  have hxW := add_range hZ1 _ _ _ _ hw1 (under ha D) hx1
  exact NaturalDifferencePositive.sum_positive hZ1 _ _ _ _ hw1 hxW (.conjL (.conjL hD)) hxy (.conjR (.conjL hD))

theorem reflect {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b n x y : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w)) (hn : Derives Γ (.mem n w))
    (hx : Derives Γ (sum w a n x)) (hy : Derives Γ (sum w b n y)) (hl : Derives Γ (below x y)) : Derives Γ (below a b) := by
  have hxW := add_range hZ _ _ _ _ hw ha hx
  apply Derives.disjE (NaturalOrderBasic.compare hZ w a b hw ha hb)
  · exact .disjL (.hyp (Or.inl rfl))
  · apply Derives.disjE (.hyp (Or.inl rfl))
    · exact .disjR (.hyp (Or.inl rfl))
    · let C := (Formula.mem a b).disj (.mem b a)
      let Δ := Context.add (Formula.mem b a) (Context.add C Γ)
      have hZ2 : ZFContext.Evidence Δ := ZFContext.add (ZFContext.add hZ C) _
      have hw2 : Derives Δ (omega w) := add (add hw C) _
      have hbad := strict_monotone hZ2 w b a n y x hw2 (add (add hb C) _) (add (add ha C) _) (add (add hn C) _)
        (add (add hy C) _) (add (add hx C) _) (.hyp (Or.inl rfl))
      exact .botE (NaturalOrderBasic.below_not_reverse hZ2 w x y hw2 (add (add hxW C) _) (add (add hl C) _) hbad)

theorem weak_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b n x y : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w)) (hn : Derives Γ (.mem n w))
    (hx : Derives Γ (sum w a n x)) (hy : Derives Γ (sum w b n y)) : Derives Γ ((below a b).iff (below x y)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact monotone (ZFContext.add hZ _) _ _ _ _ _ _ (add hw _) (add ha _) (add hb _) (add hn _) (add hx _) (add hy _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact reflect (ZFContext.add hZ _) _ _ _ _ _ _ (add hw _) (add ha _) (add hb _) (add hn _) (add hx _) (add hy _) (.hyp (Or.inl rfl))

theorem strict_reflect {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b n x y : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w)) (hn : Derives Γ (.mem n w))
    (hx : Derives Γ (sum w a n x)) (hy : Derives Γ (sum w b n y)) (hl : Derives Γ (.mem x y)) : Derives Γ (.mem a b) := by
  have hi := reflect hZ w a b n x y hw ha hb hn hx hy (.disjR hl)
  apply Derives.disjE hi
  · let E := Formula.equal a b
    let Δ := Context.add E Γ
    have hZ1 : ZFContext.Evidence Δ := ZFContext.add hZ E
    have hs := NaturalAdditionTransport.left_subst w a b n x (Derives.hyp (Γ := Δ) (Or.inl rfl)) (add hx E)
    have heq := add_unique hZ1 w b n x y (add hw E) (add hn E) hs (add hy E)
    have hself := UnorderedPairLogic.mem_container_subst y x x (eq_symm heq) (add hl E)
    exact .botE (.impE (NaturalOrderBasic.nonself hZ1 x) hself)
  · exact .hyp (Or.inl rfl)

theorem strict_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b n x y : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w)) (hn : Derives Γ (.mem n w))
    (hx : Derives Γ (sum w a n x)) (hy : Derives Γ (sum w b n y)) : Derives Γ ((Formula.mem a b).iff (.mem x y)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact strict_monotone (ZFContext.add hZ _) _ _ _ _ _ _ (add hw _) (add ha _) (add hb _) (add hn _) (add hx _) (add hy _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact strict_reflect (ZFContext.add hZ _) _ _ _ _ _ _ (add hw _) (add ha _) (add hb _) (add hn _) (add hx _) (add hy _) (.hyp (Or.inl rfl))

theorem left_weak_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b n x y : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w)) (hn : Derives Γ (.mem n w))
    (hx : Derives Γ (sum w n a x)) (hy : Derives Γ (sum w n b y)) : Derives Γ ((below a b).iff (below x y)) :=
  weak_iff hZ w a b n x y hw ha hb hn (add_commute hZ w n a x hw hn ha hx) (add_commute hZ w n b y hw hn hb hy)

theorem left_strict_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b n x y : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w)) (hn : Derives Γ (.mem n w))
    (hx : Derives Γ (sum w n a x)) (hy : Derives Γ (sum w n b y)) : Derives Γ ((Formula.mem a b).iff (.mem x y)) :=
  strict_iff hZ w a b n x y hw ha hb hn (add_commute hZ w n a x hw hn ha hx) (add_commute hZ w n b y hw hn hb hy)
end PPAC.Migration.Internal.NaturalAdditionMonotone
