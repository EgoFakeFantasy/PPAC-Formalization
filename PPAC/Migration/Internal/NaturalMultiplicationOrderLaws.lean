import PPAC.Migration.Internal.NaturalMultiplicationMonotone

/-! 非零公共乘数下的顺序反射与消去；不把零乘数误纳入等价。 -/
namespace PPAC.Migration.Internal.NaturalMultiplicationOrderLaws
open Source SourceAlgebra SourceLogic OmegaSyntax ZFArithmetic
open NaturalMultiplicationSyntax (product)
open NaturalAdditionBounds (below)
open NaturalMultiplicationMonotone (monotone strict_monotone)

theorem reflect {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b n x y : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w)) (hn : Derives Γ (.mem n w))
    (hn0 : Derives Γ (empty n).neg) (hx : Derives Γ (product w a n x)) (hy : Derives Γ (product w b n y))
    (hl : Derives Γ (below x y)) : Derives Γ (below a b) := by
  have hxW := mul_range hZ _ _ _ _ hw hx
  apply Derives.disjE (NaturalOrderBasic.compare hZ w a b hw ha hb)
  · exact .disjL (.hyp (Or.inl rfl))
  · apply Derives.disjE (.hyp (Or.inl rfl))
    · exact .disjR (.hyp (Or.inl rfl))
    · let C := (Formula.mem a b).disj (.mem b a)
      let Δ := Context.add (Formula.mem b a) (Context.add C Γ)
      have hZ2 : ZFContext.Evidence Δ := ZFContext.add (ZFContext.add hZ C) _
      have hw2 : Derives Δ (omega w) := add (add hw C) _
      have hbad := strict_monotone hZ2 w b a n y x hw2 (add (add hb C) _) (add (add ha C) _) (add (add hn C) _)
        (add (add hn0 C) _) (add (add hy C) _) (add (add hx C) _) (.hyp (Or.inl rfl))
      exact .botE (NaturalOrderBasic.below_not_reverse hZ2 w x y hw2 (add (add hxW C) _) (add (add hl C) _) hbad)

theorem weak_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b n x y : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w)) (hn : Derives Γ (.mem n w))
    (hn0 : Derives Γ (empty n).neg) (hx : Derives Γ (product w a n x)) (hy : Derives Γ (product w b n y)) :
    Derives Γ ((below a b).iff (below x y)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact monotone (ZFContext.add hZ _) _ _ _ _ _ _ (add hw _) (add ha _) (add hb _) (add hn _) (add hx _) (add hy _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact reflect (ZFContext.add hZ _) _ _ _ _ _ _ (add hw _) (add ha _) (add hb _) (add hn _) (add hn0 _) (add hx _) (add hy _) (.hyp (Or.inl rfl))

theorem strict_reflect {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b n x y : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w)) (hn : Derives Γ (.mem n w))
    (hn0 : Derives Γ (empty n).neg) (hx : Derives Γ (product w a n x)) (hy : Derives Γ (product w b n y))
    (hl : Derives Γ (.mem x y)) : Derives Γ (.mem a b) := by
  have hi := reflect hZ w a b n x y hw ha hb hn hn0 hx hy (.disjR hl)
  apply Derives.disjE hi
  · let E := Formula.equal a b
    let Δ := Context.add E Γ
    have hZ1 : ZFContext.Evidence Δ := ZFContext.add hZ E
    have hs := NaturalMultiplicationTransport.left_subst w a b n x (Derives.hyp (Γ := Δ) (Or.inl rfl)) (add hx E)
    have heq := mul_unique hZ1 w b n x y (add hw E) (add hb E) (add hn E) hs (add hy E)
    have hself := UnorderedPairLogic.mem_container_subst y x x (eq_symm heq) (add hl E)
    exact .botE (.impE (NaturalOrderBasic.nonself hZ1 x) hself)
  · exact .hyp (Or.inl rfl)

theorem strict_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b n x y : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w)) (hn : Derives Γ (.mem n w))
    (hn0 : Derives Γ (empty n).neg) (hx : Derives Γ (product w a n x)) (hy : Derives Γ (product w b n y)) :
    Derives Γ ((Formula.mem a b).iff (.mem x y)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact strict_monotone (ZFContext.add hZ _) _ _ _ _ _ _ (add hw _) (add ha _) (add hb _) (add hn _) (add hn0 _) (add hx _) (add hy _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact strict_reflect (ZFContext.add hZ _) _ _ _ _ _ _ (add hw _) (add ha _) (add hb _) (add hn _) (add hn0 _) (add hx _) (add hy _) (.hyp (Or.inl rfl))

theorem left_monotone {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b n x y : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w)) (hn : Derives Γ (.mem n w))
    (hx : Derives Γ (product w n a x)) (hy : Derives Γ (product w n b y)) (hl : Derives Γ (below a b)) : Derives Γ (below x y) :=
  monotone hZ w a b n x y hw ha hb hn (NaturalMultiplicationCommutative.commute hZ w n a x hw hn ha hx)
    (NaturalMultiplicationCommutative.commute hZ w n b y hw hn hb hy) hl

theorem left_weak_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b n x y : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w)) (hn : Derives Γ (.mem n w))
    (hn0 : Derives Γ (empty n).neg) (hx : Derives Γ (product w n a x)) (hy : Derives Γ (product w n b y)) :
    Derives Γ ((below a b).iff (below x y)) :=
  weak_iff hZ w a b n x y hw ha hb hn hn0 (NaturalMultiplicationCommutative.commute hZ w n a x hw hn ha hx)
    (NaturalMultiplicationCommutative.commute hZ w n b y hw hn hb hy)

theorem left_strict_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b n x y : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w)) (hn : Derives Γ (.mem n w))
    (hn0 : Derives Γ (empty n).neg) (hx : Derives Γ (product w n a x)) (hy : Derives Γ (product w n b y)) :
    Derives Γ ((Formula.mem a b).iff (.mem x y)) :=
  strict_iff hZ w a b n x y hw ha hb hn hn0 (NaturalMultiplicationCommutative.commute hZ w n a x hw hn ha hx)
    (NaturalMultiplicationCommutative.commute hZ w n b y hw hn hb hy)

theorem cancel {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b n p : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w)) (hn : Derives Γ (.mem n w))
    (hn0 : Derives Γ (empty n).neg) (hp : Derives Γ (product w a n p)) (hq : Derives Γ (product w b n p)) : Derives Γ (.equal a b) := by
  have hab := reflect hZ w a b n p p hw ha hb hn hn0 hp hq (.disjL (.eqRefl p))
  have hba := reflect hZ w b a n p p hw hb ha hn hn0 hq hp (.disjL (.eqRefl p))
  exact NaturalOrderBasic.antisymmetric hZ w a b hw ha hab hba

theorem left_cancel {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b n p : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w)) (hn : Derives Γ (.mem n w))
    (hn0 : Derives Γ (empty n).neg) (hp : Derives Γ (product w n a p)) (hq : Derives Γ (product w n b p)) : Derives Γ (.equal a b) :=
  cancel hZ w a b n p hw ha hb hn hn0 (NaturalMultiplicationCommutative.commute hZ w n a p hw hn ha hp)
    (NaturalMultiplicationCommutative.commute hZ w n b p hw hn hb hq)
end PPAC.Migration.Internal.NaturalMultiplicationOrderLaws
