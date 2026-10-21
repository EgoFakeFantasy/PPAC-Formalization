import PPAC.Migration.Internal.NaturalMultiplicationAssociative

/-! 两侧分配及实际内部零后继作为乘法单位元的原核证明。 -/
namespace PPAC.Migration.Internal.NaturalMultiplicationAlgebraLaws
open Source SourceAlgebra SourceLogic OmegaSyntax NaturalAdditionSyntax ZFArithmetic
open NaturalMultiplicationSyntax (product product_rename)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem left_distributive_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b n d p q r : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w)) (hn : Derives Γ (.mem n w))
    (hd : Derives Γ (sum w a b d)) (hp : Derives Γ (product w a n p)) (hq : Derives Γ (product w b n q)) :
    Derives Γ ((product w d n r).iff (sum w p q r)) := by
  have hdW := add_range hZ _ _ _ _ hw ha hd
  have hpa := NaturalMultiplicationCommutative.commute hZ w a n p hw ha hn hp
  have hqb := NaturalMultiplicationCommutative.commute hZ w b n q hw hb hn hq
  have hi := NaturalMultiplicationDistributive.distributive_iff hZ w n a p b d q r hw hn ha hb hpa hd hqb
  apply Derives.conjI
  · apply Derives.impI
    have hm := NaturalMultiplicationCommutative.commute (ZFContext.add hZ _) w d n r (add hw _) (add hdW _) (add hn _) (.hyp (Or.inl rfl))
    exact .impE (add (.conjL hi) _) hm
  · apply Derives.impI
    have hm := Derives.impE (add (.conjR hi) _) (.hyp (Or.inl rfl))
    exact NaturalMultiplicationCommutative.commute (ZFContext.add hZ _) w n d r (add hw _) (add hn _) (add hdW _) hm

theorem right_unit {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a z e : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hz : Derives Γ (empty z)) (he : Derives Γ (successor e z)) :
    Derives Γ (product w a e a) := by
  have hzW := OmegaStructureAlgebra.zero_member w z (ZFContext.arithmetic hZ).base.extensionality hw hz
  have hzProd := mul_zero hZ w a z z hw ha hz hz
  have hall := NaturalAdditionZero.all_left_zero (ZFContext.arithmetic hZ) w z (ZFContext.recAdd hZ)
    (ZFContext.separation hZ NaturalAdditionZero.matrix) hw hz
  have hi : Derives Γ ((Formula.mem a w).imp (sum w z a a)) := by
    simpa only [Formula.instantiate, Formula.rename, sum_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.allE a hall
  exact mul_succ_backward hZ w a z e z a hw ha hzW he hzProd (.impE hi ha)

theorem product_iff_value {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a n p y : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hn : Derives Γ (.mem n w)) (hp : Derives Γ (product w a n p)) :
    Derives Γ ((product w a n y).iff (.equal y p)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact mul_unique (ZFContext.add hZ _) w a n y p (add hw _) (add ha _) (add hn _) (.hyp (Or.inl rfl)) (add hp _)
  · apply Derives.impI
    exact NaturalMultiplicationSyntax.output_subst w a n p y (eq_symm (.hyp (Or.inl rfl))) (add hp _)

theorem unit_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a z e y : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hz : Derives Γ (empty z)) (he : Derives Γ (successor e z)) :
    Derives Γ (((product w a e y).iff (.equal y a)).conj ((product w e a y).iff (.equal y a))) := by
  have hzW := OmegaStructureAlgebra.zero_member w z (ZFContext.arithmetic hZ).base.extensionality hw hz
  have heW := OmegaStructureAlgebra.successor_member w e z (ZFContext.arithmetic hZ).base.extensionality hw hzW he
  have hr := right_unit hZ w a z e hw ha hz he
  have hl := NaturalMultiplicationCommutative.commute hZ w a e a hw ha heW hr
  exact .conjI (product_iff_value hZ w a e a y hw ha heW hr) (product_iff_value hZ w e a a y hw heW ha hl)
end PPAC.Migration.Internal.NaturalMultiplicationAlgebraLaws
