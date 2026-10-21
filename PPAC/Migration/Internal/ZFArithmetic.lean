import PPAC.Migration.Internal.ZFContext

/-! 原ZF中的既有算术引理直接组合；所有前提均为原公理映射和对象公式推导。 -/
namespace PPAC.Migration.Internal.ZFArithmetic
open Source SourceAlgebra SourceLogic OmegaSyntax NaturalAdditionSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem add_exists {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a n : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hn : Derives Γ (.mem n w)) :
    Derives Γ (existsSum w a n) := NaturalAdditionCore.exists_sum (ZFContext.arithmetic hZ) w a n (ZFContext.recAdd hZ) hw ha hn

theorem add_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a n y z : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w))
    (hy : Derives Γ (sum w a n y)) (hz : Derives Γ (sum w a n z)) : Derives Γ (.equal y z) :=
  NaturalAdditionCore.unique (ZFContext.arithmetic hZ) w a n y z (ZFContext.recAdd hZ) hw hn hy hz

theorem add_range {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a n y : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hy : Derives Γ (sum w a n y)) : Derives Γ (.mem y w) :=
  NaturalAdditionCore.closure w a n y (ZFContext.arithmetic hZ).base.extensionality hw ha hy

theorem add_commute {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a n y : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hn : Derives Γ (.mem n w))
    (hy : Derives Γ (sum w a n y)) : Derives Γ (sum w n a y) :=
  NaturalAdditionCommutative.commute (ZFContext.arithmetic hZ) w a n y (ZFContext.recAdd hZ)
    (ZFContext.separation hZ NaturalAdditionCommutative.matrix) (ZFContext.separation hZ NaturalAdditionShift.matrix)
    (ZFContext.separation hZ NaturalAdditionZero.matrix) hw ha hn hy

theorem add_associate {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b u n v y : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w)) (hn : Derives Γ (.mem n w))
    (hab : Derives Γ (sum w a b u)) (hv : Derives Γ (sum w b n v)) (hy : Derives Γ (sum w u n y)) : Derives Γ (sum w a v y) :=
  NaturalAdditionAssociative.associate (ZFContext.arithmetic hZ) w a b u n v y (ZFContext.recAdd hZ)
    (ZFContext.separation hZ NaturalAdditionAssociative.matrix) hw ha hb hn hab hv hy

theorem add_unassociate {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b u n v y : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w)) (hn : Derives Γ (.mem n w))
    (hab : Derives Γ (sum w a b u)) (hv : Derives Γ (sum w b n v)) (hy : Derives Γ (sum w a v y)) : Derives Γ (sum w u n y) :=
  NaturalAdditionAlgebraLaws.associate_backward (ZFContext.arithmetic hZ) w a b u n v y (ZFContext.recAdd hZ)
    (ZFContext.separation hZ NaturalAdditionAssociative.matrix) hw ha hb hn hab hv hy

theorem add_zero {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a z : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hz : Derives Γ (empty z)) : Derives Γ (sum w a z a) :=
  NaturalAdditionLaws.zero_value (ZFContext.arithmetic hZ) w a z (ZFContext.recAdd hZ) hw ha hz

theorem add_succ_forward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a n s y z : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hn : Derives Γ (.mem n w))
    (hs : Derives Γ (successor s n)) (hy : Derives Γ (sum w a n y)) (hz : Derives Γ (sum w a s z)) : Derives Γ (successor z y) :=
  NaturalAdditionLaws.successor_forward (ZFContext.arithmetic hZ) w a n s y z (ZFContext.recAdd hZ) hw ha hn hs hy hz

theorem add_succ_backward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a n s y z : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hn : Derives Γ (.mem n w))
    (hs : Derives Γ (successor s n)) (hy : Derives Γ (sum w a n y)) (hz : Derives Γ (successor z y)) : Derives Γ (sum w a s z) :=
  NaturalAdditionLaws.successor_backward (ZFContext.arithmetic hZ) w a n s y z (ZFContext.recAdd hZ) hw ha hn hs hy hz

theorem mul_exists {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a n : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hn : Derives Γ (.mem n w)) :
    Derives Γ (NaturalMultiplicationSyntax.existsProduct w a n) :=
  NaturalMultiplicationCore.exists_product (ZFContext.arithmetic hZ) w a n (ZFContext.recAdd hZ) (ZFContext.recMul hZ) hw ha hn

theorem mul_range {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a n y : Fin m)
    (hw : Derives Γ (omega w)) (hy : Derives Γ (NaturalMultiplicationSyntax.product w a n y)) : Derives Γ (.mem y w) :=
  NaturalMultiplicationCore.closure w a n y (ZFContext.arithmetic hZ).base.extensionality hw hy

theorem mul_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a n y z : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hn : Derives Γ (.mem n w))
    (hy : Derives Γ (NaturalMultiplicationSyntax.product w a n y)) (hz : Derives Γ (NaturalMultiplicationSyntax.product w a n z)) : Derives Γ (.equal y z) :=
  NaturalMultiplicationCore.unique (ZFContext.arithmetic hZ) w a n y z (ZFContext.recAdd hZ) (ZFContext.recMul hZ) hw ha hn hy hz

theorem mul_succ_forward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a n s y z : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hn : Derives Γ (.mem n w))
    (hs : Derives Γ (successor s n)) (hy : Derives Γ (NaturalMultiplicationSyntax.product w a n y))
    (hz : Derives Γ (NaturalMultiplicationSyntax.product w a s z)) : Derives Γ (sum w y a z) :=
  NaturalMultiplicationLaws.successor_forward (ZFContext.arithmetic hZ) w a n s y z (ZFContext.recAdd hZ) (ZFContext.recMul hZ) hw ha hn hs hy hz

theorem mul_succ_backward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a n s y z : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hn : Derives Γ (.mem n w))
    (hs : Derives Γ (successor s n)) (hy : Derives Γ (NaturalMultiplicationSyntax.product w a n y))
    (hz : Derives Γ (sum w y a z)) : Derives Γ (NaturalMultiplicationSyntax.product w a s z) :=
  NaturalMultiplicationLaws.successor_backward (ZFContext.arithmetic hZ) w a n s y z (ZFContext.recAdd hZ) (ZFContext.recMul hZ) hw ha hn hs hy hz

theorem mul_zero {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a n y : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hn : Derives Γ (empty n))
    (hy : Derives Γ (empty y)) : Derives Γ (NaturalMultiplicationSyntax.product w a n y) :=
  NaturalMultiplicationLaws.zero_backward (ZFContext.arithmetic hZ) w a n y (ZFContext.recAdd hZ) (ZFContext.recMul hZ) hw ha hn hy

theorem induction {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (p : Formula (n+1)) (ρ : Fin n → Fin m) (w : Fin m)
    (hw : Derives Γ (omega w)) (hb : Derives Γ (OmegaInductionSyntax.base p ρ))
    (hs : Derives Γ (OmegaInductionSyntax.step p ρ w)) : Derives Γ (OmegaInductionSyntax.holds p ρ w) :=
  OmegaInduction.induction_on_omega p ρ w (ZFContext.separation hZ p) hw hb hs
end PPAC.Migration.Internal.ZFArithmetic
