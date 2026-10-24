import PPAC.Migration.Internal.FixedAxiomPacketArithmetic

/-! 真实叶字节包算术的自然范围、唯一性与标签单射；不调用宿主数值解释。 -/
namespace PPAC.Migration.Internal.FixedAxiomPacketFacts
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax FixedAxiomPacketSyntax FixedAxiomPacketArithmetic
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix NaturalMultiplicationSyntax.product NaturalAdditionSyntax.sum SyntaxNumeralSyntax.numeral


theorem field0 {m} {Γ : Context m} (tag : Nat) (w code : Fin m) (env : Fin 6 → Fin m)
    (hx : Derives Γ (FixedAxiomPacketSyntax.matrix tag w code env)) : Derives Γ (SyntaxNumeralSyntax.numeral 256 (env 0)) := .conjL (hx)

theorem field1 {m} {Γ : Context m} (tag : Nat) (w code : Fin m) (env : Fin 6 → Fin m)
    (hx : Derives Γ (FixedAxiomPacketSyntax.matrix tag w code env)) : Derives Γ (SyntaxNumeralSyntax.numeral tag (env 1)) := .conjL (.conjR (hx))

theorem field2 {m} {Γ : Context m} (tag : Nat) (w code : Fin m) (env : Fin 6 → Fin m)
    (hx : Derives Γ (FixedAxiomPacketSyntax.matrix tag w code env)) : Derives Γ (NaturalMultiplicationSyntax.product w (env 0) (env 0) (env 2)) := .conjL (.conjR (.conjR (hx)))

theorem field3 {m} {Γ : Context m} (tag : Nat) (w code : Fin m) (env : Fin 6 → Fin m)
    (hx : Derives Γ (FixedAxiomPacketSyntax.matrix tag w code env)) : Derives Γ (NaturalMultiplicationSyntax.product w (env 0) (env 2) (env 3)) := .conjL (.conjR (.conjR (.conjR (hx))))

theorem field4 {m} {Γ : Context m} (tag : Nat) (w code : Fin m) (env : Fin 6 → Fin m)
    (hx : Derives Γ (FixedAxiomPacketSyntax.matrix tag w code env)) : Derives Γ (NaturalMultiplicationSyntax.product w (env 0) (env 1) (env 4)) := .conjL (.conjR (.conjR (.conjR (.conjR (hx)))))

theorem field5 {m} {Γ : Context m} (tag : Nat) (w code : Fin m) (env : Fin 6 → Fin m)
    (hx : Derives Γ (FixedAxiomPacketSyntax.matrix tag w code env)) : Derives Γ (NaturalAdditionSyntax.sum w (env 3) (env 4) (env 5)) := .conjL (.conjR (.conjR (.conjR (.conjR (.conjR (hx))))))

theorem field6 {m} {Γ : Context m} (tag : Nat) (w code : Fin m) (env : Fin 6 → Fin m)
    (hx : Derives Γ (FixedAxiomPacketSyntax.matrix tag w code env)) : Derives Γ (successor code (env 5)) := .conjR (.conjR (.conjR (.conjR (.conjR (.conjR (hx))))))

theorem matrix_natural {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (w code : Fin m) (env : Fin 6 → Fin m)
    (hw : Derives Γ (omega w)) (hx : Derives Γ (FixedAxiomPacketSyntax.matrix tag w code env)) :
    Derives Γ (environmentNat 6 w env) := by
  have h0 := SyntaxNumerals.range hZ 256 w (env 0) hw (field0 tag w code env hx)
  have h1 := SyntaxNumerals.range hZ tag w (env 1) hw (field1 tag w code env hx)
  have h2 := ZFArithmetic.mul_range hZ w (env 0) (env 0) (env 2) hw (field2 tag w code env hx)
  have h3 := ZFArithmetic.mul_range hZ w (env 0) (env 2) (env 3) hw (field3 tag w code env hx)
  have h4 := ZFArithmetic.mul_range hZ w (env 0) (env 1) (env 4) hw (field4 tag w code env hx)
  have h5 := ZFArithmetic.add_range hZ w (env 3) (env 4) (env 5) hw h3 (field5 tag w code env hx)
  exact .conjI h0 (.conjI h1 (.conjI h2 (.conjI h3 (.conjI h4 (.conjI h5 HornRuleSyntax.truth_proved)))))

theorem matrix_range {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (w code : Fin m) (env : Fin 6 → Fin m)
    (hw : Derives Γ (omega w)) (hx : Derives Γ (FixedAxiomPacketSyntax.matrix tag w code env)) : Derives Γ (.mem code w) :=
  OmegaStructureAlgebra.successor_member w code (env 5) (ZFContext.arithmetic hZ).base.extensionality hw
    (environmentNat_at w env (matrix_natural hZ tag w code env hw hx) 5) (field6 tag w code env hx)

theorem matrix_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (w p q : Fin m) (xs ys : Fin 6 → Fin m)
    (hw : Derives Γ (omega w)) (hx : Derives Γ (FixedAxiomPacketSyntax.matrix tag w p xs))
    (hy : Derives Γ (FixedAxiomPacketSyntax.matrix tag w q ys)) : Derives Γ (.equal p q) := by
  have hN := matrix_natural hZ tag w p xs hw hx
  have hxN (i : Fin 6) := environmentNat_at w xs hN i
  have e0 := SyntaxNumerals.unique hZ 256 (xs 0) (ys 0) (field0 tag w p xs hx) (field0 tag w q ys hy)
  have e1 := SyntaxNumerals.unique hZ tag (xs 1) (ys 1) (field1 tag w p xs hx) (field1 tag w q ys hy)
  have h2 := mul_inputs w (ys 0) (ys 0) (xs 0) (xs 0) (ys 2) (eq_symm e0) (eq_symm e0) (field2 tag w q ys hy)
  have e2 := ZFArithmetic.mul_unique hZ w (xs 0) (xs 0) (xs 2) (ys 2) hw (hxN 0) (hxN 0) (field2 tag w p xs hx) h2
  have h3 := mul_inputs w (ys 0) (ys 2) (xs 0) (xs 2) (ys 3) (eq_symm e0) (eq_symm e2) (field3 tag w q ys hy)
  have e3 := ZFArithmetic.mul_unique hZ w (xs 0) (xs 2) (xs 3) (ys 3) hw (hxN 0) (hxN 2) (field3 tag w p xs hx) h3
  have h4 := mul_inputs w (ys 0) (ys 1) (xs 0) (xs 1) (ys 4) (eq_symm e0) (eq_symm e1) (field4 tag w q ys hy)
  have e4 := ZFArithmetic.mul_unique hZ w (xs 0) (xs 1) (xs 4) (ys 4) hw (hxN 0) (hxN 1) (field4 tag w p xs hx) h4
  have h5 := add_inputs w (ys 3) (ys 4) (xs 3) (xs 4) (ys 5) (eq_symm e3) (eq_symm e4) (field5 tag w q ys hy)
  have e5 := ZFArithmetic.add_unique hZ w (xs 3) (xs 4) (xs 5) (ys 5) hw (hxN 4) (field5 tag w p xs hx) h5
  exact OmegaUniversal.successor_unique p q (xs 5) (ZFContext.arithmetic hZ).base.extensionality
    (field6 tag w p xs hx) (GodelUnpairArithmetic.successor_base_subst q (ys 5) (xs 5) (eq_symm e5) (field6 tag w q ys hy))

theorem matrix_tag_equal {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k l : Nat) (w p : Fin m) (xs ys : Fin 6 → Fin m)
    (hw : Derives Γ (omega w)) (hx : Derives Γ (FixedAxiomPacketSyntax.matrix k w p xs))
    (hy : Derives Γ (FixedAxiomPacketSyntax.matrix l w p ys)) : Derives Γ (.equal (xs 1) (ys 1)) := by
  have hN := matrix_natural hZ k w p xs hw hx
  have hM := matrix_natural hZ l w p ys hw hy
  have hxN (i : Fin 6) := environmentNat_at w xs hN i
  have hyN (i : Fin 6) := environmentNat_at w ys hM i
  have e0 := SyntaxNumerals.unique hZ 256 (xs 0) (ys 0) (field0 k w p xs hx) (field0 l w p ys hy)
  have h2 := mul_inputs w (ys 0) (ys 0) (xs 0) (xs 0) (ys 2) (eq_symm e0) (eq_symm e0) (field2 l w p ys hy)
  have e2 := ZFArithmetic.mul_unique hZ w (xs 0) (xs 0) (xs 2) (ys 2) hw (hxN 0) (hxN 0) (field2 k w p xs hx) h2
  have h3 := mul_inputs w (ys 0) (ys 2) (xs 0) (xs 2) (ys 3) (eq_symm e0) (eq_symm e2) (field3 l w p ys hy)
  have e3 := ZFArithmetic.mul_unique hZ w (xs 0) (xs 2) (xs 3) (ys 3) hw (hxN 0) (hxN 2) (field3 k w p xs hx) h3
  have e5 := SyntaxIndexLiftOrder.successor_injective hZ w p (xs 5) (ys 5) hw (hxN 5) (field6 k w p xs hx) (field6 l w p ys hy)
  have hs0 := add_inputs w (ys 3) (ys 4) (xs 3) (ys 4) (ys 5) (eq_symm e3) (.eqRefl _) (field5 l w p ys hy)
  have hs := NaturalAdditionSyntax.output_subst w (xs 3) (ys 4) (ys 5) (xs 5) (eq_symm e5) hs0
  have e4 := NaturalDifference.unique hZ w (xs 3) (xs 5) (xs 4) (ys 4) hw (hxN 3) (hxN 4) (hyN 4) (field5 k w p xs hx) hs
  have hm0 := mul_inputs w (ys 0) (ys 1) (xs 0) (ys 1) (ys 4) (eq_symm e0) (.eqRefl _) (field4 l w p ys hy)
  have hm := NaturalMultiplicationSyntax.output_subst w (xs 0) (ys 1) (ys 4) (xs 4) (eq_symm e4) hm0
  exact NaturalMultiplicationOrderLaws.left_cancel hZ w (xs 1) (ys 1) (xs 0) (xs 4) hw (hxN 1) (hyN 1) (hxN 0)
    (base_nonempty (xs 0) (field0 k w p xs hx)) (field4 k w p xs hx) hm

end PPAC.Migration.Internal.FixedAxiomPacketFacts
