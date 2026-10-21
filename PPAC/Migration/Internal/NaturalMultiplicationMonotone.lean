import PPAC.Migration.Internal.NaturalMultiplicationPositive

/-! 乘法差值是实际差值乘公共乘数；弱单调允许零，严格单调要求非零公共乘数。 -/
namespace PPAC.Migration.Internal.NaturalMultiplicationMonotone
open Source SourceAlgebra SourceLogic OmegaSyntax ZFArithmetic
open NaturalAdditionSyntax (sum sum_rename)
open NaturalMultiplicationSyntax (product product_rename)
open NaturalAdditionBounds (below below_rename)
open NaturalDifferenceSyntax (witness positiveWitness)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem translate_difference {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b n d x y z : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hd : Derives Γ (.mem d w)) (hn : Derives Γ (.mem n w))
    (hs : Derives Γ (sum w a d b)) (hx : Derives Γ (product w a n x))
    (hy : Derives Γ (product w b n y)) (hz : Derives Γ (product w d n z)) : Derives Γ (sum w x z y) :=
  .impE (.conjL (NaturalMultiplicationAlgebraLaws.left_distributive_iff hZ w a d n b x z y hw ha hd hn hs hx hz)) hy

theorem monotone {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b n x y : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w)) (hn : Derives Γ (.mem n w))
    (hx : Derives Γ (product w a n x)) (hy : Derives Γ (product w b n y)) (hl : Derives Γ (below a b)) : Derives Γ (below x y) := by
  have hd := NaturalDifference.exists_of_below hZ w a b hw ha hb hl
  let D := witness w.castSucc a.castSucc b.castSucc (Fin.last m)
  let Ξ := Context.add D (Context.image Formula.raise Γ)
  change Derives Γ (.ex D) at hd
  apply Derives.exE (p := D) hd
  have hZ1 : ZFContext.Evidence Ξ := ZFContext.under hZ D
  have hw1 : Derives Ξ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw D
  have hD1 : Derives Ξ D := .hyp (Or.inl rfl)
  have hz := mul_exists hZ1 w.castSucc (Fin.last m) n.castSucc hw1 (.conjL hD1) (under hn D)
  let Z := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj
    (product w.castSucc.castSucc (Fin.last m).castSucc n.castSucc.castSucc (Fin.last (m+1)))
  let Δ := Context.add Z (Context.image Formula.raise Ξ)
  change Derives Ξ (.ex Z) at hz
  apply Derives.exE (p := Z) hz
  have hZ2 : ZFContext.Evidence Δ := ZFContext.under hZ1 Z
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw1 Z
  have hx2 : Derives Δ (product w.castSucc.castSucc a.castSucc.castSucc n.castSucc.castSucc x.castSucc.castSucc) := by simpa only [Formula.raise, product_rename] using under (under hx D) Z
  have hy2 : Derives Δ (product w.castSucc.castSucc b.castSucc.castSucc n.castSucc.castSucc y.castSucc.castSucc) := by simpa only [Formula.raise, product_rename] using under (under hy D) Z
  have hD2 : Derives Δ D.raise := under hD1 Z
  have hdSum : Derives Δ (sum w.castSucc.castSucc a.castSucc.castSucc (Fin.last m).castSucc b.castSucc.castSucc) := by
    simpa only [D, Formula.raise, Formula.rename, sum_rename] using Derives.conjR hD2
  have hZval : Derives Δ Z := .hyp (Or.inl rfl)
  have hsum := translate_difference hZ2 _ _ _ _ _ _ _ _ hw2 (under (under ha D) Z) (.conjL hD2) (under (under hn D) Z) hdSum hx2 hy2 (.conjR hZval)
  have hxW := mul_range hZ2 _ _ _ _ hw2 hx2
  have hlo := NaturalAdditionBounds.lower_bound (ZFContext.arithmetic hZ2) _ _ _ _ (ZFContext.recAdd hZ2)
    (ZFContext.separation hZ2 NaturalAdditionBounds.matrix) hw2 hxW (.conjL hZval) hsum
  simpa only [Formula.raise, below_rename] using hlo

theorem strict_monotone {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b n x y : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w)) (hn : Derives Γ (.mem n w))
    (hn0 : Derives Γ (empty n).neg) (hx : Derives Γ (product w a n x)) (hy : Derives Γ (product w b n y))
    (hl : Derives Γ (.mem a b)) : Derives Γ (.mem x y) := by
  have hd := NaturalDifferencePositive.positive_of_member hZ w a b hw ha hb hl
  let D := positiveWitness w.castSucc a.castSucc b.castSucc (Fin.last m)
  let Ξ := Context.add D (Context.image Formula.raise Γ)
  change Derives Γ (.ex D) at hd
  apply Derives.exE (p := D) hd
  have hZ1 : ZFContext.Evidence Ξ := ZFContext.under hZ D
  have hw1 : Derives Ξ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw D
  have hD1 : Derives Ξ D := .hyp (Or.inl rfl)
  have hz := mul_exists hZ1 w.castSucc (Fin.last m) n.castSucc hw1 (.conjL (.conjL hD1)) (under hn D)
  let Z := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj
    (product w.castSucc.castSucc (Fin.last m).castSucc n.castSucc.castSucc (Fin.last (m+1)))
  let Δ := Context.add Z (Context.image Formula.raise Ξ)
  change Derives Ξ (.ex Z) at hz
  apply Derives.exE (p := Z) hz
  have hZ2 : ZFContext.Evidence Δ := ZFContext.under hZ1 Z
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw1 Z
  have hx2 : Derives Δ (product w.castSucc.castSucc a.castSucc.castSucc n.castSucc.castSucc x.castSucc.castSucc) := by simpa only [Formula.raise, product_rename] using under (under hx D) Z
  have hy2 : Derives Δ (product w.castSucc.castSucc b.castSucc.castSucc n.castSucc.castSucc y.castSucc.castSucc) := by simpa only [Formula.raise, product_rename] using under (under hy D) Z
  have hn02 : Derives Δ (empty n.castSucc.castSucc).neg := by
    simpa only [Formula.raise, Formula.neg, Formula.rename, empty_rename] using under (under hn0 D) Z
  have hD2 : Derives Δ D.raise := under hD1 Z
  have hdSum : Derives Δ (sum w.castSucc.castSucc a.castSucc.castSucc (Fin.last m).castSucc b.castSucc.castSucc) := by
    simpa only [D, Formula.raise, Formula.rename, sum_rename] using Derives.conjR hD2
  have hd02 : Derives Δ (empty (Fin.last m).castSucc).neg := by
    simpa only [D, Formula.raise, Formula.rename, empty_rename] using Derives.conjR (Derives.conjL hD2)
  have hZval : Derives Δ Z := .hyp (Or.inl rfl)
  have hdW : Derives Δ (.mem (Fin.last m).castSucc w.castSucc.castSucc) := .conjL (.conjL hD2)
  have hnW : Derives Δ (.mem n.castSucc.castSucc w.castSucc.castSucc) := under (under hn D) Z
  have hz0 := NaturalMultiplicationPositive.nonzero hZ2 _ _ _ _ hw2 hdW hnW hd02 hn02 (.conjR hZval)
  have hsum := translate_difference hZ2 _ _ _ _ _ _ _ _ hw2 (under (under ha D) Z) hdW hnW hdSum hx2 hy2 (.conjR hZval)
  have hxW := mul_range hZ2 _ _ _ _ hw2 hx2
  exact NaturalDifferencePositive.sum_positive hZ2 _ _ _ _ hw2 hxW (.conjL hZval) hsum hz0
end PPAC.Migration.Internal.NaturalMultiplicationMonotone
