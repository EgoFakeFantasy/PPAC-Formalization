import PPAC.Migration.Internal.GodelUnpairArithmetic

/-! 固定原配数枚举的四种后继转移；每次转移返回实际原关系证书。 -/
namespace PPAC.Migration.Internal.GodelUnpairTransitions
open Source SourceAlgebra SourceLogic OmegaSyntax ZFArithmetic GodelPairSyntax GodelUnpairArithmetic
open NaturalAdditionSyntax (sum sum_rename)
open NaturalMultiplicationSyntax (product product_rename)
open NaturalAdditionBounds (below below_rename)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem zero_code {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) : Derives Γ (code w z z z) := by
  have hzW := OmegaStructureAlgebra.zero_member w z (ZFContext.arithmetic hZ).base.extensionality hw hz
  have hq := mul_zero hZ w z z z hw hzW hz hz
  have hs := add_zero hZ w z z hw hzW hz
  exact .disjR (.conjI (NaturalOrderBasic.nonself hZ z) (intro_upper w z z z z z hq hs hs))

theorem lower_inner {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b t p r : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w))
    (ht : Derives Γ (successor t a)) (htb : Derives Γ (.mem t b))
    (hp : Derives Γ (lower w a b p)) (hr : Derives Γ (successor r p)) : Derives Γ (code w t b r) := by
  let L := lowerWitness w a b p
  let Δ := Context.add L (Context.image Formula.raise Γ)
  apply eliminate_lower w a b p _ hp
  have hZ1 : ZFContext.Evidence Δ := ZFContext.under hZ L
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw L
  have ht1 : Derives Δ (successor t.castSucc a.castSucc) := by simpa only [Formula.raise, successor_rename] using under ht L
  have hr1 : Derives Δ (successor r.castSucc p.castSucc) := by simpa only [Formula.raise, successor_rename] using under hr L
  have hL : Derives Δ L := .hyp (Or.inl rfl)
  have hqW := mul_range hZ1 _ _ _ _ hw1 (.conjL hL)
  have hs := add_succ_backward hZ1 _ _ _ _ _ _ hw1 hqW (under ha L) ht1 (.conjR hL) hr1
  have hout : Derives Δ (code w.castSucc t.castSucc b.castSucc r.castSucc) := .disjL (.conjI (under htb L) (intro_lower _ _ _ _ _ (.conjL hL) hs))
  simpa only [Formula.raise, code_rename] using hout

theorem lower_turn {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b z p r : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hz : Derives Γ (empty z))
    (hb : Derives Γ (successor b a)) (hp : Derives Γ (lower w a b p)) (hr : Derives Γ (successor r p)) :
    Derives Γ (code w b z r) := by
  let L := lowerWitness w a b p
  let Δ := Context.add L (Context.image Formula.raise Γ)
  apply eliminate_lower w a b p _ hp
  have hZ1 : ZFContext.Evidence Δ := ZFContext.under hZ L
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw L
  have hb1 : Derives Δ (successor b.castSucc a.castSucc) := by simpa only [Formula.raise, successor_rename] using under hb L
  have hr1 : Derives Δ (successor r.castSucc p.castSucc) := by simpa only [Formula.raise, successor_rename] using under hr L
  have hz1 : Derives Δ (empty z.castSucc) := by simpa only [Formula.raise, empty_rename] using under hz L
  have hL : Derives Δ L := .hyp (Or.inl rfl)
  have hqW := mul_range hZ1 _ _ _ _ hw1 (.conjL hL)
  have hs := add_succ_backward hZ1 _ _ _ _ _ _ hw1 hqW (under ha L) hb1 (.conjR hL) hr1
  have hrW := add_range hZ1 _ _ _ _ hw1 hqW hs
  have hzSum := add_zero hZ1 _ _ _ hw1 hrW hz1
  have hout : Derives Δ (code w.castSucc b.castSucc z.castSucc r.castSucc) :=
    .disjR (.conjI (empty_at z.castSucc b.castSucc hz1) (intro_upper _ _ _ _ _ _ (.conjL hL) hs hzSum))
  simpa only [Formula.raise, code_rename] using hout

theorem upper_inner {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b t p r : Fin m)
    (hw : Derives Γ (omega w)) (hb : Derives Γ (.mem b w))
    (ht : Derives Γ (successor t b)) (hta : Derives Γ (below t a))
    (hp : Derives Γ (upper w a b p)) (hr : Derives Γ (successor r p)) : Derives Γ (code w a t r) := by
  let U := upperWitness w a b p
  let Δ := Context.add U (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_upper w a b p _ hp
  have hZ2 : ZFContext.Evidence Δ := ZFContext.under_two hZ U
  have lift {f : Formula m} (h : Derives Γ f) : Derives Δ f.raise.raise := OrderedPairElimination.under_two h U
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using lift hw
  have ht2 : Derives Δ (successor t.castSucc.castSucc b.castSucc.castSucc) := by simpa only [Formula.raise, successor_rename] using lift ht
  have hr2 : Derives Δ (successor r.castSucc.castSucc p.castSucc.castSucc) := by simpa only [Formula.raise, successor_rename] using lift hr
  have hta2 : Derives Δ (below t.castSucc.castSucc a.castSucc.castSucc) := by simpa only [Formula.raise, below_rename] using lift hta
  have hU : Derives Δ U := .hyp (Or.inl rfl)
  have hqW := mul_range hZ2 _ _ _ _ hw2 (.conjL hU)
  have huW := add_range hZ2 _ _ _ _ hw2 hqW (.conjL (.conjR hU))
  have hs := add_succ_backward hZ2 _ _ _ _ _ _ hw2 huW (lift hb) ht2 (.conjR (.conjR hU)) hr2
  have htW := OmegaStructureAlgebra.successor_member _ _ _ (ZFContext.arithmetic hZ2).base.extensionality hw2 (lift hb) ht2
  have hn := not_reverse hZ2 _ _ _ hw2 htW hta2
  have hout : Derives Δ (code w.castSucc.castSucc a.castSucc.castSucc t.castSucc.castSucc r.castSucc.castSucc) :=
    .disjR (.conjI hn (intro_upper _ _ _ _ _ _ (.conjL hU) (.conjL (.conjR hU)) hs))
  simpa only [Formula.raise, code_rename] using hout

theorem upper_turn {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a z s p r : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hz : Derives Γ (empty z))
    (hs : Derives Γ (successor s a)) (hp : Derives Γ (upper w a a p)) (hr : Derives Γ (successor r p)) :
    Derives Γ (code w z s r) := by
  let U := upperWitness w a a p
  let Δ := Context.add U (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_upper w a a p _ hp
  have hZ2 : ZFContext.Evidence Δ := ZFContext.under_two hZ U
  have lift {f : Formula m} (h : Derives Γ f) : Derives Δ f.raise.raise := OrderedPairElimination.under_two h U
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using lift hw
  have hs2 : Derives Δ (successor s.castSucc.castSucc a.castSucc.castSucc) := by simpa only [Formula.raise, successor_rename] using lift hs
  have hr2 : Derives Δ (successor r.castSucc.castSucc p.castSucc.castSucc) := by simpa only [Formula.raise, successor_rename] using lift hr
  have hz2 : Derives Δ (empty z.castSucc.castSucc) := by simpa only [Formula.raise, empty_rename] using lift hz
  have hU : Derives Δ U := .hyp (Or.inl rfl)
  have hsq := square_advance hZ2 _ _ _ _ _ _ _ hw2 (lift ha) hs2 (.conjL hU) (.conjL (.conjR hU)) (.conjR (.conjR hU)) hr2
  have hrW := mul_range hZ2 _ _ _ _ hw2 hsq
  have hzSum := add_zero hZ2 _ _ _ hw2 hrW hz2
  have hza := zero_below hZ2 _ _ _ hw2 hz2 (lift ha)
  have hzs := NaturalOrderBasic.below_successor _ _ _ hs2 hza
  have hout : Derives Δ (code w.castSucc.castSucc z.castSucc.castSucc s.castSucc.castSucc r.castSucc.castSucc) :=
    .disjL (.conjI hzs (intro_lower _ _ _ _ _ hsq hzSum))
  simpa only [Formula.raise, code_rename] using hout
end PPAC.Migration.Internal.GodelUnpairTransitions
