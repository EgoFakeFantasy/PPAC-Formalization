import PPAC.Migration.Internal.GodelPairBounds

/-! 原配数的平方区间界：低支落在[b²,(b+1)²)，高支落在[a²,(a+1)²)。 -/
namespace PPAC.Migration.Internal.GodelPairIntervals
open Source SourceAlgebra SourceLogic OmegaSyntax ZFArithmetic GodelPairArithmetic
open NaturalAdditionSyntax (sum sum_rename)
open NaturalMultiplicationSyntax (product product_rename)
open NaturalAdditionBounds (below below_rename)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem reverse_below {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w))
    (hn : Derives Γ (Formula.mem a b).neg) : Derives Γ (below b a) := by
  apply Derives.disjE (NaturalOrderBasic.compare hZ w a b hw ha hb)
  · exact .disjL (eq_symm (.hyp (Or.inl rfl)))
  · apply Derives.disjE (.hyp (Or.inl rfl))
    · exact .botE (.impE (add (add hn _) _) (.hyp (Or.inl rfl)))
    · exact .disjR (.hyp (Or.inl rfl))

theorem upper_ceiling {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b p q t s v : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w))
    (hq : Derives Γ (product w a a q)) (ht : Derives Γ (sum w q a t)) (hp : Derives Γ (sum w t b p))
    (hba : Derives Γ (below b a)) (hs : Derives Γ (successor s a)) (hv : Derives Γ (product w s s v)) :
    Derives Γ (.mem p v) := by
  have hqW := mul_range hZ _ _ _ _ hw hq
  have htW := add_range hZ _ _ _ _ hw hqW ht
  have hu := add_exists hZ w t a hw htW ha
  let U := (Formula.mem (Fin.last m) w.castSucc).conj (sum w.castSucc t.castSucc a.castSucc (Fin.last m))
  let Δ := Context.add U (Context.image Formula.raise Γ)
  change Derives Γ (.ex U) at hu
  apply Derives.exE (p := U) hu
  have hZ1 : ZFContext.Evidence Δ := ZFContext.under hZ U
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw U
  have hU : Derives Δ U := .hyp (Or.inl rfl)
  have hq1 : Derives Δ (product w.castSucc a.castSucc a.castSucc q.castSucc) := by simpa only [Formula.raise, product_rename] using under hq U
  have ht1 : Derives Δ (sum w.castSucc q.castSucc a.castSucc t.castSucc) := by simpa only [Formula.raise, sum_rename] using under ht U
  have hp1 : Derives Δ (sum w.castSucc t.castSucc b.castSucc p.castSucc) := by simpa only [Formula.raise, sum_rename] using under hp U
  have hs1 : Derives Δ (successor s.castSucc a.castSucc) := by simpa only [Formula.raise, successor_rename] using under hs U
  have hv1 : Derives Δ (product w.castSucc s.castSucc s.castSucc v.castSucc) := by simpa only [Formula.raise, product_rename] using under hv U
  have hba1 : Derives Δ (below b.castSucc a.castSucc) := by simpa only [Formula.raise, below_rename] using under hba U
  have hpu := Derives.impE (Derives.conjL (NaturalAdditionMonotone.left_weak_iff hZ1 _ _ _ _ _ _ hw1 (under hb U) (under ha U) (under htW U) hp1 (.conjR hU))) hba1
  have hstep := square_step hZ1 _ _ _ _ _ _ _ hw1 (under ha U) hs1 hq1 hv1 ht1 (.conjR hU)
  exact NaturalOrderBasic.below_successor _ _ _ hstep hpu

theorem lower_ceiling {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b p q s v : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w))
    (hq : Derives Γ (product w b b q)) (hp : Derives Γ (sum w q a p))
    (hab : Derives Γ (.mem a b)) (hs : Derives Γ (successor s b)) (hv : Derives Γ (product w s s v)) :
    Derives Γ (.mem p v) := by
  have hqW := mul_range hZ _ _ _ _ hw hq
  have ht := add_exists hZ w q b hw hqW hb
  let T := (Formula.mem (Fin.last m) w.castSucc).conj (sum w.castSucc q.castSucc b.castSucc (Fin.last m))
  let Ξ := Context.add T (Context.image Formula.raise Γ)
  change Derives Γ (.ex T) at ht
  apply Derives.exE (p := T) ht
  have hZ1 : ZFContext.Evidence Ξ := ZFContext.under hZ T
  have hw1 : Derives Ξ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw T
  have hT : Derives Ξ T := .hyp (Or.inl rfl)
  have hu := add_exists hZ1 w.castSucc (Fin.last m) b.castSucc hw1 (.conjL hT) (under hb T)
  let U := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj
    (sum w.castSucc.castSucc (Fin.last m).castSucc b.castSucc.castSucc (Fin.last (m+1)))
  let Δ := Context.add U (Context.image Formula.raise Ξ)
  change Derives Ξ (.ex U) at hu
  apply Derives.exE (p := U) hu
  have hZ2 : ZFContext.Evidence Δ := ZFContext.under hZ1 U
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw1 U
  have hT2 : Derives Δ ((Formula.mem (Fin.last m).castSucc w.castSucc.castSucc).conj
      (sum w.castSucc.castSucc q.castSucc.castSucc b.castSucc.castSucc (Fin.last m).castSucc)) := by
    simpa only [T, Formula.raise, Formula.rename, sum_rename] using under hT U
  have hU : Derives Δ U := .hyp (Or.inl rfl)
  have lift {f : Formula m} (h : Derives Γ f) : Derives Δ f.raise.raise := under (under h T) U
  have hq2 : Derives Δ (product w.castSucc.castSucc b.castSucc.castSucc b.castSucc.castSucc q.castSucc.castSucc) := by simpa only [Formula.raise, product_rename] using lift hq
  have hp2 : Derives Δ (sum w.castSucc.castSucc q.castSucc.castSucc a.castSucc.castSucc p.castSucc.castSucc) := by simpa only [Formula.raise, sum_rename] using lift hp
  have hs2 : Derives Δ (successor s.castSucc.castSucc b.castSucc.castSucc) := by simpa only [Formula.raise, successor_rename] using lift hs
  have hv2 : Derives Δ (product w.castSucc.castSucc s.castSucc.castSucc s.castSucc.castSucc v.castSucc.castSucc) := by simpa only [Formula.raise, product_rename] using lift hv
  have hpt := Derives.impE (Derives.conjL (NaturalAdditionMonotone.left_strict_iff hZ2 _ _ _ _ _ _ hw2 (lift ha) (lift hb) (lift hqW) hp2 (.conjR hT2))) (lift hab)
  have htu := sum_left_bound hZ2 _ _ _ _ hw2 (.conjL hT2) (lift hb) (.conjR hU)
  have hpu := NaturalOrderBasic.transitive hZ2 _ _ _ _ hw2 (.conjL hU) (.disjR hpt) htu
  have hstep := square_step hZ2 _ _ _ _ _ _ _ hw2 (lift hb) hs2 hq2 hv2 (.conjR hT2) (.conjR hU)
  exact NaturalOrderBasic.below_successor _ _ _ hstep hpu
end PPAC.Migration.Internal.GodelPairIntervals
