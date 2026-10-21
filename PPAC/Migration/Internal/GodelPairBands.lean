import PPAC.Migration.Internal.GodelPairBandSyntax

/-! 两支的实际多项式见证产生相应平方区间；不引入额外区间公理。 -/
namespace PPAC.Migration.Internal.GodelPairBands
open Source SourceAlgebra SourceLogic OmegaSyntax ZFArithmetic GodelPairSyntax GodelPairBandSyntax GodelPairArithmetic
open NaturalAdditionSyntax (sum sum_rename)
open NaturalMultiplicationSyntax (product product_rename)
open NaturalAdditionBounds (below below_rename)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem lower_polynomial {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b p q : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w))
    (hq : Derives Γ (product w b b q)) (hp : Derives Γ (sum w q a p)) (hab : Derives Γ (.mem a b)) : Derives Γ (band w b p) := by
  have hqW := mul_range hZ _ _ _ _ hw hq
  have hqp := sum_left_bound hZ _ _ _ _ hw hqW ha hp
  apply Derives.conjI
  · apply Derives.allI
    apply Derives.impI
    let Q := product w.castSucc b.castSucc b.castSucc (Fin.last m)
    let Δ := Context.add Q (Context.image Formula.raise Γ)
    have hZ1 : ZFContext.Evidence Δ := ZFContext.under hZ Q
    have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw Q
    have hq1 : Derives Δ (product w.castSucc b.castSucc b.castSucc q.castSucc) := by simpa only [Formula.raise, product_rename] using under hq Q
    have he := mul_unique hZ1 _ _ _ _ _ hw1 (under hb Q) (under hb Q) hq1 (.hyp (Or.inl rfl))
    have hlo : Derives Δ (below q.castSucc p.castSucc) := by simpa only [Formula.raise, below_rename] using under hqp Q
    exact NaturalOrderBasic.below_subst_left _ _ _ he hlo
  · apply Derives.allI
    apply Derives.allI
    apply Derives.impI
    apply Derives.impI
    let S := successor (Fin.last m).castSucc b.castSucc.castSucc
    let V := product w.castSucc.castSucc (Fin.last m).castSucc (Fin.last m).castSucc (Fin.last (m+1))
    let Δ := Context.add V (Context.add S (Context.image Formula.raise (Context.image Formula.raise Γ)))
    have lift {f : Formula m} (h : Derives Γ f) : Derives Δ f.raise.raise := add (add (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc h)) S) V
    have hZ2 : ZFContext.Evidence Δ := ZFContext.add (ZFContext.add (ZFContext.rename (ZFContext.rename hZ Fin.castSucc) Fin.castSucc) S) V
    have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using lift hw
    have hq2 : Derives Δ (product w.castSucc.castSucc b.castSucc.castSucc b.castSucc.castSucc q.castSucc.castSucc) := by simpa only [Formula.raise, product_rename] using lift hq
    have hp2 : Derives Δ (sum w.castSucc.castSucc q.castSucc.castSucc a.castSucc.castSucc p.castSucc.castSucc) := by simpa only [Formula.raise, sum_rename] using lift hp
    exact GodelPairIntervals.lower_ceiling hZ2 _ _ _ _ _ _ _ hw2 (lift ha) (lift hb) hq2 hp2 (lift hab) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem upper_polynomial {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b p q t : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w))
    (hq : Derives Γ (product w a a q)) (ht : Derives Γ (sum w q a t)) (hp : Derives Γ (sum w t b p)) (hab : Derives Γ (Formula.mem a b).neg) : Derives Γ (band w a p) := by
  have hqW := mul_range hZ _ _ _ _ hw hq
  have htW := add_range hZ _ _ _ _ hw hqW ht
  have hpW := add_range hZ _ _ _ _ hw htW hp
  have hqt := sum_left_bound hZ _ _ _ _ hw hqW ha ht
  have htp := sum_left_bound hZ _ _ _ _ hw htW hb hp
  have hqp := NaturalOrderBasic.transitive hZ _ _ _ _ hw hpW hqt htp
  apply Derives.conjI
  · apply Derives.allI
    apply Derives.impI
    let Q := product w.castSucc a.castSucc a.castSucc (Fin.last m)
    let Δ := Context.add Q (Context.image Formula.raise Γ)
    have hZ1 : ZFContext.Evidence Δ := ZFContext.under hZ Q
    have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw Q
    have hq1 : Derives Δ (product w.castSucc a.castSucc a.castSucc q.castSucc) := by simpa only [Formula.raise, product_rename] using under hq Q
    have he := mul_unique hZ1 _ _ _ _ _ hw1 (under ha Q) (under ha Q) hq1 (.hyp (Or.inl rfl))
    have hlo : Derives Δ (below q.castSucc p.castSucc) := by simpa only [Formula.raise, below_rename] using under hqp Q
    exact NaturalOrderBasic.below_subst_left _ _ _ he hlo
  · apply Derives.allI
    apply Derives.allI
    apply Derives.impI
    apply Derives.impI
    let S := successor (Fin.last m).castSucc a.castSucc.castSucc
    let V := product w.castSucc.castSucc (Fin.last m).castSucc (Fin.last m).castSucc (Fin.last (m+1))
    let Δ := Context.add V (Context.add S (Context.image Formula.raise (Context.image Formula.raise Γ)))
    have lift {f : Formula m} (h : Derives Γ f) : Derives Δ f.raise.raise := add (add (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc h)) S) V
    have hZ2 : ZFContext.Evidence Δ := ZFContext.add (ZFContext.add (ZFContext.rename (ZFContext.rename hZ Fin.castSucc) Fin.castSucc) S) V
    have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using lift hw
    have hq2 : Derives Δ (product w.castSucc.castSucc a.castSucc.castSucc a.castSucc.castSucc q.castSucc.castSucc) := by simpa only [Formula.raise, product_rename] using lift hq
    have ht2 : Derives Δ (sum w.castSucc.castSucc q.castSucc.castSucc a.castSucc.castSucc t.castSucc.castSucc) := by simpa only [Formula.raise, sum_rename] using lift ht
    have hp2 : Derives Δ (sum w.castSucc.castSucc t.castSucc.castSucc b.castSucc.castSucc p.castSucc.castSucc) := by simpa only [Formula.raise, sum_rename] using lift hp
    have hba := GodelPairIntervals.reverse_below hZ _ _ _ hw ha hb hab
    have hba2 : Derives Δ (below b.castSucc.castSucc a.castSucc.castSucc) := by simpa only [Formula.raise, below_rename] using lift hba
    exact GodelPairIntervals.upper_ceiling hZ2 _ _ _ _ _ _ _ _ hw2 (lift ha) (lift hb) hq2 ht2 hp2 hba2 (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem lower_band {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b p : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w))
    (hab : Derives Γ (.mem a b)) (hp : Derives Γ (lower w a b p)) : Derives Γ (band w b p) := by
  let L := lowerWitness w a b p
  let Δ := Context.add L (Context.image Formula.raise Γ)
  apply eliminate_lower w a b p _ hp
  have hZ1 : ZFContext.Evidence Δ := ZFContext.under hZ L
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw L
  have hL : Derives Δ L := .hyp (Or.inl rfl)
  have hout := lower_polynomial hZ1 _ _ _ _ _ hw1 (under ha L) (under hb L) (.conjL hL) (.conjR hL) (under hab L)
  simpa only [Formula.raise, band_rename] using hout

theorem upper_band {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b p : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w))
    (hab : Derives Γ (Formula.mem a b).neg) (hp : Derives Γ (upper w a b p)) : Derives Γ (band w a p) := by
  let U := upperWitness w a b p
  let Δ := Context.add U (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_upper w a b p _ hp
  have hZ2 : ZFContext.Evidence Δ := ZFContext.under_two hZ U
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using OrderedPairElimination.under_two hw U
  have hU : Derives Δ U := .hyp (Or.inl rfl)
  have hout := upper_polynomial hZ2 _ _ _ _ _ _ hw2 (OrderedPairElimination.under_two ha U) (OrderedPairElimination.under_two hb U)
    (.conjL hU) (.conjL (.conjR hU)) (.conjR (.conjR hU)) (OrderedPairElimination.under_two hab U)
  simpa only [Formula.raise, band_rename] using hout
end PPAC.Migration.Internal.GodelPairBands
