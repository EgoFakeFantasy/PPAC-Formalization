import PPAC.Migration.Internal.GodelPairBranchExistence

/-! 真实分支见证的ω闭包与输出唯一性，逐次使用平方/和的原核唯一性。 -/
namespace PPAC.Migration.Internal.GodelPairPolynomial
open Source SourceAlgebra SourceLogic OmegaSyntax ZFArithmetic GodelPairSyntax
open NaturalAdditionSyntax (sum sum_rename)
open NaturalMultiplicationSyntax (product product_rename)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem lower_range {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b p : Fin m)
    (hw : Derives Γ (omega w)) (hp : Derives Γ (lower w a b p)) : Derives Γ (.mem p w) := by
  let L := lowerWitness w a b p
  let Ξ := Context.add L (Context.image Formula.raise Γ)
  apply eliminate_lower w a b p _ hp
  have hZ1 : ZFContext.Evidence Ξ := ZFContext.under hZ L
  have hw1 : Derives Ξ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw L
  have hL : Derives Ξ L := .hyp (Or.inl rfl)
  have hqW := mul_range hZ1 _ _ _ _ hw1 (.conjL hL)
  exact add_range hZ1 _ _ _ _ hw1 hqW (.conjR hL)

theorem upper_range {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b p : Fin m)
    (hw : Derives Γ (omega w)) (hp : Derives Γ (upper w a b p)) : Derives Γ (.mem p w) := by
  let U := upperWitness w a b p
  let Δ := Context.add U (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_upper w a b p _ hp
  have hZ2 : ZFContext.Evidence Δ := ZFContext.under_two hZ U
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using OrderedPairElimination.under_two hw U
  have hU : Derives Δ U := .hyp (Or.inl rfl)
  have hqW := mul_range hZ2 _ _ _ _ hw2 (.conjL hU)
  have htW := add_range hZ2 _ _ _ _ hw2 hqW (.conjL (.conjR hU))
  exact add_range hZ2 _ _ _ _ hw2 htW (.conjR (.conjR hU))

theorem lower_value_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b p r q t : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w))
    (hq : Derives Γ (product w b b q)) (ht : Derives Γ (product w b b t))
    (hp : Derives Γ (sum w q a p)) (hr : Derives Γ (sum w t a r)) : Derives Γ (.equal p r) := by
  have heq := mul_unique hZ _ _ _ _ _ hw hb hb hq ht
  exact add_unique hZ w t a p r hw ha (NaturalAdditionTransport.left_subst w q t a p heq hp) hr

theorem upper_value_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b p r q t u v : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w))
    (hq : Derives Γ (product w a a q)) (hu : Derives Γ (product w a a u))
    (ht : Derives Γ (sum w q a t)) (hv : Derives Γ (sum w u a v))
    (hp : Derives Γ (sum w t b p)) (hr : Derives Γ (sum w v b r)) : Derives Γ (.equal p r) := by
  have heq := mul_unique hZ _ _ _ _ _ hw ha ha hq hu
  have het := add_unique hZ w u a t v hw ha (NaturalAdditionTransport.left_subst w q u a t heq ht) hv
  exact add_unique hZ w v b p r hw hb (NaturalAdditionTransport.left_subst w t v b p het hp) hr

theorem lower_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b p r : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w))
    (hp : Derives Γ (lower w a b p)) (hr : Derives Γ (lower w a b r)) : Derives Γ (.equal p r) := by
  let L := lowerWitness w a b p
  let Ξ := Context.add L (Context.image Formula.raise Γ)
  apply eliminate_lower w a b p _ hp
  have hr1 : Derives Ξ (lower w.castSucc a.castSucc b.castSucc r.castSucc) := by simpa only [Formula.raise, lower_rename] using under hr L
  let R := lowerWitness w.castSucc a.castSucc b.castSucc r.castSucc
  let Δ := Context.add R (Context.image Formula.raise Ξ)
  apply eliminate_lower w.castSucc a.castSucc b.castSucc r.castSucc _ hr1
  have hZ2 : ZFContext.Evidence Δ := ZFContext.under (ZFContext.under hZ L) R
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using under (under hw L) R
  have hL : Derives Ξ L := .hyp (Or.inl rfl)
  have hL2 : Derives Δ ((product w.castSucc.castSucc b.castSucc.castSucc b.castSucc.castSucc (Fin.last m).castSucc).conj
      (sum w.castSucc.castSucc (Fin.last m).castSucc a.castSucc.castSucc p.castSucc.castSucc)) := by
    simpa only [L, lowerWitness, Formula.raise, Formula.rename, product_rename, sum_rename] using under hL R
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  exact lower_value_unique hZ2 _ _ _ _ _ _ _ hw2 (under (under ha L) R) (under (under hb L) R) (.conjL hL2) (.conjL hR) (.conjR hL2) (.conjR hR)

theorem upper_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b p r : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w))
    (hp : Derives Γ (upper w a b p)) (hr : Derives Γ (upper w a b r)) : Derives Γ (.equal p r) := by
  let U := upperWitness w a b p
  let Ξ := Context.add U (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_upper w a b p _ hp
  have hr2 : Derives Ξ (upper w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc r.castSucc.castSucc) := by
    simpa only [Formula.raise, upper_rename] using OrderedPairElimination.under_two hr U
  let V := upperWitness w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc r.castSucc.castSucc
  let Δ := Context.add V (Context.image Formula.raise (Context.image Formula.raise Ξ))
  apply eliminate_upper w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc r.castSucc.castSucc _ hr2
  have lift {f : Formula m} (h : Derives Γ f) : Derives Δ f.raise.raise.raise.raise :=
    OrderedPairElimination.under_two (OrderedPairElimination.under_two h U) V
  have hZ4 : ZFContext.Evidence Δ := ZFContext.under_two (ZFContext.under_two hZ U) V
  have hw4 : Derives Δ (omega w.castSucc.castSucc.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using lift hw
  let q1 : Fin (m+4) := (Fin.last m).castSucc.castSucc.castSucc
  let t1 : Fin (m+4) := (Fin.last (m+1)).castSucc.castSucc
  have hU : Derives Ξ U := .hyp (Or.inl rfl)
  have hU4 : Derives Δ ((product w.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc q1).conj
      ((sum w.castSucc.castSucc.castSucc.castSucc q1 a.castSucc.castSucc.castSucc.castSucc t1).conj
        (sum w.castSucc.castSucc.castSucc.castSucc t1 b.castSucc.castSucc.castSucc.castSucc p.castSucc.castSucc.castSucc.castSucc))) := by
    simpa only [U, upperWitness, Formula.raise, Formula.rename, product_rename, sum_rename] using OrderedPairElimination.under_two hU V
  have hV : Derives Δ V := .hyp (Or.inl rfl)
  exact upper_value_unique hZ4 _ _ _ _ _ _ _ _ _ hw4 (lift ha) (lift hb) (.conjL hU4) (.conjL hV)
    (.conjL (.conjR hU4)) (.conjL (.conjR hV)) (.conjR (.conjR hU4)) (.conjR (.conjR hV))
end PPAC.Migration.Internal.GodelPairPolynomial
