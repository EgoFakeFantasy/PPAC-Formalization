import PPAC.Migration.Internal.NaturalMultiplicationDistributiveStep

/-! 对象ω归纳取得a*(b+n)=a*b+a*n，并以实际乘积唯一性证明双向等价。 -/
namespace PPAC.Migration.Internal.NaturalMultiplicationDistributive
open Source SourceAlgebra SourceLogic OmegaSyntax ReplacementPredicates NaturalAdditionSyntax ZFArithmetic
open NaturalAdditionTransport (params4 params4_0 params4_1 params4_2 params4_3)
open NaturalMultiplicationSyntax (product product_rename)
open NaturalMultiplicationDistributiveSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem zero_property {m} {Γ : Context m} (w a b p n : Fin m) (hp : Derives Γ (product w a b p))
    (hn : Derives Γ (empty n)) : Derives Γ (property w a b p n) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  let Δ := Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ))
  have lift {f : Formula m} (h : Derives Γ f) : Derives Δ f.raise.raise.raise := OrdinalRestriction.raise_three h
  have hp' : Derives Δ (product w.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc p.castSucc.castSucc.castSucc) := by simpa only [Formula.raise, product_rename] using lift hp
  have hn' : Derives Δ (empty n.castSucc.castSucc.castSucc) := by simpa only [Formula.raise, empty_rename] using lift hn
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact NaturalMultiplicationDistributiveStep.zero_point _ _ _ _ _ _ _ _ (add (add (add hp' _) _) _) (add (add (add hn' _) _) _)
    (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem step_property {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b p n s : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w)) (hn : Derives Γ (.mem n w))
    (hp : Derives Γ (product w a b p)) (hi : Derives Γ (property w a b p n)) (hs : Derives Γ (successor s n)) :
    Derives Γ (property w a b p s) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  let Δ := Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ))
  have lift {f : Formula m} (h : Derives Γ f) : Derives Δ f.raise.raise.raise := OrdinalRestriction.raise_three h
  have hZ' := ZFContext.rename (ZFContext.rename (ZFContext.rename hZ Fin.castSucc) Fin.castSucc) Fin.castSucc
  have hw' : Derives Δ (omega w.castSucc.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using lift hw
  have hp' : Derives Δ (product w.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc p.castSucc.castSucc.castSucc) := by simpa only [Formula.raise, product_rename] using lift hp
  have hi' : Derives Δ (property w.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc p.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc) := by simpa only [Formula.raise, property_rename] using lift hi
  have hs' : Derives Δ (successor s.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc) := by simpa only [Formula.raise, successor_rename] using lift hs
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact NaturalMultiplicationDistributiveStep.step_point (ZFContext.add (ZFContext.add (ZFContext.add hZ' _) _) _) _ _ _ _ _ _ _ _ _
    (add (add (add hw' _) _) _) (add (add (add (lift ha) _) _) _) (add (add (add (lift hb) _) _) _) (add (add (add (lift hn) _) _) _)
    (add (add (add hp' _) _) _) (add (add (add hi' _) _) _) (add (add (add hs' _) _) _)
    (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem base {m} {Γ : Context m} (w a b p : Fin m) (hp : Derives Γ (product w a b p)) :
    Derives Γ (OmegaInductionSyntax.base NaturalMultiplicationDistributiveSyntax.matrix (params4 w a b p)) := by
  simp only [OmegaInductionSyntax.base, NaturalMultiplicationDistributiveSyntax.matrix_pred, paramsUp, params4_0, params4_1, params4_2, params4_3]
  apply Derives.allI
  have hp' : Derives (Context.image Formula.raise Γ) (product w.castSucc a.castSucc b.castSucc p.castSucc) := by simpa only [Formula.raise, product_rename] using Derives.rename Fin.castSucc hp
  apply Derives.impI
  exact zero_property _ _ _ _ _ (add hp' _) (.hyp (Or.inl rfl))

theorem step {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b p : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w)) (hp : Derives Γ (product w a b p)) :
    Derives Γ (OmegaInductionSyntax.step NaturalMultiplicationDistributiveSyntax.matrix (params4 w a b p) w) := by
  simp only [OmegaInductionSyntax.step, NaturalMultiplicationDistributiveSyntax.matrix_pred, paramsUp, params4_0, params4_1, params4_2, params4_3]
  apply Derives.allI
  apply Derives.allI
  let Δ := Context.image Formula.raise (Context.image Formula.raise Γ)
  have lift {f : Formula m} (h : Derives Γ f) : Derives Δ f.raise.raise := Derives.rename Fin.castSucc (Derives.rename Fin.castSucc h)
  have hZ' := ZFContext.rename (ZFContext.rename hZ Fin.castSucc) Fin.castSucc
  have hw' : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using lift hw
  have hp' : Derives Δ (product w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc p.castSucc.castSucc) := by simpa only [Formula.raise, product_rename] using lift hp
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact step_property (ZFContext.add (ZFContext.add (ZFContext.add hZ' _) _) _) _ _ _ _ _ _
    (add (add (add hw' _) _) _) (add (add (add (lift ha) _) _) _) (add (add (add (lift hb) _) _) _) (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (add (add (add hp' _) _) _) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem all_distributive {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b p : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w)) (hp : Derives Γ (product w a b p)) :
    Derives Γ (.all ((Formula.mem (Fin.last m) w.castSucc).imp (property w.castSucc a.castSucc b.castSucc p.castSucc (Fin.last m)))) := by
  have hi := ZFArithmetic.induction hZ NaturalMultiplicationDistributiveSyntax.matrix (params4 w a b p) w hw (base w a b p hp) (step hZ w a b p hw ha hb hp)
  simpa only [OmegaInductionSyntax.holds, NaturalMultiplicationDistributiveSyntax.matrix_pred, paramsUp, params4_0, params4_1, params4_2, params4_3] using hi

theorem distribute {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b p n d q r : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w)) (hn : Derives Γ (.mem n w))
    (hp : Derives Γ (product w a b p)) (hd : Derives Γ (sum w b n d)) (hq : Derives Γ (product w a n q))
    (hr : Derives Γ (sum w p q r)) : Derives Γ (product w a d r) := by
  have hi := Derives.allE n (all_distributive hZ w a b p hw ha hb hp)
  have hi' : Derives Γ ((Formula.mem n w).imp (property w a b p n)) := by
    simpa only [Formula.instantiate, Formula.rename, property_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi
  exact property_at w a b p n d q r (.impE hi' hn) hd hq hr

theorem distribute_backward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b p n d q r : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w)) (hn : Derives Γ (.mem n w))
    (hp : Derives Γ (product w a b p)) (hd : Derives Γ (sum w b n d)) (hq : Derives Γ (product w a n q))
    (hr : Derives Γ (product w a d r)) : Derives Γ (sum w p q r) := by
  have hpW := mul_range hZ _ _ _ _ hw hp
  have hqW := mul_range hZ _ _ _ _ hw hq
  have ht := add_exists hZ w p q hw hpW hqW
  let T := (Formula.mem (Fin.last m) w.castSucc).conj (sum w.castSucc p.castSucc q.castSucc (Fin.last m))
  let Ξ := Context.add T (Context.image Formula.raise Γ)
  change Derives Γ (.ex T) at ht
  apply Derives.exE (p := T) ht
  have hZT : ZFContext.Evidence Ξ := ZFContext.under hZ T
  have hwT : Derives Ξ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw T
  have hpT : Derives Ξ (product w.castSucc a.castSucc b.castSucc p.castSucc) := by simpa only [Formula.raise, product_rename] using under hp T
  have hdT : Derives Ξ (sum w.castSucc b.castSucc n.castSucc d.castSucc) := by simpa only [Formula.raise, sum_rename] using under hd T
  have hqT : Derives Ξ (product w.castSucc a.castSucc n.castSucc q.castSucc) := by simpa only [Formula.raise, product_rename] using under hq T
  have hrT : Derives Ξ (product w.castSucc a.castSucc d.castSucc r.castSucc) := by simpa only [Formula.raise, product_rename] using under hr T
  have hT : Derives Ξ T := .hyp (Or.inl rfl)
  have hm := distribute hZT _ _ _ _ _ _ _ _ hwT (under ha T) (under hb T) (under hn T) hpT hdT hqT (.conjR hT)
  have hdW := add_range hZT _ _ _ _ hwT (under hb T) hdT
  have heq := mul_unique hZT _ _ _ _ _ hwT (under ha T) hdW hm hrT
  simpa only [Formula.raise, sum_rename] using NaturalAdditionSyntax.output_subst _ _ _ _ _ heq (.conjR hT)

theorem distributive_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b p n d q r : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w)) (hn : Derives Γ (.mem n w))
    (hp : Derives Γ (product w a b p)) (hd : Derives Γ (sum w b n d)) (hq : Derives Γ (product w a n q)) :
    Derives Γ ((product w a d r).iff (sum w p q r)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact distribute_backward (ZFContext.add hZ _) _ _ _ _ _ _ _ _ (add hw _) (add ha _) (add hb _) (add hn _) (add hp _) (add hd _) (add hq _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact distribute (ZFContext.add hZ _) _ _ _ _ _ _ _ _ (add hw _) (add ha _) (add hb _) (add hn _) (add hp _) (add hd _) (add hq _) (.hyp (Or.inl rfl))
end PPAC.Migration.Internal.NaturalMultiplicationDistributive
