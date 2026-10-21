import PPAC.Migration.Internal.NaturalMultiplicationDistributiveSyntax

/-! 分配律后继步实际取得三个旧值，再由已证结合式连接新的乘法步。 -/
namespace PPAC.Migration.Internal.NaturalMultiplicationDistributiveStep
open Source SourceAlgebra SourceLogic GraphSyntax OmegaSyntax ReplacementPredicates NaturalAdditionSyntax ZFArithmetic
open NaturalMultiplicationSyntax (product product_rename existsProduct existsProduct_rename)
open NaturalMultiplicationDistributiveSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem zero_point {m} {Γ : Context m} (w a b p n d q r : Fin m) (hp : Derives Γ (product w a b p))
    (hn : Derives Γ (empty n)) (hd : Derives Γ (sum w b n d)) (hq : Derives Γ (product w a n q))
    (hr : Derives Γ (sum w p q r)) : Derives Γ (product w a d r) := by
  have hdb := NaturalRecursionLaws.evaluation_zero NaturalSuccessorStep.matrix (params w) w b n d hn hd
  have hq0 := NaturalMultiplicationLaws.zero_forward w a n q hn hq
  have hrp := NaturalRecursionLaws.evaluation_zero NaturalSuccessorStep.matrix (params w) w p q r hq0 hr
  exact NaturalMultiplicationSyntax.output_subst w a d p r (eq_symm hrp)
    (NaturalMultiplicationTransport.index_subst w a b d p (eq_symm hdb) hp)

theorem advance {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b p n s d0 q0 r0 d q r : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w)) (hn : Derives Γ (.mem n w))
    (hp : Derives Γ (product w a b p)) (hi : Derives Γ (property w a b p n)) (hs : Derives Γ (successor s n))
    (hd0 : Derives Γ (sum w b n d0)) (hq0 : Derives Γ (product w a n q0)) (hr0 : Derives Γ (sum w p q0 r0))
    (hd : Derives Γ (sum w b s d)) (hq : Derives Γ (product w a s q)) (hr : Derives Γ (sum w p q r)) : Derives Γ (product w a d r) := by
  have hpW := mul_range hZ _ _ _ _ hw hp
  have hq0W := mul_range hZ _ _ _ _ hw hq0
  have hd0W := add_range hZ _ _ _ _ hw hb hd0
  have hds := add_succ_forward hZ _ _ _ _ _ _ hw hb hn hs hd0 hd
  have hqa := mul_succ_forward hZ _ _ _ _ _ _ hw ha hn hs hq0 hq
  have hr0a := add_unassociate hZ w p q0 r0 a q r hw hpW hq0W ha hr0 hqa hr
  have hm0 := property_at w a b p n d0 q0 r0 hi hd0 hq0 hr0
  exact mul_succ_backward hZ w a d0 d r0 r hw ha hd0W hds hm0 hr0a

theorem step_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b p n s d q r : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w)) (hn : Derives Γ (.mem n w))
    (hp : Derives Γ (product w a b p)) (hi : Derives Γ (property w a b p n)) (hs : Derives Γ (successor s n))
    (hd : Derives Γ (sum w b s d)) (hq : Derives Γ (product w a s q)) (hr : Derives Γ (sum w p q r)) : Derives Γ (product w a d r) := by
  have hpW := mul_range hZ _ _ _ _ hw hp
  have hd0 := add_exists hZ w b n hw hb hn
  have hq0 := mul_exists hZ w a n hw ha hn
  let D := (Formula.mem (Fin.last m) w.castSucc).conj (sum w.castSucc b.castSucc n.castSucc (Fin.last m))
  let Ξ := Context.add D (Context.image Formula.raise Γ)
  change Derives Γ (.ex D) at hd0
  apply Derives.exE (p := D) hd0
  let Q := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj (product w.castSucc.castSucc a.castSucc.castSucc n.castSucc.castSucc (Fin.last (m+1)))
  let Ψ := Context.add Q (Context.image Formula.raise Ξ)
  have hq0' : Derives Ξ (existsProduct w.castSucc a.castSucc n.castSucc) := by
    simpa only [Formula.raise, existsProduct_rename] using under hq0 D
  change Derives Ξ (.ex Q) at hq0'
  apply Derives.exE (p := Q) hq0'
  have hZ2 : ZFContext.Evidence Ψ := ZFContext.under (ZFContext.under hZ D) Q
  have hw2 : Derives Ψ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using under (under hw D) Q
  have hpW2 : Derives Ψ (.mem p.castSucc.castSucc w.castSucc.castSucc) := under (under hpW D) Q
  have hQ2 : Derives Ψ Q := .hyp (Or.inl rfl)
  have hr0 := add_exists hZ2 w.castSucc.castSucc p.castSucc.castSucc (Fin.last (m+1)) hw2 hpW2 (.conjL hQ2)
  let R := (Formula.mem (Fin.last (m+2)) w.castSucc.castSucc.castSucc).conj
    (sum w.castSucc.castSucc.castSucc p.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2)))
  let Δ := Context.add R (Context.image Formula.raise Ψ)
  change Derives Ψ (.ex R) at hr0
  apply Derives.exE (p := R) hr0
  have lift {f : Formula m} (h : Derives Γ f) : Derives Δ f.raise.raise.raise := under (under (under h D) Q) R
  have hZ3 : ZFContext.Evidence Δ := ZFContext.under hZ2 R
  have hw3 : Derives Δ (omega w.castSucc.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using lift hw
  have hp3 : Derives Δ (product w.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc p.castSucc.castSucc.castSucc) := by simpa only [Formula.raise, product_rename] using lift hp
  have hi3 : Derives Δ (property w.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc p.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc) := by simpa only [Formula.raise, property_rename] using lift hi
  have hs3 : Derives Δ (successor s.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc) := by simpa only [Formula.raise, successor_rename] using lift hs
  have hd3 : Derives Δ (sum w.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc) := by simpa only [Formula.raise, sum_rename] using lift hd
  have hq3 : Derives Δ (product w.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc) := by simpa only [Formula.raise, product_rename] using lift hq
  have hr3 : Derives Δ (sum w.castSucc.castSucc.castSucc p.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc) := by simpa only [Formula.raise, sum_rename] using lift hr
  have hD : Derives Δ D.raise.raise := under (under (Derives.hyp (Γ := Ξ) (Or.inl rfl)) Q) R
  have hQ : Derives Δ Q.raise := under hQ2 R
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hdOld : Derives Δ (sum w.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc) := by
    simpa only [D, Formula.raise, Formula.rename, sum_rename] using Derives.conjR hD
  have hqOld : Derives Δ (product w.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc) := by
    simpa only [Q, Formula.raise, Formula.rename, product_rename] using Derives.conjR hQ
  simpa only [Formula.raise, product_rename] using advance hZ3 _ _ _ _ _ _ _ _ _ _ _ _ hw3 (lift ha) (lift hb) (lift hn)
    hp3 hi3 hs3 hdOld hqOld (.conjR hR) hd3 hq3 hr3
end PPAC.Migration.Internal.NaturalMultiplicationDistributiveStep
