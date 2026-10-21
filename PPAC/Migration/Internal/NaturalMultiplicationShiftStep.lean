import PPAC.Migration.Internal.NaturalMultiplicationShiftSyntax

/-! 左后继乘法步：实际旧积、旧和及重排后的中间和，不作宿主代数化简。 -/
namespace PPAC.Migration.Internal.NaturalMultiplicationShiftStep
open Source SourceAlgebra SourceLogic GraphSyntax OmegaSyntax NaturalAdditionSyntax ZFArithmetic
open NaturalMultiplicationSyntax (product product_rename existsProduct existsProduct_rename)
open NaturalMultiplicationShiftSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem zero_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b n p r : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (successor b a)) (hn : Derives Γ (empty n))
    (hp : Derives Γ (product w a n p)) (hr : Derives Γ (sum w p n r)) : Derives Γ (product w b n r) := by
  have hp0 := NaturalMultiplicationLaws.zero_forward w a n p hn hp
  have hrp := NaturalRecursionLaws.evaluation_zero NaturalSuccessorStep.matrix (params w) w p n r hn hr
  have hr0 := NaturalMultiplicationLaws.empty_subst p r (eq_symm hrp) hp0
  have hbW := OmegaStructureAlgebra.successor_member w b a (ZFContext.arithmetic hZ).base.extensionality hw ha hb
  exact mul_zero hZ w b n r hw hbW hn hr0

theorem advance {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b n s p0 r0 p r : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (successor b a)) (hn : Derives Γ (.mem n w))
    (hi : Derives Γ (property w a b n)) (hs : Derives Γ (successor s n))
    (hp0 : Derives Γ (product w a n p0)) (hr0 : Derives Γ (sum w p0 n r0))
    (hp : Derives Γ (product w a s p)) (hr : Derives Γ (sum w p s r)) : Derives Γ (product w b s r) := by
  have hp0W := mul_range hZ _ _ _ _ hw hp0
  have hr0W := add_range hZ _ _ _ _ hw hp0W hr0
  have hk := add_exists hZ w r0 a hw hr0W ha
  let K := (Formula.mem (Fin.last m) w.castSucc).conj (sum w.castSucc r0.castSucc a.castSucc (Fin.last m))
  let Ξ := Context.add K (Context.image Formula.raise Γ)
  change Derives Γ (.ex K) at hk
  apply Derives.exE (p := K) hk
  have hZK : ZFContext.Evidence Ξ := ZFContext.under hZ K
  have hwK : Derives Ξ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw K
  have hbK : Derives Ξ (successor b.castSucc a.castSucc) := by simpa only [Formula.raise, successor_rename] using under hb K
  have hiK : Derives Ξ (property w.castSucc a.castSucc b.castSucc n.castSucc) := by simpa only [Formula.raise, property_rename] using under hi K
  have hsK : Derives Ξ (successor s.castSucc n.castSucc) := by simpa only [Formula.raise, successor_rename] using under hs K
  have hp0K : Derives Ξ (product w.castSucc a.castSucc n.castSucc p0.castSucc) := by simpa only [Formula.raise, product_rename] using under hp0 K
  have hr0K : Derives Ξ (sum w.castSucc p0.castSucc n.castSucc r0.castSucc) := by simpa only [Formula.raise, sum_rename] using under hr0 K
  have hpK : Derives Ξ (product w.castSucc a.castSucc s.castSucc p.castSucc) := by simpa only [Formula.raise, product_rename] using under hp K
  have hrK : Derives Ξ (sum w.castSucc p.castSucc s.castSucc r.castSucc) := by simpa only [Formula.raise, sum_rename] using under hr K
  have hK : Derives Ξ K := .hyp (Or.inl rfl)
  have hpa := mul_succ_forward hZK _ _ _ _ _ _ hwK (under ha K) (under hn K) hsK hp0K hpK
  have hpn := NaturalAdditionReassociation.swap_middle hZK _ _ _ _ _ _ _ hwK (under hp0W K) (under hn K) (under ha K) hr0K hpa (.conjR hK)
  have hpW := mul_range hZK _ _ _ _ hwK hpK
  have hrS := add_succ_forward hZK _ _ _ _ _ _ hwK hpW (under hn K) hsK hpn hrK
  have hrb := add_succ_backward hZK _ _ _ _ _ _ hwK (under hr0W K) (under ha K) hbK (.conjR hK) hrS
  have hm0 := property_at _ _ _ _ _ _ hiK hp0K hr0K
  have hbW := OmegaStructureAlgebra.successor_member _ _ _ (ZFContext.arithmetic hZK).base.extensionality hwK (under ha K) hbK
  simpa only [Formula.raise, product_rename] using mul_succ_backward hZK _ _ _ _ _ _ hwK hbW (under hn K) hsK hm0 hrb

theorem step_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b n s p r : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (successor b a)) (hn : Derives Γ (.mem n w))
    (hi : Derives Γ (property w a b n)) (hs : Derives Γ (successor s n))
    (hp : Derives Γ (product w a s p)) (hr : Derives Γ (sum w p s r)) : Derives Γ (product w b s r) := by
  have hp0 := mul_exists hZ w a n hw ha hn
  let P := (Formula.mem (Fin.last m) w.castSucc).conj (product w.castSucc a.castSucc n.castSucc (Fin.last m))
  let Ξ := Context.add P (Context.image Formula.raise Γ)
  change Derives Γ (.ex P) at hp0
  apply Derives.exE (p := P) hp0
  have hZ1 : ZFContext.Evidence Ξ := ZFContext.under hZ P
  have hw1 : Derives Ξ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw P
  have hP1 : Derives Ξ P := .hyp (Or.inl rfl)
  have hr0 := add_exists hZ1 w.castSucc (Fin.last m) n.castSucc hw1 (.conjL hP1) (under hn P)
  let R := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj (sum w.castSucc.castSucc (Fin.last m).castSucc n.castSucc.castSucc (Fin.last (m+1)))
  let Δ := Context.add R (Context.image Formula.raise Ξ)
  change Derives Ξ (.ex R) at hr0
  apply Derives.exE (p := R) hr0
  have lift {f : Formula m} (h : Derives Γ f) : Derives Δ f.raise.raise := under (under h P) R
  have hZ2 : ZFContext.Evidence Δ := ZFContext.under hZ1 R
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using lift hw
  have hb2 : Derives Δ (successor b.castSucc.castSucc a.castSucc.castSucc) := by simpa only [Formula.raise, successor_rename] using lift hb
  have hi2 : Derives Δ (property w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc n.castSucc.castSucc) := by simpa only [Formula.raise, property_rename] using lift hi
  have hs2 : Derives Δ (successor s.castSucc.castSucc n.castSucc.castSucc) := by simpa only [Formula.raise, successor_rename] using lift hs
  have hp2 : Derives Δ (product w.castSucc.castSucc a.castSucc.castSucc s.castSucc.castSucc p.castSucc.castSucc) := by simpa only [Formula.raise, product_rename] using lift hp
  have hr2 : Derives Δ (sum w.castSucc.castSucc p.castSucc.castSucc s.castSucc.castSucc r.castSucc.castSucc) := by simpa only [Formula.raise, sum_rename] using lift hr
  have hP : Derives Δ P.raise := under hP1 R
  have hpOld : Derives Δ (product w.castSucc.castSucc a.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc) := by
    simpa only [P, Formula.raise, Formula.rename, product_rename] using Derives.conjR hP
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  simpa only [Formula.raise, product_rename] using advance hZ2 _ _ _ _ _ _ _ _ _ hw2 (lift ha) hb2 (lift hn) hi2 hs2 hpOld (.conjR hR) hp2 hr2
end PPAC.Migration.Internal.NaturalMultiplicationShiftStep
