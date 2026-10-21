import PPAC.Migration.Internal.NaturalMultiplicationAssociativeSyntax

/-! 两个实际旧积和已证分配律给出结合归纳步。 -/
namespace PPAC.Migration.Internal.NaturalMultiplicationAssociativeStep
open Source SourceAlgebra SourceLogic OmegaSyntax ZFArithmetic
open NaturalMultiplicationSyntax (product product_rename existsProduct existsProduct_rename)
open NaturalMultiplicationAssociativeSyntax (property property_at property_rename)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem zero_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b u n v r : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hn : Derives Γ (empty n))
    (hv : Derives Γ (product w b n v)) (hr : Derives Γ (product w u n r)) : Derives Γ (product w a v r) :=
  mul_zero hZ w a v r hw ha (NaturalMultiplicationLaws.zero_forward w b n v hn hv)
    (NaturalMultiplicationLaws.zero_forward w u n r hn hr)

theorem advance {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b u n s v0 r0 v r : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w)) (hn : Derives Γ (.mem n w))
    (hab : Derives Γ (product w a b u)) (hi : Derives Γ (property w a b u n)) (hs : Derives Γ (successor s n))
    (hv0 : Derives Γ (product w b n v0)) (hr0 : Derives Γ (product w u n r0))
    (hv : Derives Γ (product w b s v)) (hr : Derives Γ (product w u s r)) : Derives Γ (product w a v r) := by
  have huW := mul_range hZ _ _ _ _ hw hab
  have hv0W := mul_range hZ _ _ _ _ hw hv0
  have hvb := mul_succ_forward hZ _ _ _ _ _ _ hw hb hn hs hv0 hv
  have hru := mul_succ_forward hZ _ _ _ _ _ _ hw huW hn hs hr0 hr
  have hm0 := property_at w a b u n v0 r0 hi hv0 hr0
  exact NaturalMultiplicationDistributive.distribute hZ w a v0 r0 b v u r hw ha hv0W hb hm0 hvb hab hru

theorem step_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b u n s v r : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w)) (hn : Derives Γ (.mem n w))
    (hab : Derives Γ (product w a b u)) (hi : Derives Γ (property w a b u n)) (hs : Derives Γ (successor s n))
    (hv : Derives Γ (product w b s v)) (hr : Derives Γ (product w u s r)) : Derives Γ (product w a v r) := by
  have huW := mul_range hZ _ _ _ _ hw hab
  have hv0 := mul_exists hZ w b n hw hb hn
  have hr0 := mul_exists hZ w u n hw huW hn
  let V := (Formula.mem (Fin.last m) w.castSucc).conj (product w.castSucc b.castSucc n.castSucc (Fin.last m))
  let Ξ := Context.add V (Context.image Formula.raise Γ)
  change Derives Γ (.ex V) at hv0
  apply Derives.exE (p := V) hv0
  let R := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj (product w.castSucc.castSucc u.castSucc.castSucc n.castSucc.castSucc (Fin.last (m+1)))
  let Δ := Context.add R (Context.image Formula.raise Ξ)
  have hr0' : Derives Ξ (existsProduct w.castSucc u.castSucc n.castSucc) := by simpa only [Formula.raise, existsProduct_rename] using under hr0 V
  change Derives Ξ (.ex R) at hr0'
  apply Derives.exE (p := R) hr0'
  have lift {f : Formula m} (h : Derives Γ f) : Derives Δ f.raise.raise := under (under h V) R
  have hZ2 : ZFContext.Evidence Δ := ZFContext.under (ZFContext.under hZ V) R
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using lift hw
  have hab2 : Derives Δ (product w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc u.castSucc.castSucc) := by simpa only [Formula.raise, product_rename] using lift hab
  have hi2 : Derives Δ (property w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc u.castSucc.castSucc n.castSucc.castSucc) := by simpa only [Formula.raise, property_rename] using lift hi
  have hs2 : Derives Δ (successor s.castSucc.castSucc n.castSucc.castSucc) := by simpa only [Formula.raise, successor_rename] using lift hs
  have hv2 : Derives Δ (product w.castSucc.castSucc b.castSucc.castSucc s.castSucc.castSucc v.castSucc.castSucc) := by simpa only [Formula.raise, product_rename] using lift hv
  have hr2 : Derives Δ (product w.castSucc.castSucc u.castSucc.castSucc s.castSucc.castSucc r.castSucc.castSucc) := by simpa only [Formula.raise, product_rename] using lift hr
  have hV : Derives Δ V.raise := under (Derives.hyp (Γ := Ξ) (Or.inl rfl)) R
  have hvOld : Derives Δ (product w.castSucc.castSucc b.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc) := by
    simpa only [V, Formula.raise, Formula.rename, product_rename] using Derives.conjR hV
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  simpa only [Formula.raise, product_rename] using advance hZ2 _ _ _ _ _ _ _ _ _ _ hw2 (lift ha) (lift hb) (lift hn) hab2 hi2 hs2 hvOld (.conjR hR) hv2 hr2
end PPAC.Migration.Internal.NaturalMultiplicationAssociativeStep
