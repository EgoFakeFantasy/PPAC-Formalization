import PPAC.Migration.Internal.NaturalMultiplicationTransport

/-! 实际和见证之间的三项和四项重排；对象量词保留全部中间数值。 -/
namespace PPAC.Migration.Internal.NaturalAdditionReassociation
open Source SourceAlgebra SourceLogic GraphSyntax OmegaSyntax NaturalAdditionSyntax ZFArithmetic
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem swap_middle {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b c u v r : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w)) (hc : Derives Γ (.mem c w))
    (hu : Derives Γ (sum w a b u)) (hv : Derives Γ (sum w a c v)) (hr : Derives Γ (sum w u c r)) : Derives Γ (sum w v b r) := by
  have ht := add_exists hZ w b c hw hb hc
  let T := (Formula.mem (Fin.last m) w.castSucc).conj (sum w.castSucc b.castSucc c.castSucc (Fin.last m))
  let Ξ := Context.add T (Context.image Formula.raise Γ)
  change Derives Γ (.ex T) at ht
  apply Derives.exE (p := T) ht
  have hZT : ZFContext.Evidence Ξ := ZFContext.under hZ T
  have hwT : Derives Ξ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw T
  have huT : Derives Ξ (sum w.castSucc a.castSucc b.castSucc u.castSucc) := by simpa only [Formula.raise, sum_rename] using under hu T
  have hvT : Derives Ξ (sum w.castSucc a.castSucc c.castSucc v.castSucc) := by simpa only [Formula.raise, sum_rename] using under hv T
  have hrT : Derives Ξ (sum w.castSucc u.castSucc c.castSucc r.castSucc) := by simpa only [Formula.raise, sum_rename] using under hr T
  have hT : Derives Ξ T := .hyp (Or.inl rfl)
  have har := add_associate hZT _ _ _ _ _ _ _ hwT (under ha T) (under hb T) (under hc T) huT (.conjR hT) hrT
  have hcb := add_commute hZT _ _ _ _ hwT (under hb T) (under hc T) (.conjR hT)
  simpa only [Formula.raise, sum_rename] using add_unassociate hZT _ _ _ _ _ _ _ hwT (under ha T) (under hc T) (under hb T) hvT hcb har

theorem interchange {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b c d u v x y r : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w))
    (hc : Derives Γ (.mem c w)) (hd : Derives Γ (.mem d w))
    (hu : Derives Γ (sum w a b u)) (hv : Derives Γ (sum w c d v))
    (hx : Derives Γ (sum w a c x)) (hy : Derives Γ (sum w b d y)) (hr : Derives Γ (sum w u v r)) : Derives Γ (sum w x y r) := by
  have huW := add_range hZ _ _ _ _ hw ha hu
  have hk := add_exists hZ w u c hw huW hc
  let K := (Formula.mem (Fin.last m) w.castSucc).conj (sum w.castSucc u.castSucc c.castSucc (Fin.last m))
  let Ξ := Context.add K (Context.image Formula.raise Γ)
  change Derives Γ (.ex K) at hk
  apply Derives.exE (p := K) hk
  have hZK : ZFContext.Evidence Ξ := ZFContext.under hZ K
  have hwK : Derives Ξ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw K
  have huK : Derives Ξ (sum w.castSucc a.castSucc b.castSucc u.castSucc) := by simpa only [Formula.raise, sum_rename] using under hu K
  have hvK : Derives Ξ (sum w.castSucc c.castSucc d.castSucc v.castSucc) := by simpa only [Formula.raise, sum_rename] using under hv K
  have hxK : Derives Ξ (sum w.castSucc a.castSucc c.castSucc x.castSucc) := by simpa only [Formula.raise, sum_rename] using under hx K
  have hyK : Derives Ξ (sum w.castSucc b.castSucc d.castSucc y.castSucc) := by simpa only [Formula.raise, sum_rename] using under hy K
  have hrK : Derives Ξ (sum w.castSucc u.castSucc v.castSucc r.castSucc) := by simpa only [Formula.raise, sum_rename] using under hr K
  have hK : Derives Ξ K := .hyp (Or.inl rfl)
  have hkd := add_unassociate hZK _ _ _ _ _ _ _ hwK (under huW K) (under hc K) (under hd K) (.conjR hK) hvK hrK
  have hxb := swap_middle hZK _ _ _ _ _ _ _ hwK (under ha K) (under hb K) (under hc K) huK hxK (.conjR hK)
  have hxW := add_range hZK _ _ _ _ hwK (under ha K) hxK
  simpa only [Formula.raise, sum_rename] using add_associate hZK _ _ _ _ _ _ _ hwK hxW (under hb K) (under hd K) hxb hyK hkd
end PPAC.Migration.Internal.NaturalAdditionReassociation
