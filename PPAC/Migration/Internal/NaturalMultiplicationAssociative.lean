import PPAC.Migration.Internal.NaturalMultiplicationAssociativeStep

/-! 全内部自然数乘法结合律，逆向由实际乘积的存在唯一性取得。 -/
namespace PPAC.Migration.Internal.NaturalMultiplicationAssociative
open Source SourceAlgebra SourceLogic OmegaSyntax ReplacementPredicates ZFArithmetic
open NaturalAdditionTransport (params4 params4_0 params4_1 params4_2 params4_3)
open NaturalMultiplicationSyntax (product product_rename existsProduct existsProduct_rename)
open NaturalMultiplicationAssociativeSyntax (property property_at property_rename)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem zero_property {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b u n : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hn : Derives Γ (empty n)) : Derives Γ (property w a b u n) := by
  apply Derives.allI
  apply Derives.allI
  let Δ := Context.image Formula.raise (Context.image Formula.raise Γ)
  have lift {f : Formula m} (h : Derives Γ f) : Derives Δ f.raise.raise := Derives.rename Fin.castSucc (Derives.rename Fin.castSucc h)
  have hZ' := ZFContext.rename (ZFContext.rename hZ Fin.castSucc) Fin.castSucc
  have hw' : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using lift hw
  have hn' : Derives Δ (empty n.castSucc.castSucc) := by simpa only [Formula.raise, empty_rename] using lift hn
  apply Derives.impI
  apply Derives.impI
  exact NaturalMultiplicationAssociativeStep.zero_point (ZFContext.add (ZFContext.add hZ' _) _) _ _ _ _ _ _ _ (add (add hw' _) _)
    (add (add (lift ha) _) _) (add (add hn' _) _) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem step_property {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b u n s : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w)) (hn : Derives Γ (.mem n w))
    (hab : Derives Γ (product w a b u)) (hi : Derives Γ (property w a b u n)) (hs : Derives Γ (successor s n)) : Derives Γ (property w a b u s) := by
  apply Derives.allI
  apply Derives.allI
  let Δ := Context.image Formula.raise (Context.image Formula.raise Γ)
  have lift {f : Formula m} (h : Derives Γ f) : Derives Δ f.raise.raise := Derives.rename Fin.castSucc (Derives.rename Fin.castSucc h)
  have hZ' := ZFContext.rename (ZFContext.rename hZ Fin.castSucc) Fin.castSucc
  have hw' : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using lift hw
  have hab' : Derives Δ (product w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc u.castSucc.castSucc) := by simpa only [Formula.raise, product_rename] using lift hab
  have hi' : Derives Δ (property w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc u.castSucc.castSucc n.castSucc.castSucc) := by simpa only [Formula.raise, property_rename] using lift hi
  have hs' : Derives Δ (successor s.castSucc.castSucc n.castSucc.castSucc) := by simpa only [Formula.raise, successor_rename] using lift hs
  apply Derives.impI
  apply Derives.impI
  exact NaturalMultiplicationAssociativeStep.step_point (ZFContext.add (ZFContext.add hZ' _) _) _ _ _ _ _ _ _ _ (add (add hw' _) _)
    (add (add (lift ha) _) _) (add (add (lift hb) _) _) (add (add (lift hn) _) _) (add (add hab' _) _) (add (add hi' _) _) (add (add hs' _) _)
    (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem base {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b u : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) :
    Derives Γ (OmegaInductionSyntax.base NaturalMultiplicationAssociativeSyntax.matrix (params4 w a b u)) := by
  simp only [OmegaInductionSyntax.base, NaturalMultiplicationAssociativeSyntax.matrix_pred, paramsUp, params4_0, params4_1, params4_2, params4_3]
  apply Derives.allI
  have hw' : Derives (Context.image Formula.raise Γ) (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using Derives.rename Fin.castSucc hw
  apply Derives.impI
  exact zero_property (ZFContext.add (ZFContext.rename hZ Fin.castSucc) _) _ _ _ _ _ (add hw' _) (add (Derives.rename Fin.castSucc ha) _) (.hyp (Or.inl rfl))

theorem step {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b u : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w)) (hab : Derives Γ (product w a b u)) :
    Derives Γ (OmegaInductionSyntax.step NaturalMultiplicationAssociativeSyntax.matrix (params4 w a b u) w) := by
  simp only [OmegaInductionSyntax.step, NaturalMultiplicationAssociativeSyntax.matrix_pred, paramsUp, params4_0, params4_1, params4_2, params4_3]
  apply Derives.allI
  apply Derives.allI
  let Δ := Context.image Formula.raise (Context.image Formula.raise Γ)
  have lift {f : Formula m} (h : Derives Γ f) : Derives Δ f.raise.raise := Derives.rename Fin.castSucc (Derives.rename Fin.castSucc h)
  have hw' : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using lift hw
  have hab' : Derives Δ (product w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc u.castSucc.castSucc) := by simpa only [Formula.raise, product_rename] using lift hab
  have hZ' := ZFContext.rename (ZFContext.rename hZ Fin.castSucc) Fin.castSucc
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact step_property (ZFContext.add (ZFContext.add (ZFContext.add hZ' _) _) _) _ _ _ _ _ _ (add (add (add hw' _) _) _)
    (add (add (add (lift ha) _) _) _) (add (add (add (lift hb) _) _) _) (.hyp (Or.inr (Or.inr (Or.inl rfl))))
    (add (add (add hab' _) _) _) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem associate {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b u n v r : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w)) (hn : Derives Γ (.mem n w))
    (hab : Derives Γ (product w a b u)) (hv : Derives Γ (product w b n v)) (hr : Derives Γ (product w u n r)) : Derives Γ (product w a v r) := by
  have hall := ZFArithmetic.induction hZ NaturalMultiplicationAssociativeSyntax.matrix (params4 w a b u) w hw (base hZ w a b u hw ha) (step hZ w a b u hw ha hb hab)
  have hi : Derives Γ (.all ((Formula.mem (Fin.last m) w.castSucc).imp (property w.castSucc a.castSucc b.castSucc u.castSucc (Fin.last m)))) := by
    simpa only [OmegaInductionSyntax.holds, NaturalMultiplicationAssociativeSyntax.matrix_pred, paramsUp, params4_0, params4_1, params4_2, params4_3] using hall
  have hi' : Derives Γ ((Formula.mem n w).imp (property w a b u n)) := by
    simpa only [Formula.instantiate, Formula.rename, property_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.allE n hi
  exact property_at w a b u n v r (.impE hi' hn) hv hr

theorem associate_backward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b u n v r : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w)) (hn : Derives Γ (.mem n w))
    (hab : Derives Γ (product w a b u)) (hv : Derives Γ (product w b n v)) (hr : Derives Γ (product w a v r)) : Derives Γ (product w u n r) := by
  have huW := mul_range hZ _ _ _ _ hw hab
  have ht := mul_exists hZ w u n hw huW hn
  let T := (Formula.mem (Fin.last m) w.castSucc).conj (product w.castSucc u.castSucc n.castSucc (Fin.last m))
  let Ξ := Context.add T (Context.image Formula.raise Γ)
  change Derives Γ (.ex T) at ht
  apply Derives.exE (p := T) ht
  have hZT : ZFContext.Evidence Ξ := ZFContext.under hZ T
  have hwT : Derives Ξ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw T
  have habT : Derives Ξ (product w.castSucc a.castSucc b.castSucc u.castSucc) := by simpa only [Formula.raise, product_rename] using under hab T
  have hvT : Derives Ξ (product w.castSucc b.castSucc n.castSucc v.castSucc) := by simpa only [Formula.raise, product_rename] using under hv T
  have hrT : Derives Ξ (product w.castSucc a.castSucc v.castSucc r.castSucc) := by simpa only [Formula.raise, product_rename] using under hr T
  have hT : Derives Ξ T := .hyp (Or.inl rfl)
  have hm := associate hZT _ _ _ _ _ _ _ hwT (under ha T) (under hb T) (under hn T) habT hvT (.conjR hT)
  have hvW := mul_range hZT _ _ _ _ hwT hvT
  have heq := mul_unique hZT _ _ _ _ _ hwT (under ha T) hvW hm hrT
  simpa only [Formula.raise, product_rename] using NaturalMultiplicationSyntax.output_subst _ _ _ _ _ heq (.conjR hT)

theorem associative_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b u n v r : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w)) (hn : Derives Γ (.mem n w))
    (hab : Derives Γ (product w a b u)) (hv : Derives Γ (product w b n v)) :
    Derives Γ ((product w u n r).iff (product w a v r)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact associate (ZFContext.add hZ _) _ _ _ _ _ _ _ (add hw _) (add ha _) (add hb _) (add hn _) (add hab _) (add hv _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact associate_backward (ZFContext.add hZ _) _ _ _ _ _ _ _ (add hw _) (add ha _) (add hb _) (add hn _) (add hab _) (add hv _) (.hyp (Or.inl rfl))
end PPAC.Migration.Internal.NaturalMultiplicationAssociative
