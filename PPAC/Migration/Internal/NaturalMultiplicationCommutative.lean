import PPAC.Migration.Internal.NaturalMultiplicationShift

/-! 以已证明左后继方程和实际旧积，作全内部ω上的乘法交换归纳。 -/
namespace PPAC.Migration.Internal.NaturalMultiplicationCommutative
open Source SourceAlgebra SourceLogic OmegaSyntax ReplacementPredicates ZFArithmetic
open NaturalMultiplicationSyntax (product product_rename existsProduct existsProduct_rename)
attribute [local irreducible] NaturalRecursionSyntax.matrix

def property {m} (w a n : Fin m) : Formula m := .all
  ((product w.castSucc a.castSucc n.castSucc (Fin.last m)).imp (product w.castSucc n.castSucc a.castSucc (Fin.last m)))
def matrix : Formula 3 := property 0 1 2

theorem property_rename {m k} (w a n : Fin m) (r : Fin m → Fin k) :
    (property w a n).rename r = property (r w) (r a) (r n) := by
  simp only [property, Formula.rename, product_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem matrix_pred {m} (ρ : Fin 2 → Fin m) (x : Fin m) : MinimalPredicates.pred matrix ρ x = property (ρ 0) (ρ 1) x := by
  have h0 : Fin.lastCases x ρ (0 : Fin 3) = ρ 0 := by
    change Fin.lastCases x ρ (0 : Fin 2).castSucc = ρ 0
    exact Fin.lastCases_castSucc _
  have h1 : Fin.lastCases x ρ (1 : Fin 3) = ρ 1 := by
    change Fin.lastCases x ρ (1 : Fin 2).castSucc = ρ 1
    exact Fin.lastCases_castSucc _
  have h2 : Fin.lastCases x ρ (2 : Fin 3) = x := by
    change Fin.lastCases x ρ (Fin.last 2) = x
    exact Fin.lastCases_last
  simp only [MinimalPredicates.pred, matrix, property_rename, h0, h1, h2]

theorem property_at {m} {Γ : Context m} (w a n p : Fin m) (hi : Derives Γ (property w a n))
    (hp : Derives Γ (product w a n p)) : Derives Γ (product w n a p) := by
  have hp' := Derives.allE p hi
  have h : Derives Γ ((product w a n p).imp (product w n a p)) := by
    simpa only [property, Formula.instantiate, Formula.rename, product_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hp'
  exact .impE h hp

theorem zero_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a n p : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hn : Derives Γ (empty n)) (hp : Derives Γ (product w a n p)) :
    Derives Γ (product w n a p) := by
  have hp0 := NaturalMultiplicationLaws.zero_forward w a n p hn hp
  have hall := NaturalMultiplicationZero.all_left_zero (ZFContext.arithmetic hZ) w n (ZFContext.recAdd hZ) (ZFContext.recMul hZ)
    (ZFContext.separation hZ NaturalMultiplicationZero.matrix) hw hn
  have hi : Derives Γ ((Formula.mem a w).imp (product w n a n)) := by
    simpa only [Formula.instantiate, Formula.rename, product_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.allE a hall
  have heq := OmegaUniversal.empty_unique n p (ZFContext.arithmetic hZ).base.extensionality hn hp0
  exact NaturalMultiplicationSyntax.output_subst w n a n p heq (.impE hi ha)

theorem step_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a n s p : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hn : Derives Γ (.mem n w))
    (hi : Derives Γ (property w a n)) (hs : Derives Γ (successor s n)) (hp : Derives Γ (product w a s p)) : Derives Γ (product w s a p) := by
  have ht := mul_exists hZ w a n hw ha hn
  let T := (Formula.mem (Fin.last m) w.castSucc).conj (product w.castSucc a.castSucc n.castSucc (Fin.last m))
  let Ξ := Context.add T (Context.image Formula.raise Γ)
  change Derives Γ (.ex T) at ht
  apply Derives.exE (p := T) ht
  have hZT : ZFContext.Evidence Ξ := ZFContext.under hZ T
  have hwT : Derives Ξ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw T
  have hiT : Derives Ξ (property w.castSucc a.castSucc n.castSucc) := by simpa only [Formula.raise, property_rename] using under hi T
  have hsT : Derives Ξ (successor s.castSucc n.castSucc) := by simpa only [Formula.raise, successor_rename] using under hs T
  have hpT : Derives Ξ (product w.castSucc a.castSucc s.castSucc p.castSucc) := by simpa only [Formula.raise, product_rename] using under hp T
  have hT : Derives Ξ T := .hyp (Or.inl rfl)
  have hsum := mul_succ_forward hZT _ _ _ _ _ _ hwT (under ha T) (under hn T) hsT (.conjR hT) hpT
  have hswap := property_at _ _ _ _ hiT (.conjR hT)
  simpa only [Formula.raise, product_rename] using NaturalMultiplicationShift.shift_at hZT _ _ _ _ _ _ hwT (under hn T) hsT (under ha T) hswap hsum

theorem zero_property {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a n : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hn : Derives Γ (empty n)) : Derives Γ (property w a n) := by
  apply Derives.allI
  let Δ := Context.image Formula.raise Γ
  have hw' : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using Derives.rename Fin.castSucc hw
  have hn' : Derives Δ (empty n.castSucc) := by simpa only [Formula.raise, empty_rename] using Derives.rename Fin.castSucc hn
  apply Derives.impI
  exact zero_point (ZFContext.add (ZFContext.rename hZ Fin.castSucc) _) _ _ _ _ (add hw' _) (add (Derives.rename Fin.castSucc ha) _) (add hn' _) (.hyp (Or.inl rfl))

theorem step_property {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a n s : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hn : Derives Γ (.mem n w))
    (hi : Derives Γ (property w a n)) (hs : Derives Γ (successor s n)) : Derives Γ (property w a s) := by
  apply Derives.allI
  let Δ := Context.image Formula.raise Γ
  have hw' : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using Derives.rename Fin.castSucc hw
  have hi' : Derives Δ (property w.castSucc a.castSucc n.castSucc) := by simpa only [Formula.raise, property_rename] using Derives.rename Fin.castSucc hi
  have hs' : Derives Δ (successor s.castSucc n.castSucc) := by simpa only [Formula.raise, successor_rename] using Derives.rename Fin.castSucc hs
  apply Derives.impI
  exact step_point (ZFContext.add (ZFContext.rename hZ Fin.castSucc) _) _ _ _ _ _ (add hw' _) (add (Derives.rename Fin.castSucc ha) _) (add (Derives.rename Fin.castSucc hn) _) (add hi' _) (add hs' _) (.hyp (Or.inl rfl))

theorem base {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a : Fin m) (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) :
    Derives Γ (OmegaInductionSyntax.base matrix (Source.SetLanguage.args2 w a)) := by
  simp only [OmegaInductionSyntax.base, matrix_pred, paramsUp, PairSyntax.args2_first, PairSyntax.args2_second]
  apply Derives.allI
  have hw' : Derives (Context.image Formula.raise Γ) (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using Derives.rename Fin.castSucc hw
  apply Derives.impI
  exact zero_property (ZFContext.add (ZFContext.rename hZ Fin.castSucc) _) _ _ _ (add hw' _) (add (Derives.rename Fin.castSucc ha) _) (.hyp (Or.inl rfl))

theorem step {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a : Fin m) (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) :
    Derives Γ (OmegaInductionSyntax.step matrix (Source.SetLanguage.args2 w a) w) := by
  simp only [OmegaInductionSyntax.step, matrix_pred, paramsUp, PairSyntax.args2_first, PairSyntax.args2_second]
  apply Derives.allI
  apply Derives.allI
  let Δ := Context.image Formula.raise (Context.image Formula.raise Γ)
  have hw' : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hw)
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact step_property (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.rename (ZFContext.rename hZ Fin.castSucc) Fin.castSucc) _) _) _) _ _ _ _
    (add (add (add hw' _) _) _) (add (add (add (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc ha)) _) _) _)
    (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem commute {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a n p : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hn : Derives Γ (.mem n w)) (hp : Derives Γ (product w a n p)) : Derives Γ (product w n a p) := by
  have hall := ZFArithmetic.induction hZ matrix (Source.SetLanguage.args2 w a) w hw (base hZ w a hw ha) (step hZ w a hw ha)
  have hi : Derives Γ (.all ((Formula.mem (Fin.last m) w.castSucc).imp (property w.castSucc a.castSucc (Fin.last m)))) := by
    simpa only [OmegaInductionSyntax.holds, matrix_pred, paramsUp, PairSyntax.args2_first, PairSyntax.args2_second] using hall
  have hi' : Derives Γ ((Formula.mem n w).imp (property w a n)) := by
    simpa only [Formula.instantiate, Formula.rename, property_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.allE n hi
  exact property_at w a n p (.impE hi' hn) hp

theorem commutative_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a n p : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hn : Derives Γ (.mem n w)) :
    Derives Γ ((product w a n p).iff (product w n a p)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact commute (ZFContext.add hZ _) _ _ _ _ (add hw _) (add ha _) (add hn _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact commute (ZFContext.add hZ _) _ _ _ _ (add hw _) (add hn _) (add ha _) (.hyp (Or.inl rfl))
end PPAC.Migration.Internal.NaturalMultiplicationCommutative
