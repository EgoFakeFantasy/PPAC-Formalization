import PPAC.Migration.Internal.NaturalMultiplicationShiftStep

/-! 全内部自然索引的左后继乘法方程及双向刻画。 -/
namespace PPAC.Migration.Internal.NaturalMultiplicationShift
open Source SourceAlgebra SourceLogic OmegaSyntax ReplacementPredicates NaturalAdditionSyntax ZFArithmetic
open NaturalAdditionTransport (params3 params3_0 params3_1 params3_2)
open NaturalMultiplicationSyntax (product product_rename)
open NaturalMultiplicationShiftSyntax (property property_at property_rename)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem zero_property {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b n : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (successor b a)) (hn : Derives Γ (empty n)) :
    Derives Γ (property w a b n) := by
  apply Derives.allI
  apply Derives.allI
  let Δ := Context.image Formula.raise (Context.image Formula.raise Γ)
  have lift {f : Formula m} (h : Derives Γ f) : Derives Δ f.raise.raise := Derives.rename Fin.castSucc (Derives.rename Fin.castSucc h)
  have hZ' := ZFContext.rename (ZFContext.rename hZ Fin.castSucc) Fin.castSucc
  have hw' : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using lift hw
  have hb' : Derives Δ (successor b.castSucc.castSucc a.castSucc.castSucc) := by simpa only [Formula.raise, successor_rename] using lift hb
  have hn' : Derives Δ (empty n.castSucc.castSucc) := by simpa only [Formula.raise, empty_rename] using lift hn
  apply Derives.impI
  apply Derives.impI
  exact NaturalMultiplicationShiftStep.zero_point (ZFContext.add (ZFContext.add hZ' _) _) _ _ _ _ _ _ (add (add hw' _) _) (add (add (lift ha) _) _)
    (add (add hb' _) _) (add (add hn' _) _) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem step_property {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b n s : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (successor b a)) (hn : Derives Γ (.mem n w))
    (hi : Derives Γ (property w a b n)) (hs : Derives Γ (successor s n)) : Derives Γ (property w a b s) := by
  apply Derives.allI
  apply Derives.allI
  let Δ := Context.image Formula.raise (Context.image Formula.raise Γ)
  have lift {f : Formula m} (h : Derives Γ f) : Derives Δ f.raise.raise := Derives.rename Fin.castSucc (Derives.rename Fin.castSucc h)
  have hZ' := ZFContext.rename (ZFContext.rename hZ Fin.castSucc) Fin.castSucc
  have hw' : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using lift hw
  have hb' : Derives Δ (successor b.castSucc.castSucc a.castSucc.castSucc) := by simpa only [Formula.raise, successor_rename] using lift hb
  have hi' : Derives Δ (property w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc n.castSucc.castSucc) := by simpa only [Formula.raise, property_rename] using lift hi
  have hs' : Derives Δ (successor s.castSucc.castSucc n.castSucc.castSucc) := by simpa only [Formula.raise, successor_rename] using lift hs
  apply Derives.impI
  apply Derives.impI
  exact NaturalMultiplicationShiftStep.step_point (ZFContext.add (ZFContext.add hZ' _) _) _ _ _ _ _ _ _ (add (add hw' _) _) (add (add (lift ha) _) _)
    (add (add hb' _) _) (add (add (lift hn) _) _) (add (add hi' _) _) (add (add hs' _) _) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem base {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (successor b a)) :
    Derives Γ (OmegaInductionSyntax.base NaturalMultiplicationShiftSyntax.matrix (params3 w a b)) := by
  simp only [OmegaInductionSyntax.base, NaturalMultiplicationShiftSyntax.matrix_pred, paramsUp, params3_0, params3_1, params3_2]
  apply Derives.allI
  have hw' : Derives (Context.image Formula.raise Γ) (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using Derives.rename Fin.castSucc hw
  have hb' : Derives (Context.image Formula.raise Γ) (successor b.castSucc a.castSucc) := by simpa only [Formula.raise, successor_rename] using Derives.rename Fin.castSucc hb
  apply Derives.impI
  exact zero_property (ZFContext.add (ZFContext.rename hZ Fin.castSucc) _) _ _ _ _ (add hw' _) (add (Derives.rename Fin.castSucc ha) _) (add hb' _) (.hyp (Or.inl rfl))

theorem step {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (successor b a)) :
    Derives Γ (OmegaInductionSyntax.step NaturalMultiplicationShiftSyntax.matrix (params3 w a b) w) := by
  simp only [OmegaInductionSyntax.step, NaturalMultiplicationShiftSyntax.matrix_pred, paramsUp, params3_0, params3_1, params3_2]
  apply Derives.allI
  apply Derives.allI
  let Δ := Context.image Formula.raise (Context.image Formula.raise Γ)
  have lift {f : Formula m} (h : Derives Γ f) : Derives Δ f.raise.raise := Derives.rename Fin.castSucc (Derives.rename Fin.castSucc h)
  have hZ' := ZFContext.rename (ZFContext.rename hZ Fin.castSucc) Fin.castSucc
  have hw' : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using lift hw
  have hb' : Derives Δ (successor b.castSucc.castSucc a.castSucc.castSucc) := by simpa only [Formula.raise, successor_rename] using lift hb
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact step_property (ZFContext.add (ZFContext.add (ZFContext.add hZ' _) _) _) _ _ _ _ _ (add (add (add hw' _) _) _)
    (add (add (add (lift ha) _) _) _) (add (add (add hb' _) _) _) (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem all_shift {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (successor b a)) :
    Derives Γ (.all ((Formula.mem (Fin.last m) w.castSucc).imp (property w.castSucc a.castSucc b.castSucc (Fin.last m)))) := by
  have hi := ZFArithmetic.induction hZ NaturalMultiplicationShiftSyntax.matrix (params3 w a b) w hw (base hZ w a b hw ha hb) (step hZ w a b hw ha hb)
  simpa only [OmegaInductionSyntax.holds, NaturalMultiplicationShiftSyntax.matrix_pred, paramsUp, params3_0, params3_1, params3_2] using hi

theorem shift_at {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b n p r : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (successor b a)) (hn : Derives Γ (.mem n w))
    (hp : Derives Γ (product w a n p)) (hr : Derives Γ (sum w p n r)) : Derives Γ (product w b n r) := by
  have hi := Derives.allE n (all_shift hZ w a b hw ha hb)
  have hi' : Derives Γ ((Formula.mem n w).imp (property w a b n)) := by
    simpa only [Formula.instantiate, Formula.rename, property_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi
  exact property_at w a b n p r (.impE hi' hn) hp hr

theorem shift_backward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b n p r : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (successor b a)) (hn : Derives Γ (.mem n w))
    (hp : Derives Γ (product w a n p)) (hr : Derives Γ (product w b n r)) : Derives Γ (sum w p n r) := by
  have hpW := mul_range hZ _ _ _ _ hw hp
  have ht := add_exists hZ w p n hw hpW hn
  let T := (Formula.mem (Fin.last m) w.castSucc).conj (sum w.castSucc p.castSucc n.castSucc (Fin.last m))
  let Ξ := Context.add T (Context.image Formula.raise Γ)
  change Derives Γ (.ex T) at ht
  apply Derives.exE (p := T) ht
  have hZT : ZFContext.Evidence Ξ := ZFContext.under hZ T
  have hwT : Derives Ξ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw T
  have hbT : Derives Ξ (successor b.castSucc a.castSucc) := by simpa only [Formula.raise, successor_rename] using under hb T
  have hpT : Derives Ξ (product w.castSucc a.castSucc n.castSucc p.castSucc) := by simpa only [Formula.raise, product_rename] using under hp T
  have hrT : Derives Ξ (product w.castSucc b.castSucc n.castSucc r.castSucc) := by simpa only [Formula.raise, product_rename] using under hr T
  have hT : Derives Ξ T := .hyp (Or.inl rfl)
  have hm := shift_at hZT _ _ _ _ _ _ hwT (under ha T) hbT (under hn T) hpT (.conjR hT)
  have hbW := OmegaStructureAlgebra.successor_member _ _ _ (ZFContext.arithmetic hZT).base.extensionality hwT (under ha T) hbT
  have heq := mul_unique hZT _ _ _ _ _ hwT hbW (under hn T) hm hrT
  simpa only [Formula.raise, sum_rename] using NaturalAdditionSyntax.output_subst _ _ _ _ _ heq (.conjR hT)

theorem shift_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b n p r : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (successor b a)) (hn : Derives Γ (.mem n w))
    (hp : Derives Γ (product w a n p)) : Derives Γ ((product w b n r).iff (sum w p n r)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact shift_backward (ZFContext.add hZ _) _ _ _ _ _ _ (add hw _) (add ha _) (add hb _) (add hn _) (add hp _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact shift_at (ZFContext.add hZ _) _ _ _ _ _ _ (add hw _) (add ha _) (add hb _) (add hn _) (add hp _) (.hyp (Or.inl rfl))
end PPAC.Migration.Internal.NaturalMultiplicationShift
