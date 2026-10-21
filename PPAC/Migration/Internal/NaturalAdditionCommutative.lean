import PPAC.Migration.Internal.NaturalAdditionShift

/-! 用全部内部自然数上的ω归纳证明加法交换，非宿主Nat归纳。 -/
namespace PPAC.Migration.Internal.NaturalAdditionCommutative
open Source SourceAlgebra SourceLogic GraphSyntax OmegaSyntax ReplacementPredicates NaturalAdditionSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

def property {m} (w a n : Fin m) : Formula m := .all
  ((sum w.castSucc a.castSucc n.castSucc (Fin.last m)).imp (sum w.castSucc n.castSucc a.castSucc (Fin.last m)))
def matrix : Formula 3 := property 0 1 2

theorem property_rename {m k} (w a n : Fin m) (r : Fin m → Fin k) :
    (property w a n).rename r = property (r w) (r a) (r n) := by
  simp only [property, Formula.rename, sum_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

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

theorem property_at {m} {Γ : Context m} (w a n y : Fin m) (hi : Derives Γ (property w a n))
    (hy : Derives Γ (sum w a n y)) : Derives Γ (sum w n a y) := by
  have hp := Derives.allE y hi
  have h : Derives Γ ((sum w a n y).imp (sum w n a y)) := by
    simpa only [property, Formula.instantiate, Formula.rename, sum_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hp
  exact .impE h hy

theorem zero_point {m} {Γ : Context m} (hA : ArithmeticContext.Evidence Γ) (w a n y : Fin m)
    (hc : Derives Γ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0))
    (hzsep : Derives Γ ((Source.SetLanguage.separation NaturalAdditionZero.matrix).rename Fin.elim0))
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hn : Derives Γ (empty n))
    (hy : Derives Γ (sum w a n y)) : Derives Γ (sum w n a y) := by
  have hya := NaturalRecursionLaws.evaluation_zero NaturalSuccessorStep.matrix (params w) w a n y hn hy
  have hi := Derives.allE a (NaturalAdditionZero.all_left_zero hA w n hc hzsep hw hn)
  have hp : Derives Γ ((Formula.mem a w).imp (sum w n a a)) := by
    simpa only [Formula.instantiate, Formula.rename, sum_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi
  exact output_subst w n a a y (eq_symm hya) (.impE hp ha)

theorem step_point {m} {Γ : Context m} (hA : ArithmeticContext.Evidence Γ) (w a n s y : Fin m)
    (hc : Derives Γ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0))
    (hsep : Derives Γ ((Source.SetLanguage.separation NaturalAdditionShift.matrix).rename Fin.elim0))
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hn : Derives Γ (.mem n w))
    (hi : Derives Γ (property w a n)) (hs : Derives Γ (successor s n)) (hy : Derives Γ (sum w a s y)) : Derives Γ (sum w s a y) := by
  have ht := NaturalAdditionCore.exists_sum hA w a n hc hw ha hn
  let T := (Formula.mem (Fin.last m) w.castSucc).conj (sum w.castSucc a.castSucc n.castSucc (Fin.last m))
  let Ξ := Context.add T (Context.image Formula.raise Γ)
  change Derives Γ (.ex T) at ht
  apply Derives.exE (p := T) ht
  have hAT : ArithmeticContext.Evidence Ξ := ArithmeticContext.under hA T
  have hcT : Derives Ξ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0) := by simpa only [Formula.raise, closed_rename] using under hc T
  have hsepT : Derives Ξ ((Source.SetLanguage.separation NaturalAdditionShift.matrix).rename Fin.elim0) := by simpa only [Formula.raise, closed_rename] using under hsep T
  have hwT : Derives Ξ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw T
  have hiT : Derives Ξ (property w.castSucc a.castSucc n.castSucc) := by simpa only [Formula.raise, property_rename] using under hi T
  have hsT : Derives Ξ (successor s.castSucc n.castSucc) := by simpa only [Formula.raise, successor_rename] using under hs T
  have hyT : Derives Ξ (sum w.castSucc a.castSucc s.castSucc y.castSucc) := by simpa only [Formula.raise, sum_rename] using under hy T
  have hT : Derives Ξ T := .hyp (Or.inl rfl)
  have hyt := NaturalAdditionLaws.successor_forward hAT _ _ _ _ _ _ hcT hwT (under ha T) (under hn T) hsT (.conjR hT) hyT
  have hna := property_at _ _ _ _ hiT (.conjR hT)
  simpa only [Formula.raise, sum_rename] using NaturalAdditionShift.shift_at hAT _ _ _ _ _ _ hcT hsepT hwT (under hn T) hsT (under ha T) hna hyt

theorem zero_property {m} {Γ : Context m} (hA : ArithmeticContext.Evidence Γ) (w a n : Fin m)
    (hc : Derives Γ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0))
    (hzsep : Derives Γ ((Source.SetLanguage.separation NaturalAdditionZero.matrix).rename Fin.elim0))
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hn : Derives Γ (empty n)) : Derives Γ (property w a n) := by
  apply Derives.allI
  let Δ := Context.image Formula.raise Γ
  have hc' : Derives Δ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0) := by simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc hc
  have hzsep' : Derives Δ ((Source.SetLanguage.separation NaturalAdditionZero.matrix).rename Fin.elim0) := by simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc hzsep
  have hw' : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using Derives.rename Fin.castSucc hw
  have hn' : Derives Δ (empty n.castSucc) := by simpa only [Formula.raise, empty_rename] using Derives.rename Fin.castSucc hn
  apply Derives.impI
  exact zero_point (ArithmeticContext.add (ArithmeticContext.rename hA Fin.castSucc) _) _ _ _ _ (add hc' _) (add hzsep' _) (add hw' _) (add (Derives.rename Fin.castSucc ha) _) (add hn' _) (.hyp (Or.inl rfl))

theorem step_property {m} {Γ : Context m} (hA : ArithmeticContext.Evidence Γ) (w a n s : Fin m)
    (hc : Derives Γ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0))
    (hsep : Derives Γ ((Source.SetLanguage.separation NaturalAdditionShift.matrix).rename Fin.elim0))
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hn : Derives Γ (.mem n w))
    (hi : Derives Γ (property w a n)) (hs : Derives Γ (successor s n)) : Derives Γ (property w a s) := by
  apply Derives.allI
  let Δ := Context.image Formula.raise Γ
  have hc' : Derives Δ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0) := by simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc hc
  have hsep' : Derives Δ ((Source.SetLanguage.separation NaturalAdditionShift.matrix).rename Fin.elim0) := by simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc hsep
  have hw' : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using Derives.rename Fin.castSucc hw
  have hi' : Derives Δ (property w.castSucc a.castSucc n.castSucc) := by simpa only [Formula.raise, property_rename] using Derives.rename Fin.castSucc hi
  have hs' : Derives Δ (successor s.castSucc n.castSucc) := by simpa only [Formula.raise, successor_rename] using Derives.rename Fin.castSucc hs
  apply Derives.impI
  exact step_point (ArithmeticContext.add (ArithmeticContext.rename hA Fin.castSucc) _) _ _ _ _ _ (add hc' _) (add hsep' _) (add hw' _)
    (add (Derives.rename Fin.castSucc ha) _) (add (Derives.rename Fin.castSucc hn) _) (add hi' _) (add hs' _) (.hyp (Or.inl rfl))

theorem base {m} {Γ : Context m} (hA : ArithmeticContext.Evidence Γ) (w a : Fin m)
    (hc : Derives Γ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0))
    (hzsep : Derives Γ ((Source.SetLanguage.separation NaturalAdditionZero.matrix).rename Fin.elim0))
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) : Derives Γ (OmegaInductionSyntax.base matrix (Source.SetLanguage.args2 w a)) := by
  simp only [OmegaInductionSyntax.base, matrix_pred, paramsUp, PairSyntax.args2_first, PairSyntax.args2_second]
  apply Derives.allI
  let Δ := Context.image Formula.raise Γ
  have hc' : Derives Δ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0) := by simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc hc
  have hzsep' : Derives Δ ((Source.SetLanguage.separation NaturalAdditionZero.matrix).rename Fin.elim0) := by simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc hzsep
  have hw' : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using Derives.rename Fin.castSucc hw
  apply Derives.impI
  exact zero_property (ArithmeticContext.add (ArithmeticContext.rename hA Fin.castSucc) _) _ _ _ (add hc' _) (add hzsep' _) (add hw' _) (add (Derives.rename Fin.castSucc ha) _) (.hyp (Or.inl rfl))

theorem step {m} {Γ : Context m} (hA : ArithmeticContext.Evidence Γ) (w a : Fin m)
    (hc : Derives Γ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0))
    (hsep : Derives Γ ((Source.SetLanguage.separation NaturalAdditionShift.matrix).rename Fin.elim0))
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) : Derives Γ (OmegaInductionSyntax.step matrix (Source.SetLanguage.args2 w a) w) := by
  simp only [OmegaInductionSyntax.step, matrix_pred, paramsUp, PairSyntax.args2_first, PairSyntax.args2_second]
  apply Derives.allI
  apply Derives.allI
  let Δ := Context.image Formula.raise (Context.image Formula.raise Γ)
  have hA' := ArithmeticContext.rename (ArithmeticContext.rename hA Fin.castSucc) Fin.castSucc
  have hc' : Derives Δ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0) := by simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hc)
  have hsep' : Derives Δ ((Source.SetLanguage.separation NaturalAdditionShift.matrix).rename Fin.elim0) := by simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hsep)
  have hw' : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hw)
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact step_property (ArithmeticContext.add (ArithmeticContext.add (ArithmeticContext.add hA' _) _) _) _ _ _ _
    (add (add (add hc' _) _) _) (add (add (add hsep' _) _) _) (add (add (add hw' _) _) _)
    (add (add (add (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc ha)) _) _) _)
    (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem all_commutative {m} {Γ : Context m} (hA : ArithmeticContext.Evidence Γ) (w a : Fin m)
    (hc : Derives Γ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0))
    (hcsep : Derives Γ ((Source.SetLanguage.separation matrix).rename Fin.elim0))
    (hssep : Derives Γ ((Source.SetLanguage.separation NaturalAdditionShift.matrix).rename Fin.elim0))
    (hzsep : Derives Γ ((Source.SetLanguage.separation NaturalAdditionZero.matrix).rename Fin.elim0))
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) :
    Derives Γ (.all ((Formula.mem (Fin.last m) w.castSucc).imp (property w.castSucc a.castSucc (Fin.last m)))) := by
  have hi := OmegaInduction.induction_on_omega matrix (Source.SetLanguage.args2 w a) w hcsep hw
    (base hA w a hc hzsep hw ha) (step hA w a hc hssep hw ha)
  simpa only [OmegaInductionSyntax.holds, matrix_pred, paramsUp, PairSyntax.args2_first, PairSyntax.args2_second] using hi

theorem commute {m} {Γ : Context m} (hA : ArithmeticContext.Evidence Γ) (w a n y : Fin m)
    (hc : Derives Γ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0))
    (hcsep : Derives Γ ((Source.SetLanguage.separation matrix).rename Fin.elim0))
    (hssep : Derives Γ ((Source.SetLanguage.separation NaturalAdditionShift.matrix).rename Fin.elim0))
    (hzsep : Derives Γ ((Source.SetLanguage.separation NaturalAdditionZero.matrix).rename Fin.elim0))
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hn : Derives Γ (.mem n w)) (hy : Derives Γ (sum w a n y)) :
    Derives Γ (sum w n a y) := by
  have hi := Derives.allE n (all_commutative hA w a hc hcsep hssep hzsep hw ha)
  have hp : Derives Γ ((Formula.mem n w).imp (property w a n)) := by
    simpa only [Formula.instantiate, Formula.rename, property_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi
  exact property_at w a n y (.impE hp hn) hy

theorem commutative_iff {m} {Γ : Context m} (hA : ArithmeticContext.Evidence Γ) (w a n y : Fin m)
    (hc : Derives Γ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0))
    (hcsep : Derives Γ ((Source.SetLanguage.separation matrix).rename Fin.elim0))
    (hssep : Derives Γ ((Source.SetLanguage.separation NaturalAdditionShift.matrix).rename Fin.elim0))
    (hzsep : Derives Γ ((Source.SetLanguage.separation NaturalAdditionZero.matrix).rename Fin.elim0))
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hn : Derives Γ (.mem n w)) :
    Derives Γ ((sum w a n y).iff (sum w n a y)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact commute (ArithmeticContext.add hA _) w a n y (add hc _) (add hcsep _) (add hssep _) (add hzsep _) (add hw _) (add ha _) (add hn _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact commute (ArithmeticContext.add hA _) w n a y (add hc _) (add hcsep _) (add hssep _) (add hzsep _) (add hw _) (add hn _) (add ha _) (.hyp (Or.inl rfl))
end PPAC.Migration.Internal.NaturalAdditionCommutative
