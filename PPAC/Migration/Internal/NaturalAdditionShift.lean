import PPAC.Migration.Internal.NaturalAdditionTransport

/-! 左参数后继律经对象ω归纳获得，参数和旧/新和值仍为内部量词。 -/
namespace PPAC.Migration.Internal.NaturalAdditionShift
open Source SourceAlgebra SourceLogic GraphSyntax OmegaSyntax ReplacementPredicates NaturalAdditionSyntax NaturalAdditionTransport
attribute [local irreducible] NaturalRecursionSyntax.matrix

def property {m} (w a b n : Fin m) : Formula m := .all (.all
  ((sum w.castSucc.castSucc a.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc).imp
    ((successor (Fin.last (m+1)) (Fin.last m).castSucc).imp
      (sum w.castSucc.castSucc b.castSucc.castSucc n.castSucc.castSucc (Fin.last (m+1))))))
def matrix : Formula 4 := property 0 1 2 3

theorem property_rename {m k} (w a b n : Fin m) (r : Fin m → Fin k) :
    (property w a b n).rename r = property (r w) (r a) (r b) (r n) := by
  simp only [property, Formula.rename, sum_rename, successor_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem matrix_pred {m} (ρ : Fin 3 → Fin m) (x : Fin m) : MinimalPredicates.pred matrix ρ x = property (ρ 0) (ρ 1) (ρ 2) x := by
  have h0 : Fin.lastCases x ρ (0 : Fin 4) = ρ 0 := by
    change Fin.lastCases x ρ (0 : Fin 3).castSucc = ρ 0
    exact Fin.lastCases_castSucc _
  have h1 : Fin.lastCases x ρ (1 : Fin 4) = ρ 1 := by
    change Fin.lastCases x ρ (1 : Fin 3).castSucc = ρ 1
    exact Fin.lastCases_castSucc _
  have h2 : Fin.lastCases x ρ (2 : Fin 4) = ρ 2 := by
    change Fin.lastCases x ρ (2 : Fin 3).castSucc = ρ 2
    exact Fin.lastCases_castSucc _
  have h3 : Fin.lastCases x ρ (3 : Fin 4) = x := by
    change Fin.lastCases x ρ (Fin.last 3) = x
    exact Fin.lastCases_last
  simp only [MinimalPredicates.pred, matrix, property_rename, h0, h1, h2, h3]

theorem property_at {m} {Γ : Context m} (w a b n y z : Fin m) (hi : Derives Γ (property w a b n))
    (hy : Derives Γ (sum w a n y)) (hz : Derives Γ (successor z y)) : Derives Γ (sum w b n z) := by
  have hp := Derives.allE z (Derives.allE y hi)
  have h : Derives Γ ((sum w a n y).imp ((successor z y).imp (sum w b n z))) := by
    simpa only [property, Formula.instantiate, Formula.rename, sum_rename, successor_rename,
      Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hp
  exact .impE (.impE h hy) hz

theorem zero_point {m} {Γ : Context m} (hA : ArithmeticContext.Evidence Γ) (w a b n y z : Fin m)
    (hc : Derives Γ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0))
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (successor b a))
    (hn : Derives Γ (empty n)) (hy : Derives Γ (sum w a n y)) (hz : Derives Γ (successor z y)) : Derives Γ (sum w b n z) := by
  have hya := NaturalRecursionLaws.evaluation_zero NaturalSuccessorStep.matrix (params w) w a n y hn hy
  have hza := successor_input_subst z y a hya hz
  have hbz := OmegaUniversal.successor_unique b z a hA.base.extensionality hb hza
  have hbw := OmegaStructureAlgebra.successor_member w b a hA.base.extensionality hw ha hb
  exact output_subst w b n b z hbz (NaturalAdditionLaws.zero_value hA w b n hc hw hbw hn)

theorem step_point {m} {Γ : Context m} (hA : ArithmeticContext.Evidence Γ) (w a b n s y z : Fin m)
    (hc : Derives Γ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0))
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (successor b a))
    (hn : Derives Γ (.mem n w)) (hi : Derives Γ (property w a b n)) (hs : Derives Γ (successor s n))
    (hy : Derives Γ (sum w a s y)) (hz : Derives Γ (successor z y)) : Derives Γ (sum w b s z) := by
  have ht := NaturalAdditionCore.exists_sum hA w a n hc hw ha hn
  let T := (Formula.mem (Fin.last m) w.castSucc).conj (sum w.castSucc a.castSucc n.castSucc (Fin.last m))
  let Ξ := Context.add T (Context.image Formula.raise Γ)
  change Derives Γ (.ex T) at ht
  apply Derives.exE (p := T) ht
  have hAT : ArithmeticContext.Evidence Ξ := ArithmeticContext.under hA T
  have hcT : Derives Ξ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hc T
  have hwT : Derives Ξ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw T
  have hbT : Derives Ξ (successor b.castSucc a.castSucc) := by simpa only [Formula.raise, successor_rename] using under hb T
  have hiT : Derives Ξ (property w.castSucc a.castSucc b.castSucc n.castSucc) := by simpa only [Formula.raise, property_rename] using under hi T
  have hsT : Derives Ξ (successor s.castSucc n.castSucc) := by simpa only [Formula.raise, successor_rename] using under hs T
  have hyT : Derives Ξ (sum w.castSucc a.castSucc s.castSucc y.castSucc) := by simpa only [Formula.raise, sum_rename] using under hy T
  have hzT : Derives Ξ (successor z.castSucc y.castSucc) := by simpa only [Formula.raise, successor_rename] using under hz T
  have hT : Derives Ξ T := .hyp (Or.inl rfl)
  have hyt := NaturalAdditionLaws.successor_forward hAT _ _ _ _ _ _ hcT hwT (under ha T) (under hn T) hsT (.conjR hT) hyT
  have hby := property_at _ _ _ _ _ _ hiT (.conjR hT) hyt
  have hbw := OmegaStructureAlgebra.successor_member _ _ _ hAT.base.extensionality hwT (under ha T) hbT
  simpa only [Formula.raise, sum_rename] using NaturalAdditionLaws.successor_backward hAT _ _ _ _ _ _ hcT hwT hbw (under hn T) hsT hby hzT

theorem zero_property {m} {Γ : Context m} (hA : ArithmeticContext.Evidence Γ) (w a b n : Fin m)
    (hc : Derives Γ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0))
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (successor b a))
    (hn : Derives Γ (empty n)) : Derives Γ (property w a b n) := by
  apply Derives.allI
  apply Derives.allI
  let Δ := Context.image Formula.raise (Context.image Formula.raise Γ)
  have hA' := ArithmeticContext.rename (ArithmeticContext.rename hA Fin.castSucc) Fin.castSucc
  have hc' : Derives Δ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hc)
  have hw' : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hw)
  have hb' : Derives Δ (successor b.castSucc.castSucc a.castSucc.castSucc) := by simpa only [Formula.raise, successor_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hb)
  have hn' : Derives Δ (empty n.castSucc.castSucc) := by simpa only [Formula.raise, empty_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hn)
  apply Derives.impI
  apply Derives.impI
  exact zero_point (ArithmeticContext.add (ArithmeticContext.add hA' _) _) _ _ _ _ _ _ (add (add hc' _) _) (add (add hw' _) _)
    (add (add (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc ha)) _) _) (add (add hb' _) _) (add (add hn' _) _)
    (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem step_property {m} {Γ : Context m} (hA : ArithmeticContext.Evidence Γ) (w a b n s : Fin m)
    (hc : Derives Γ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0))
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (successor b a))
    (hn : Derives Γ (.mem n w)) (hi : Derives Γ (property w a b n)) (hs : Derives Γ (successor s n)) : Derives Γ (property w a b s) := by
  apply Derives.allI
  apply Derives.allI
  let Δ := Context.image Formula.raise (Context.image Formula.raise Γ)
  have hA' := ArithmeticContext.rename (ArithmeticContext.rename hA Fin.castSucc) Fin.castSucc
  have hc' : Derives Δ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0) := by simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hc)
  have hw' : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hw)
  have hb' : Derives Δ (successor b.castSucc.castSucc a.castSucc.castSucc) := by simpa only [Formula.raise, successor_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hb)
  have hi' : Derives Δ (property w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc n.castSucc.castSucc) := by simpa only [Formula.raise, property_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hi)
  have hs' : Derives Δ (successor s.castSucc.castSucc n.castSucc.castSucc) := by simpa only [Formula.raise, successor_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hs)
  apply Derives.impI
  apply Derives.impI
  exact step_point (ArithmeticContext.add (ArithmeticContext.add hA' _) _) _ _ _ _ _ _ _ (add (add hc' _) _) (add (add hw' _) _)
    (add (add (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc ha)) _) _) (add (add hb' _) _)
    (add (add (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hn)) _) _) (add (add hi' _) _) (add (add hs' _) _)
    (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem base {m} {Γ : Context m} (hA : ArithmeticContext.Evidence Γ) (w a b : Fin m)
    (hc : Derives Γ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0))
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (successor b a)) :
    Derives Γ (OmegaInductionSyntax.base matrix (params3 w a b)) := by
  simp only [OmegaInductionSyntax.base, matrix_pred, paramsUp, params3_0, params3_1, params3_2]
  apply Derives.allI
  let Δ := Context.image Formula.raise Γ
  have hc' : Derives Δ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0) := by simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc hc
  have hw' : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using Derives.rename Fin.castSucc hw
  have hb' : Derives Δ (successor b.castSucc a.castSucc) := by simpa only [Formula.raise, successor_rename] using Derives.rename Fin.castSucc hb
  apply Derives.impI
  exact zero_property (ArithmeticContext.add (ArithmeticContext.rename hA Fin.castSucc) _) _ _ _ _ (add hc' _) (add hw' _) (add (Derives.rename Fin.castSucc ha) _) (add hb' _) (.hyp (Or.inl rfl))

theorem step {m} {Γ : Context m} (hA : ArithmeticContext.Evidence Γ) (w a b : Fin m)
    (hc : Derives Γ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0))
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (successor b a)) :
    Derives Γ (OmegaInductionSyntax.step matrix (params3 w a b) w) := by
  simp only [OmegaInductionSyntax.step, matrix_pred, paramsUp, params3_0, params3_1, params3_2]
  apply Derives.allI
  apply Derives.allI
  let Δ := Context.image Formula.raise (Context.image Formula.raise Γ)
  have hA' := ArithmeticContext.rename (ArithmeticContext.rename hA Fin.castSucc) Fin.castSucc
  have hc' : Derives Δ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0) := by simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hc)
  have hw' : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hw)
  have hb' : Derives Δ (successor b.castSucc.castSucc a.castSucc.castSucc) := by simpa only [Formula.raise, successor_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hb)
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact step_property (ArithmeticContext.add (ArithmeticContext.add (ArithmeticContext.add hA' _) _) _) _ _ _ _ _
    (add (add (add hc' _) _) _) (add (add (add hw' _) _) _) (add (add (add (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc ha)) _) _) _) (add (add (add hb' _) _) _)
    (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem all_shift {m} {Γ : Context m} (hA : ArithmeticContext.Evidence Γ) (w a b : Fin m)
    (hc : Derives Γ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0))
    (hsep : Derives Γ ((Source.SetLanguage.separation matrix).rename Fin.elim0))
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (successor b a)) :
    Derives Γ (.all ((Formula.mem (Fin.last m) w.castSucc).imp (property w.castSucc a.castSucc b.castSucc (Fin.last m)))) := by
  have hi := OmegaInduction.induction_on_omega matrix (params3 w a b) w hsep hw (base hA w a b hc hw ha hb) (step hA w a b hc hw ha hb)
  simpa only [OmegaInductionSyntax.holds, matrix_pred, paramsUp, params3_0, params3_1, params3_2] using hi

theorem shift_at {m} {Γ : Context m} (hA : ArithmeticContext.Evidence Γ) (w a b n y z : Fin m)
    (hc : Derives Γ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0))
    (hsep : Derives Γ ((Source.SetLanguage.separation matrix).rename Fin.elim0))
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (successor b a))
    (hn : Derives Γ (.mem n w)) (hy : Derives Γ (sum w a n y)) (hz : Derives Γ (successor z y)) : Derives Γ (sum w b n z) := by
  have hi := Derives.allE n (all_shift hA w a b hc hsep hw ha hb)
  have hp : Derives Γ ((Formula.mem n w).imp (property w a b n)) := by
    simpa only [Formula.instantiate, Formula.rename, property_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi
  exact property_at w a b n y z (.impE hp hn) hy hz
end PPAC.Migration.Internal.NaturalAdditionShift
