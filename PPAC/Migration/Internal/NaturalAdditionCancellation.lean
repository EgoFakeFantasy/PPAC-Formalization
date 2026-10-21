import PPAC.Migration.Internal.NaturalAdditionAssociative

/-! 原后继单射与全部内部ω归纳证明右加数抵消，包含实际旧和见证。 -/
namespace PPAC.Migration.Internal.NaturalAdditionCancellation
open Source SourceAlgebra SourceLogic GraphSyntax OmegaSyntax ReplacementPredicates NaturalAdditionSyntax NaturalAdditionTransport
attribute [local irreducible] NaturalRecursionSyntax.matrix

def property {m} (w a b n : Fin m) : Formula m := .all
  ((sum w.castSucc a.castSucc n.castSucc (Fin.last m)).imp
    ((sum w.castSucc b.castSucc n.castSucc (Fin.last m)).imp (.equal a.castSucc b.castSucc)))
def matrix : Formula 4 := property 0 1 2 3

theorem property_rename {m k} (w a b n : Fin m) (r : Fin m → Fin k) :
    (property w a b n).rename r = property (r w) (r a) (r b) (r n) := by
  simp only [property, Formula.rename, sum_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

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

theorem property_at {m} {Γ : Context m} (w a b n y : Fin m) (hi : Derives Γ (property w a b n))
    (ha : Derives Γ (sum w a n y)) (hb : Derives Γ (sum w b n y)) : Derives Γ (.equal a b) := by
  have hp := Derives.allE y hi
  have h : Derives Γ ((sum w a n y).imp ((sum w b n y).imp (.equal a b))) := by
    simpa only [property, Formula.instantiate, Formula.rename, sum_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hp
  exact .impE (.impE h ha) hb

theorem zero_point {m} {Γ : Context m} (w a b n y : Fin m) (hn : Derives Γ (empty n))
    (ha : Derives Γ (sum w a n y)) (hb : Derives Γ (sum w b n y)) : Derives Γ (.equal a b) :=
  eq_trans (eq_symm (NaturalRecursionLaws.evaluation_zero NaturalSuccessorStep.matrix (params w) w a n y hn ha))
    (NaturalRecursionLaws.evaluation_zero NaturalSuccessorStep.matrix (params w) w b n y hn hb)

theorem advance {m} {Γ : Context m} (hA : ArithmeticContext.Evidence Γ) (w a b n s x z y : Fin m)
    (hc : Derives Γ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0))
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w)) (hn : Derives Γ (.mem n w))
    (hi : Derives Γ (property w a b n)) (hs : Derives Γ (successor s n))
    (hx : Derives Γ (sum w a n x)) (hz : Derives Γ (sum w b n z))
    (hay : Derives Γ (sum w a s y)) (hby : Derives Γ (sum w b s y)) : Derives Γ (.equal a b) := by
  have hxW := NaturalAdditionCore.closure w a n x hA.base.extensionality hw ha hx
  have hxT := OmegaStructureAlgebra.element_transitive_at w x
    (OmegaStructureInduction.elements_transitive w hA.transitiveSeparation hw) hxW
  have hxSelf := ObjectIrreflexivity.no_self_member x hA.base.foundation hA.base.pairing
  have hyx := NaturalAdditionLaws.successor_forward hA w a n s x y hc hw ha hn hs hx hay
  have hyz := NaturalAdditionLaws.successor_forward hA w b n s z y hc hw hb hn hs hz hby
  have hxz := OmegaStructureAlgebra.successor_injective y x z hxT hxSelf hyx hyz
  exact property_at w a b n x hi hx (output_subst w b n z x (eq_symm hxz) hz)

theorem step_point {m} {Γ : Context m} (hA : ArithmeticContext.Evidence Γ) (w a b n s y : Fin m)
    (hc : Derives Γ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0))
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w)) (hn : Derives Γ (.mem n w))
    (hi : Derives Γ (property w a b n)) (hs : Derives Γ (successor s n))
    (hay : Derives Γ (sum w a s y)) (hby : Derives Γ (sum w b s y)) : Derives Γ (.equal a b) := by
  have hx := NaturalAdditionCore.exists_sum hA w a n hc hw ha hn
  have hz := NaturalAdditionCore.exists_sum hA w b n hc hw hb hn
  let X := (Formula.mem (Fin.last m) w.castSucc).conj (sum w.castSucc a.castSucc n.castSucc (Fin.last m))
  let Ξ := Context.add X (Context.image Formula.raise Γ)
  change Derives Γ (.ex X) at hx
  apply Derives.exE (p := X) hx
  let Z := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj (sum w.castSucc.castSucc b.castSucc.castSucc n.castSucc.castSucc (Fin.last (m+1)))
  let Δ := Context.add Z (Context.image Formula.raise Ξ)
  have hz' : Derives Ξ (existsSum w.castSucc b.castSucc n.castSucc) := by simpa only [Formula.raise, existsSum_rename] using under hz X
  change Derives Ξ (.ex Z) at hz'
  apply Derives.exE (p := Z) hz'
  have lift {q : Formula m} (h : Derives Γ q) : Derives Δ q.raise.raise := under (under h X) Z
  have hA' : ArithmeticContext.Evidence Δ := ArithmeticContext.under (ArithmeticContext.under hA X) Z
  have hc' : Derives Δ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0) := by simpa only [Formula.raise, closed_rename] using lift hc
  have hw' : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using lift hw
  have hi' : Derives Δ (property w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc n.castSucc.castSucc) := by simpa only [Formula.raise, property_rename] using lift hi
  have hs' : Derives Δ (successor s.castSucc.castSucc n.castSucc.castSucc) := by simpa only [Formula.raise, successor_rename] using lift hs
  have hay' : Derives Δ (sum w.castSucc.castSucc a.castSucc.castSucc s.castSucc.castSucc y.castSucc.castSucc) := by simpa only [Formula.raise, sum_rename] using lift hay
  have hby' : Derives Δ (sum w.castSucc.castSucc b.castSucc.castSucc s.castSucc.castSucc y.castSucc.castSucc) := by simpa only [Formula.raise, sum_rename] using lift hby
  have hX : Derives Δ X.raise := under (Derives.hyp (Γ := Ξ) (Or.inl rfl)) Z
  have hxs : Derives Δ (sum w.castSucc.castSucc a.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc) := by
    simpa only [X, Formula.raise, Formula.rename, sum_rename] using Derives.conjR hX
  have hZ : Derives Δ Z := .hyp (Or.inl rfl)
  exact advance hA' _ _ _ _ _ _ _ _ hc' hw' (lift ha) (lift hb) (lift hn) hi' hs' hxs (.conjR hZ) hay' hby'

theorem zero_property {m} {Γ : Context m} (w a b n : Fin m) (hn : Derives Γ (empty n)) : Derives Γ (property w a b n) := by
  apply Derives.allI
  have hn' : Derives (Context.image Formula.raise Γ) (empty n.castSucc) := by simpa only [Formula.raise, empty_rename] using Derives.rename Fin.castSucc hn
  apply Derives.impI
  apply Derives.impI
  exact zero_point _ _ _ _ _ (add (add hn' _) _) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem step_property {m} {Γ : Context m} (hA : ArithmeticContext.Evidence Γ) (w a b n s : Fin m)
    (hc : Derives Γ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0))
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w)) (hn : Derives Γ (.mem n w))
    (hi : Derives Γ (property w a b n)) (hs : Derives Γ (successor s n)) : Derives Γ (property w a b s) := by
  apply Derives.allI
  let Δ := Context.image Formula.raise Γ
  have lift {q : Formula m} (h : Derives Γ q) : Derives Δ q.raise := Derives.rename Fin.castSucc h
  have hc' : Derives Δ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0) := by simpa only [Formula.raise, closed_rename] using lift hc
  have hw' : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using lift hw
  have hi' : Derives Δ (property w.castSucc a.castSucc b.castSucc n.castSucc) := by simpa only [Formula.raise, property_rename] using lift hi
  have hs' : Derives Δ (successor s.castSucc n.castSucc) := by simpa only [Formula.raise, successor_rename] using lift hs
  apply Derives.impI
  apply Derives.impI
  exact step_point (ArithmeticContext.add (ArithmeticContext.add (ArithmeticContext.rename hA Fin.castSucc) _) _) _ _ _ _ _ _
    (add (add hc' _) _) (add (add hw' _) _) (add (add (lift ha) _) _) (add (add (lift hb) _) _) (add (add (lift hn) _) _) (add (add hi' _) _) (add (add hs' _) _)
    (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem base {m} {Γ : Context m} (w a b : Fin m) : Derives Γ (OmegaInductionSyntax.base matrix (params3 w a b)) := by
  simp only [OmegaInductionSyntax.base, matrix_pred, paramsUp, params3_0, params3_1, params3_2]
  apply Derives.allI
  apply Derives.impI
  exact zero_property _ _ _ _ (.hyp (Or.inl rfl))

theorem step {m} {Γ : Context m} (hA : ArithmeticContext.Evidence Γ) (w a b : Fin m)
    (hc : Derives Γ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0))
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w)) :
    Derives Γ (OmegaInductionSyntax.step matrix (params3 w a b) w) := by
  simp only [OmegaInductionSyntax.step, matrix_pred, paramsUp, params3_0, params3_1, params3_2]
  apply Derives.allI
  apply Derives.allI
  let Δ := Context.image Formula.raise (Context.image Formula.raise Γ)
  have lift {q : Formula m} (h : Derives Γ q) : Derives Δ q.raise.raise := Derives.rename Fin.castSucc (Derives.rename Fin.castSucc h)
  have hA' := ArithmeticContext.rename (ArithmeticContext.rename hA Fin.castSucc) Fin.castSucc
  have hc' : Derives Δ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0) := by simpa only [Formula.raise, closed_rename] using lift hc
  have hw' : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using lift hw
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact step_property (ArithmeticContext.add (ArithmeticContext.add (ArithmeticContext.add hA' _) _) _) _ _ _ _ _
    (add (add (add hc' _) _) _) (add (add (add hw' _) _) _) (add (add (add (lift ha) _) _) _) (add (add (add (lift hb) _) _) _)
    (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem all_cancellation {m} {Γ : Context m} (hA : ArithmeticContext.Evidence Γ) (w a b : Fin m)
    (hc : Derives Γ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0))
    (hsep : Derives Γ ((Source.SetLanguage.separation matrix).rename Fin.elim0))
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w)) :
    Derives Γ (.all ((Formula.mem (Fin.last m) w.castSucc).imp (property w.castSucc a.castSucc b.castSucc (Fin.last m)))) := by
  have hi := OmegaInduction.induction_on_omega matrix (params3 w a b) w hsep hw (base w a b) (step hA w a b hc hw ha hb)
  simpa only [OmegaInductionSyntax.holds, matrix_pred, paramsUp, params3_0, params3_1, params3_2] using hi

theorem cancel_right {m} {Γ : Context m} (hA : ArithmeticContext.Evidence Γ) (w a b n y : Fin m)
    (hc : Derives Γ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0))
    (hsep : Derives Γ ((Source.SetLanguage.separation matrix).rename Fin.elim0))
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w)) (hn : Derives Γ (.mem n w))
    (hay : Derives Γ (sum w a n y)) (hby : Derives Γ (sum w b n y)) : Derives Γ (.equal a b) := by
  have hi := Derives.allE n (all_cancellation hA w a b hc hsep hw ha hb)
  have hp : Derives Γ ((Formula.mem n w).imp (property w a b n)) := by
    simpa only [Formula.instantiate, Formula.rename, property_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi
  exact property_at w a b n y (.impE hp hn) hay hby
end PPAC.Migration.Internal.NaturalAdditionCancellation
