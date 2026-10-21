import PPAC.Migration.Internal.NaturalAdditionCommutative

/-! 结合律比较实际内部和见证；固定a+b=u后在第三个加数上作对象ω归纳。 -/
namespace PPAC.Migration.Internal.NaturalAdditionAssociative
open Source SourceAlgebra SourceLogic GraphSyntax OmegaSyntax ReplacementPredicates NaturalAdditionSyntax NaturalAdditionTransport
attribute [local irreducible] NaturalRecursionSyntax.matrix

def property {m} (w a b u n : Fin m) : Formula m := .all (.all
  ((sum w.castSucc.castSucc b.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc).imp
    ((sum w.castSucc.castSucc u.castSucc.castSucc n.castSucc.castSucc (Fin.last (m+1))).imp
      (sum w.castSucc.castSucc a.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))))))
def matrix : Formula 5 := property 0 1 2 3 4

theorem property_rename {m k} (w a b u n : Fin m) (r : Fin m → Fin k) :
    (property w a b u n).rename r = property (r w) (r a) (r b) (r u) (r n) := by
  simp only [property, Formula.rename, sum_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem matrix_pred {m} (ρ : Fin 4 → Fin m) (x : Fin m) : MinimalPredicates.pred matrix ρ x = property (ρ 0) (ρ 1) (ρ 2) (ρ 3) x := by
  have h0 : Fin.lastCases x ρ (0 : Fin 5) = ρ 0 := by
    change Fin.lastCases x ρ (0 : Fin 4).castSucc = ρ 0
    exact Fin.lastCases_castSucc _
  have h1 : Fin.lastCases x ρ (1 : Fin 5) = ρ 1 := by
    change Fin.lastCases x ρ (1 : Fin 4).castSucc = ρ 1
    exact Fin.lastCases_castSucc _
  have h2 : Fin.lastCases x ρ (2 : Fin 5) = ρ 2 := by
    change Fin.lastCases x ρ (2 : Fin 4).castSucc = ρ 2
    exact Fin.lastCases_castSucc _
  have h3 : Fin.lastCases x ρ (3 : Fin 5) = ρ 3 := by
    change Fin.lastCases x ρ (3 : Fin 4).castSucc = ρ 3
    exact Fin.lastCases_castSucc _
  have h4 : Fin.lastCases x ρ (4 : Fin 5) = x := by
    change Fin.lastCases x ρ (Fin.last 4) = x
    exact Fin.lastCases_last
  simp only [MinimalPredicates.pred, matrix, property_rename, h0, h1, h2, h3, h4]

theorem property_at {m} {Γ : Context m} (w a b u n v y : Fin m) (hi : Derives Γ (property w a b u n))
    (hv : Derives Γ (sum w b n v)) (hy : Derives Γ (sum w u n y)) : Derives Γ (sum w a v y) := by
  have hp := Derives.allE y (Derives.allE v hi)
  have h : Derives Γ ((sum w b n v).imp ((sum w u n y).imp (sum w a v y))) := by
    simpa only [property, Formula.instantiate, Formula.rename, sum_rename,
      Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hp
  exact .impE (.impE h hv) hy

theorem zero_point {m} {Γ : Context m} (w a b u n v y : Fin m) (hab : Derives Γ (sum w a b u))
    (hn : Derives Γ (empty n)) (hv : Derives Γ (sum w b n v)) (hy : Derives Γ (sum w u n y)) : Derives Γ (sum w a v y) := by
  have hvb := NaturalRecursionLaws.evaluation_zero NaturalSuccessorStep.matrix (params w) w b n v hn hv
  have hyu := NaturalRecursionLaws.evaluation_zero NaturalSuccessorStep.matrix (params w) w u n y hn hy
  exact output_subst w a v u y (eq_symm hyu) (index_subst w a b v u (eq_symm hvb) hab)

theorem advance {m} {Γ : Context m} (hA : ArithmeticContext.Evidence Γ) (w a b u n s v0 y0 v y : Fin m)
    (hc : Derives Γ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0))
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w))
    (hab : Derives Γ (sum w a b u)) (hn : Derives Γ (.mem n w)) (hi : Derives Γ (property w a b u n))
    (hs : Derives Γ (successor s n)) (hv0 : Derives Γ (sum w b n v0)) (hy0 : Derives Γ (sum w u n y0))
    (hv : Derives Γ (sum w b s v)) (hy : Derives Γ (sum w u s y)) : Derives Γ (sum w a v y) := by
  have huW := NaturalAdditionCore.closure w a b u hA.base.extensionality hw ha hab
  have hv0W := NaturalAdditionCore.closure w b n v0 hA.base.extensionality hw hb hv0
  have hvS := NaturalAdditionLaws.successor_forward hA w b n s v0 v hc hw hb hn hs hv0 hv
  have hyS := NaturalAdditionLaws.successor_forward hA w u n s y0 y hc hw huW hn hs hy0 hy
  exact NaturalAdditionLaws.successor_backward hA w a v0 v y0 y hc hw ha hv0W hvS
    (property_at w a b u n v0 y0 hi hv0 hy0) hyS

theorem step_point {m} {Γ : Context m} (hA : ArithmeticContext.Evidence Γ) (w a b u n s v y : Fin m)
    (hc : Derives Γ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0))
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w))
    (hab : Derives Γ (sum w a b u)) (hn : Derives Γ (.mem n w)) (hi : Derives Γ (property w a b u n))
    (hs : Derives Γ (successor s n)) (hv : Derives Γ (sum w b s v)) (hy : Derives Γ (sum w u s y)) : Derives Γ (sum w a v y) := by
  have huW := NaturalAdditionCore.closure _ _ _ _ hA.base.extensionality hw ha hab
  have hv0 := NaturalAdditionCore.exists_sum hA w b n hc hw hb hn
  have hy0 := NaturalAdditionCore.exists_sum hA w u n hc hw huW hn
  let V := (Formula.mem (Fin.last m) w.castSucc).conj (sum w.castSucc b.castSucc n.castSucc (Fin.last m))
  let Ξ := Context.add V (Context.image Formula.raise Γ)
  change Derives Γ (.ex V) at hv0
  apply Derives.exE (p := V) hv0
  let Y := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj (sum w.castSucc.castSucc u.castSucc.castSucc n.castSucc.castSucc (Fin.last (m+1)))
  let Δ := Context.add Y (Context.image Formula.raise Ξ)
  have hy0' : Derives Ξ (existsSum w.castSucc u.castSucc n.castSucc) := by
    simpa only [Formula.raise, existsSum_rename] using under hy0 V
  change Derives Ξ (.ex Y) at hy0'
  apply Derives.exE (p := Y) hy0'
  have lift {q : Formula m} (h : Derives Γ q) : Derives Δ q.raise.raise := under (under h V) Y
  have hA' : ArithmeticContext.Evidence Δ := ArithmeticContext.under (ArithmeticContext.under hA V) Y
  have hc' : Derives Δ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0) := by simpa only [Formula.raise, closed_rename] using lift hc
  have hw' : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using lift hw
  have hab' : Derives Δ (sum w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc u.castSucc.castSucc) := by simpa only [Formula.raise, sum_rename] using lift hab
  have hi' : Derives Δ (property w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc u.castSucc.castSucc n.castSucc.castSucc) := by simpa only [Formula.raise, property_rename] using lift hi
  have hs' : Derives Δ (successor s.castSucc.castSucc n.castSucc.castSucc) := by simpa only [Formula.raise, successor_rename] using lift hs
  have hv' : Derives Δ (sum w.castSucc.castSucc b.castSucc.castSucc s.castSucc.castSucc v.castSucc.castSucc) := by simpa only [Formula.raise, sum_rename] using lift hv
  have hy' : Derives Δ (sum w.castSucc.castSucc u.castSucc.castSucc s.castSucc.castSucc y.castSucc.castSucc) := by simpa only [Formula.raise, sum_rename] using lift hy
  have hV : Derives Δ V.raise := under (Derives.hyp (Γ := Ξ) (Or.inl rfl)) Y
  have hvs : Derives Δ (sum w.castSucc.castSucc b.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc) := by
    simpa only [V, Formula.raise, Formula.rename, sum_rename] using Derives.conjR hV
  have hY : Derives Δ Y := .hyp (Or.inl rfl)
  simpa only [Formula.raise, sum_rename] using advance hA' _ _ _ _ _ _ _ _ _ _ hc' hw' (lift ha) (lift hb) hab' (lift hn) hi' hs' hvs (.conjR hY) hv' hy'

theorem zero_property {m} {Γ : Context m} (w a b u n : Fin m) (hab : Derives Γ (sum w a b u))
    (hn : Derives Γ (empty n)) : Derives Γ (property w a b u n) := by
  apply Derives.allI
  apply Derives.allI
  let Δ := Context.image Formula.raise (Context.image Formula.raise Γ)
  have hab' : Derives Δ (sum w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc u.castSucc.castSucc) := by simpa only [Formula.raise, sum_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hab)
  have hn' : Derives Δ (empty n.castSucc.castSucc) := by simpa only [Formula.raise, empty_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hn)
  apply Derives.impI
  apply Derives.impI
  exact zero_point _ _ _ _ _ _ _ (add (add hab' _) _) (add (add hn' _) _) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem step_property {m} {Γ : Context m} (hA : ArithmeticContext.Evidence Γ) (w a b u n s : Fin m)
    (hc : Derives Γ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0))
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w))
    (hab : Derives Γ (sum w a b u)) (hn : Derives Γ (.mem n w)) (hi : Derives Γ (property w a b u n))
    (hs : Derives Γ (successor s n)) : Derives Γ (property w a b u s) := by
  apply Derives.allI
  apply Derives.allI
  let Δ := Context.image Formula.raise (Context.image Formula.raise Γ)
  have lift {q : Formula m} (h : Derives Γ q) : Derives Δ q.raise.raise := Derives.rename Fin.castSucc (Derives.rename Fin.castSucc h)
  have hA' := ArithmeticContext.rename (ArithmeticContext.rename hA Fin.castSucc) Fin.castSucc
  have hc' : Derives Δ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0) := by simpa only [Formula.raise, closed_rename] using lift hc
  have hw' : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using lift hw
  have hab' : Derives Δ (sum w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc u.castSucc.castSucc) := by simpa only [Formula.raise, sum_rename] using lift hab
  have hi' : Derives Δ (property w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc u.castSucc.castSucc n.castSucc.castSucc) := by simpa only [Formula.raise, property_rename] using lift hi
  have hs' : Derives Δ (successor s.castSucc.castSucc n.castSucc.castSucc) := by simpa only [Formula.raise, successor_rename] using lift hs
  apply Derives.impI
  apply Derives.impI
  exact step_point (ArithmeticContext.add (ArithmeticContext.add hA' _) _) _ _ _ _ _ _ _ _ (add (add hc' _) _) (add (add hw' _) _)
    (add (add (lift ha) _) _) (add (add (lift hb) _) _) (add (add hab' _) _) (add (add (lift hn) _) _) (add (add hi' _) _) (add (add hs' _) _)
    (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem base {m} {Γ : Context m} (w a b u : Fin m) (hab : Derives Γ (sum w a b u)) :
    Derives Γ (OmegaInductionSyntax.base matrix (params4 w a b u)) := by
  simp only [OmegaInductionSyntax.base, matrix_pred, paramsUp, params4_0, params4_1, params4_2, params4_3]
  apply Derives.allI
  have hab' : Derives (Context.image Formula.raise Γ) (sum w.castSucc a.castSucc b.castSucc u.castSucc) := by simpa only [Formula.raise, sum_rename] using Derives.rename Fin.castSucc hab
  apply Derives.impI
  exact zero_property _ _ _ _ _ (add hab' _) (.hyp (Or.inl rfl))

theorem step {m} {Γ : Context m} (hA : ArithmeticContext.Evidence Γ) (w a b u : Fin m)
    (hc : Derives Γ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0))
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w))
    (hab : Derives Γ (sum w a b u)) : Derives Γ (OmegaInductionSyntax.step matrix (params4 w a b u) w) := by
  simp only [OmegaInductionSyntax.step, matrix_pred, paramsUp, params4_0, params4_1, params4_2, params4_3]
  apply Derives.allI
  apply Derives.allI
  let Δ := Context.image Formula.raise (Context.image Formula.raise Γ)
  have lift {q : Formula m} (h : Derives Γ q) : Derives Δ q.raise.raise := Derives.rename Fin.castSucc (Derives.rename Fin.castSucc h)
  have hA' := ArithmeticContext.rename (ArithmeticContext.rename hA Fin.castSucc) Fin.castSucc
  have hc' : Derives Δ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0) := by simpa only [Formula.raise, closed_rename] using lift hc
  have hw' : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using lift hw
  have hab' : Derives Δ (sum w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc u.castSucc.castSucc) := by simpa only [Formula.raise, sum_rename] using lift hab
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact step_property (ArithmeticContext.add (ArithmeticContext.add (ArithmeticContext.add hA' _) _) _) _ _ _ _ _ _
    (add (add (add hc' _) _) _) (add (add (add hw' _) _) _) (add (add (add (lift ha) _) _) _) (add (add (add (lift hb) _) _) _) (add (add (add hab' _) _) _)
    (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem all_associative {m} {Γ : Context m} (hA : ArithmeticContext.Evidence Γ) (w a b u : Fin m)
    (hc : Derives Γ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0))
    (hsep : Derives Γ ((Source.SetLanguage.separation matrix).rename Fin.elim0))
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w))
    (hab : Derives Γ (sum w a b u)) :
    Derives Γ (.all ((Formula.mem (Fin.last m) w.castSucc).imp (property w.castSucc a.castSucc b.castSucc u.castSucc (Fin.last m)))) := by
  have hi := OmegaInduction.induction_on_omega matrix (params4 w a b u) w hsep hw (base w a b u hab) (step hA w a b u hc hw ha hb hab)
  simpa only [OmegaInductionSyntax.holds, matrix_pred, paramsUp, params4_0, params4_1, params4_2, params4_3] using hi

theorem associate {m} {Γ : Context m} (hA : ArithmeticContext.Evidence Γ) (w a b u n v y : Fin m)
    (hc : Derives Γ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0))
    (hsep : Derives Γ ((Source.SetLanguage.separation matrix).rename Fin.elim0))
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w)) (hn : Derives Γ (.mem n w))
    (hab : Derives Γ (sum w a b u)) (hv : Derives Γ (sum w b n v)) (hy : Derives Γ (sum w u n y)) : Derives Γ (sum w a v y) := by
  have hi := Derives.allE n (all_associative hA w a b u hc hsep hw ha hb hab)
  have hp : Derives Γ ((Formula.mem n w).imp (property w a b u n)) := by
    simpa only [Formula.instantiate, Formula.rename, property_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi
  exact property_at w a b u n v y (.impE hp hn) hv hy
end PPAC.Migration.Internal.NaturalAdditionAssociative
