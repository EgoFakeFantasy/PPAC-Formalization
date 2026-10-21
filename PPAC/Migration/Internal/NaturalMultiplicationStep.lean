import PPAC.Migration.Internal.ObjectNaturalAddition

/-! 固定自然数a的乘法步进：自然累积值x映到x+a，ω外输入映到零。 -/
namespace PPAC.Migration.Internal.NaturalMultiplicationStep
open Source SourceAlgebra SourceLogic GraphSyntax OmegaSyntax ReplacementPredicates NaturalRecursionSyntax

def step {m} (w a x y : Fin m) : Formula m :=
  ((Formula.mem x w).conj (NaturalAdditionSyntax.sum w x a y)).disj ((Formula.mem x w).neg.conj (empty y))
def hasStep {m} (w a x : Fin m) : Formula m := .ex (step w.castSucc a.castSucc x.castSucc (Fin.last m))
def matrix : Formula 4 := step 0 1 2 3

theorem step_rename {m k} (w a x y : Fin m) (r : Fin m → Fin k) :
    (step w a x y).rename r = step (r w) (r a) (r x) (r y) := by
  simp only [step, Formula.rename, Formula.neg, NaturalAdditionSyntax.sum_rename, empty_rename]
theorem hasStep_rename {m k} (w a x : Fin m) (r : Fin m → Fin k) :
    (hasStep w a x).rename r = hasStep (r w) (r a) (r x) := by
  simp only [hasStep, Formula.rename, step_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem matrix_rel {m} (ρ : Fin 2 → Fin m) (x y : Fin m) : rel matrix ρ x y = step (ρ 0) (ρ 1) x y := by
  have h0 : Fin.lastCases y (Fin.lastCases x ρ) (0 : Fin 4) = ρ 0 := by
    change Fin.lastCases y (Fin.lastCases x ρ) (0 : Fin 2).castSucc.castSucc = ρ 0
    simp only [Fin.lastCases_castSucc]
  have h1 : Fin.lastCases y (Fin.lastCases x ρ) (1 : Fin 4) = ρ 1 := by
    change Fin.lastCases y (Fin.lastCases x ρ) (1 : Fin 2).castSucc.castSucc = ρ 1
    simp only [Fin.lastCases_castSucc]
  have h2 : Fin.lastCases y (Fin.lastCases x ρ) (2 : Fin 4) = x := by
    change Fin.lastCases y (Fin.lastCases x ρ) (Fin.last 2).castSucc = x
    simp only [Fin.lastCases_castSucc, Fin.lastCases_last]
  have h3 : Fin.lastCases y (Fin.lastCases x ρ) (3 : Fin 4) = y := by
    change Fin.lastCases y (Fin.lastCases x ρ) (Fin.last 3) = y
    exact Fin.lastCases_last
  simp only [rel, Source.SetLanguage.relation, matrix, step_rename, h0, h1, h2, h3]

theorem intro_value {m} {Γ : Context m} (w a x y : Fin m) (hy : Derives Γ (step w a x y)) : Derives Γ (hasStep w a x) := by
  apply Derives.exI y
  simpa only [Formula.instantiate, step_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hy

theorem exists_step {m} {Γ : Context m} (hA : ArithmeticContext.Evidence Γ) (w a x : Fin m)
    (hc : Derives Γ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0))
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) : Derives Γ (hasStep w a x) := by
  apply SourcePropositional.by_cases (.mem x w) (hasStep w a x)
  · let M := Formula.mem x w
    let Γm := Context.add M Γ
    have hs := NaturalAdditionCore.exists_sum (ArithmeticContext.add hA M) w x a (add hc M) (add hw M) (.hyp (Or.inl rfl)) (add ha M)
    let Y := (Formula.mem (Fin.last m) w.castSucc).conj (NaturalAdditionSyntax.sum w.castSucc x.castSucc a.castSucc (Fin.last m))
    let Ξ := Context.add Y (Context.image Formula.raise Γm)
    change Derives Γm (.ex Y) at hs
    apply Derives.exE (p := Y) hs
    have hxY : Derives Ξ (.mem x.castSucc w.castSucc) := under (Derives.hyp (Γ := Γm) (Or.inl rfl)) Y
    have hY : Derives Ξ Y := .hyp (Or.inl rfl)
    have hst : Derives Ξ (step w.castSucc a.castSucc x.castSucc (Fin.last m)) := .disjL (.conjI hxY (.conjR hY))
    simpa only [Formula.raise, hasStep_rename] using intro_value w.castSucc a.castSucc x.castSucc (Fin.last m) hst
  · let M := (Formula.mem x w).neg
    let Γm := Context.add M Γ
    have hz : Derives Γm (zeroIn w) := add (.conjL (.conjL hw)) M
    let Z := (Formula.mem (Fin.last m) w.castSucc).conj (empty (Fin.last m))
    let Ξ := Context.add Z (Context.image Formula.raise Γm)
    change Derives Γm (.ex Z) at hz
    apply Derives.exE (p := Z) hz
    have hxZ : Derives Ξ (Formula.mem x.castSucc w.castSucc).neg := under (Derives.hyp (Γ := Γm) (Or.inl rfl)) Z
    have hZ : Derives Ξ Z := .hyp (Or.inl rfl)
    have hst : Derives Ξ (step w.castSucc a.castSucc x.castSucc (Fin.last m)) := .disjR (.conjI hxZ (.conjR hZ))
    simpa only [Formula.raise, hasStep_rename] using intro_value w.castSucc a.castSucc x.castSucc (Fin.last m) hst

theorem functional_point {m} {Γ : Context m} (hA : ArithmeticContext.Evidence Γ) (w a x y z : Fin m)
    (hc : Derives Γ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0))
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w))
    (hy : Derives Γ (step w a x y)) (hz : Derives Γ (step w a x z)) : Derives Γ (.equal y z) := by
  apply Derives.disjE hy
  · apply Derives.disjE (add hz _)
    · exact NaturalAdditionCore.unique (ArithmeticContext.add (ArithmeticContext.add hA _) _) w x a y z
        (add (add hc _) _) (add (add hw _) _) (add (add ha _) _)
        (.conjR (.hyp (Or.inr (Or.inl rfl)))) (.conjR (.hyp (Or.inl rfl)))
    · exact .botE (.impE (.conjL (.hyp (Or.inl rfl))) (.conjL (.hyp (Or.inr (Or.inl rfl)))))
  · apply Derives.disjE (add hz _)
    · exact .botE (.impE (.conjL (.hyp (Or.inr (Or.inl rfl)))) (.conjL (.hyp (Or.inl rfl))))
    · exact OmegaUniversal.empty_unique y z (add (add hA.base.extensionality _) _) (.conjR (.hyp (Or.inr (Or.inl rfl)))) (.conjR (.hyp (Or.inl rfl)))

theorem range_point {m} {Γ : Context m} (w a x y : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hw : Derives Γ (omega w)) (hy : Derives Γ (step w a x y)) : Derives Γ (.mem y w) := by
  apply Derives.disjE hy
  · exact NaturalAdditionCore.closure w x a y (add he _) (add hw _) (.conjL (.hyp (Or.inl rfl))) (.conjR (.hyp (Or.inl rfl)))
  · exact OmegaStructureAlgebra.zero_member w y (add he _) (add hw _) (.conjR (.hyp (Or.inl rfl)))

theorem on_natural {m} {Γ : Context m} (w a x y : Fin m) (hx : Derives Γ (.mem x w))
    (hy : Derives Γ (step w a x y)) : Derives Γ (NaturalAdditionSyntax.sum w x a y) := by
  apply Derives.disjE hy
  · exact .conjR (.hyp (Or.inl rfl))
  · exact .botE (.impE (.conjL (.hyp (Or.inl rfl))) (add hx _))

theorem total {m} {Γ : Context m} (hA : ArithmeticContext.Evidence Γ) (ρ : Fin 2 → Fin m)
    (hc : Derives Γ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0))
    (hw : Derives Γ (omega (ρ 0))) (ha : Derives Γ (.mem (ρ 1) (ρ 0))) : Derives Γ (relationTotal matrix ρ) := by
  simp only [relationTotal, matrix_rel, paramsUp]
  apply Derives.allI
  let Δ := Context.image Formula.raise Γ
  have hc' : Derives Δ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc hc
  have hw' : Derives Δ (omega (ρ 0).castSucc) := by
    simpa only [Formula.raise, omega_rename] using Derives.rename Fin.castSucc hw
  exact exists_step (ArithmeticContext.rename hA Fin.castSucc) (ρ 0).castSucc (ρ 1).castSucc (Fin.last m) hc' hw' (Derives.rename Fin.castSucc ha)

theorem functional {m} {Γ : Context m} (hA : ArithmeticContext.Evidence Γ) (ρ : Fin 2 → Fin m)
    (hc : Derives Γ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0))
    (hw : Derives Γ (omega (ρ 0))) (ha : Derives Γ (.mem (ρ 1) (ρ 0))) : Derives Γ (relationFunctional matrix ρ) := by
  simp only [relationFunctional, matrix_rel, paramsUp]
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  let Δ := Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ))
  have hA' := ArithmeticContext.rename (ArithmeticContext.rename (ArithmeticContext.rename hA Fin.castSucc) Fin.castSucc) Fin.castSucc
  have hc' : Derives Δ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using OrdinalRestriction.raise_three hc
  have hw' : Derives Δ (omega (ρ 0).castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, omega_rename] using OrdinalRestriction.raise_three hw
  have ha' : Derives Δ (.mem (ρ 1).castSucc.castSucc.castSucc (ρ 0).castSucc.castSucc.castSucc) := OrdinalRestriction.raise_three ha
  apply Derives.impI
  apply Derives.impI
  exact functional_point (ArithmeticContext.add (ArithmeticContext.add hA' _) _) (ρ 0).castSucc.castSucc.castSucc (ρ 1).castSucc.castSucc.castSucc
    (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2)) (add (add hc' _) _) (add (add hw' _) _) (add (add ha' _) _)
    (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem range {m} {Γ : Context m} (ρ : Fin 2 → Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0)) (hw : Derives Γ (omega (ρ 0))) :
    Derives Γ (NaturalEvaluationRange.range matrix ρ (ρ 0)) := by
  simp only [NaturalEvaluationRange.range, matrix_rel, paramsUp]
  apply Derives.allI
  apply Derives.allI
  let Δ := Context.image Formula.raise (Context.image Formula.raise Γ)
  have he' : Derives Δ (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc he)
  have hw' : Derives Δ (omega (ρ 0).castSucc.castSucc) := by
    simpa only [Formula.raise, omega_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hw)
  apply Derives.impI
  exact range_point (ρ 0).castSucc.castSucc (ρ 1).castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) (add he' _) (add hw' _) (.hyp (Or.inl rfl))
end PPAC.Migration.Internal.NaturalMultiplicationStep
