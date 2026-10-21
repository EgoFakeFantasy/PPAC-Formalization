import PPAC.Migration.Internal.NaturalEvaluationStep

/-! ω内取原后继、ω外取零的全定义关系；在自然输入上严格保持原后继，全部输出在ω。 -/
namespace PPAC.Migration.Internal.NaturalSuccessorStep
open Source SourceAlgebra SourceLogic GraphSyntax OmegaSyntax ReplacementPredicates NaturalRecursionSyntax

def step {m} (w x y : Fin m) : Formula m :=
  ((Formula.mem x w).conj (successor y x)).disj ((Formula.mem x w).neg.conj (empty y))
def hasStep {m} (w x : Fin m) : Formula m := .ex (step w.castSucc x.castSucc (Fin.last m))
def matrix : Formula 3 := step 0 1 2

theorem step_rename {m k} (w x y : Fin m) (r : Fin m → Fin k) :
    (step w x y).rename r = step (r w) (r x) (r y) := by
  simp only [step, Formula.rename, Formula.neg, successor_rename, empty_rename]
theorem hasStep_rename {m k} (w x : Fin m) (r : Fin m → Fin k) :
    (hasStep w x).rename r = hasStep (r w) (r x) := by
  simp only [hasStep, Formula.rename, step_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem matrix_rel {m} (ρ : Fin 1 → Fin m) (x y : Fin m) : rel matrix ρ x y = step (ρ 0) x y := by
  have h0 : Fin.lastCases y (Fin.lastCases x ρ) (0 : Fin 3) = ρ 0 := by
    change Fin.lastCases y (Fin.lastCases x ρ) (0 : Fin 1).castSucc.castSucc = ρ 0
    simp only [Fin.lastCases_castSucc]
  have h1 : Fin.lastCases y (Fin.lastCases x ρ) (1 : Fin 3) = x := by
    change Fin.lastCases y (Fin.lastCases x ρ) (Fin.last 1).castSucc = x
    simp only [Fin.lastCases_castSucc, Fin.lastCases_last]
  have h2 : Fin.lastCases y (Fin.lastCases x ρ) (2 : Fin 3) = y := by
    change Fin.lastCases y (Fin.lastCases x ρ) (Fin.last 2) = y
    exact Fin.lastCases_last
  simp only [rel, Source.SetLanguage.relation, matrix, step_rename, h0, h1, h2]

theorem intro_value {m} {Γ : Context m} (w x y : Fin m) (hy : Derives Γ (step w x y)) : Derives Γ (hasStep w x) := by
  apply Derives.exI y
  simpa only [Formula.instantiate, step_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hy

theorem exists_step {m} {Γ : Context m} (w x : Fin m) (hw : Derives Γ (omega w)) : Derives Γ (hasStep w x) := by
  apply SourcePropositional.by_cases (.mem x w) (hasStep w x)
  · let M := Formula.mem x w
    let Γm := Context.add M Γ
    have hs := Derives.impE (add (step_at w x (.conjL hw)) M) (Derives.hyp (Or.inl rfl))
    let Y := (Formula.mem (Fin.last m) w.castSucc).conj (successor (Fin.last m) x.castSucc)
    let Ξ := Context.add Y (Context.image Formula.raise Γm)
    change Derives Γm (.ex Y) at hs
    apply Derives.exE (p := Y) hs
    have hxY : Derives Ξ (.mem x.castSucc w.castSucc) := under (Derives.hyp (Γ := Γm) (Or.inl rfl)) Y
    have hY : Derives Ξ Y := .hyp (Or.inl rfl)
    have hst : Derives Ξ (step w.castSucc x.castSucc (Fin.last m)) := .disjL (.conjI hxY (.conjR hY))
    simpa only [Formula.raise, hasStep_rename] using intro_value w.castSucc x.castSucc (Fin.last m) hst
  · let M := (Formula.mem x w).neg
    let Γm := Context.add M Γ
    have hz : Derives Γm (zeroIn w) := add (.conjL (.conjL hw)) M
    let Z := (Formula.mem (Fin.last m) w.castSucc).conj (empty (Fin.last m))
    let Ξ := Context.add Z (Context.image Formula.raise Γm)
    change Derives Γm (.ex Z) at hz
    apply Derives.exE (p := Z) hz
    have hxZ : Derives Ξ (Formula.mem x.castSucc w.castSucc).neg := under (Derives.hyp (Γ := Γm) (Or.inl rfl)) Z
    have hZ : Derives Ξ Z := .hyp (Or.inl rfl)
    have hst : Derives Ξ (step w.castSucc x.castSucc (Fin.last m)) := .disjR (.conjI hxZ (.conjR hZ))
    simpa only [Formula.raise, hasStep_rename] using intro_value w.castSucc x.castSucc (Fin.last m) hst

theorem functional_point {m} {Γ : Context m} (w x y z : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hy : Derives Γ (step w x y)) (hz : Derives Γ (step w x z)) : Derives Γ (.equal y z) := by
  apply Derives.disjE hy
  · apply Derives.disjE (add hz _)
    · exact OmegaUniversal.successor_unique y z x (add (add he _) _) (.conjR (.hyp (Or.inr (Or.inl rfl)))) (.conjR (.hyp (Or.inl rfl)))
    · exact .botE (.impE (.conjL (.hyp (Or.inl rfl))) (.conjL (.hyp (Or.inr (Or.inl rfl)))))
  · apply Derives.disjE (add hz _)
    · exact .botE (.impE (.conjL (.hyp (Or.inr (Or.inl rfl)))) (.conjL (.hyp (Or.inl rfl))))
    · exact OmegaUniversal.empty_unique y z (add (add he _) _) (.conjR (.hyp (Or.inr (Or.inl rfl)))) (.conjR (.hyp (Or.inl rfl)))

theorem range_point {m} {Γ : Context m} (w x y : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hw : Derives Γ (omega w)) (hy : Derives Γ (step w x y)) : Derives Γ (.mem y w) := by
  apply Derives.disjE hy
  · exact OmegaStructureAlgebra.successor_member w y x (add he _) (add hw _) (.conjL (.hyp (Or.inl rfl))) (.conjR (.hyp (Or.inl rfl)))
  · exact OmegaStructureAlgebra.zero_member w y (add he _) (add hw _) (.conjR (.hyp (Or.inl rfl)))

theorem on_natural {m} {Γ : Context m} (w x y : Fin m) (hx : Derives Γ (.mem x w))
    (hy : Derives Γ (step w x y)) : Derives Γ (successor y x) := by
  apply Derives.disjE hy
  · exact .conjR (.hyp (Or.inl rfl))
  · exact .botE (.impE (.conjL (.hyp (Or.inl rfl))) (add hx _))

theorem total {m} {Γ : Context m} (ρ : Fin 1 → Fin m) (hw : Derives Γ (omega (ρ 0))) : Derives Γ (relationTotal matrix ρ) := by
  simp only [relationTotal, matrix_rel, paramsUp]
  apply Derives.allI
  have hw' : Derives (Context.image Formula.raise Γ) (omega (ρ 0).castSucc) := by
    simpa only [Formula.raise, omega_rename] using Derives.rename Fin.castSucc hw
  exact exists_step (ρ 0).castSucc (Fin.last m) hw'

theorem functional {m} {Γ : Context m} (ρ : Fin 1 → Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0)) : Derives Γ (relationFunctional matrix ρ) := by
  simp only [relationFunctional, matrix_rel, paramsUp]
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  have he' : Derives (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ)))
      (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using OrdinalRestriction.raise_three he
  apply Derives.impI
  apply Derives.impI
  exact functional_point (ρ 0).castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2))
    (add (add he' _) _) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem range {m} {Γ : Context m} (ρ : Fin 1 → Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0)) (hw : Derives Γ (omega (ρ 0))) :
    Derives Γ (NaturalEvaluationRange.range matrix ρ (ρ 0)) := by
  simp only [NaturalEvaluationRange.range, matrix_rel, paramsUp]
  apply Derives.allI
  apply Derives.allI
  have he' : Derives (Context.image Formula.raise (Context.image Formula.raise Γ)) (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc he)
  have hw' : Derives (Context.image Formula.raise (Context.image Formula.raise Γ)) (omega (ρ 0).castSucc.castSucc) := by
    simpa only [Formula.raise, omega_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hw)
  apply Derives.impI
  exact range_point (ρ 0).castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) (add he' _) (add hw' _) (.hyp (Or.inl rfl))
end PPAC.Migration.Internal.NaturalSuccessorStep
