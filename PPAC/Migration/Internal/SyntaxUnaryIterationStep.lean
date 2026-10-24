import PPAC.Migration.Internal.ObjectFixedAxiomTest

/-! Totalized unary syntax-node step, using an object zero only outside omega. -/
namespace PPAC.Migration.Internal.SyntaxUnaryIterationStep
open Source SourceAlgebra SourceLogic OmegaSyntax ReplacementPredicates NaturalRecursionSyntax
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

def step {m} (tag : Nat) (w x y : Fin m) : Formula m :=
  ((Formula.mem x w).conj (SyntaxNodeSyntax.constructor 1 tag w (fun _ => x) y)).disj
    ((Formula.mem x w).neg.conj (empty y))

def hasStep {m} (tag : Nat) (w x : Fin m) : Formula m := .ex (step tag w.castSucc x.castSucc (Fin.last m))

def matrix (tag : Nat) : Formula 3 := step tag 0 1 2

theorem step_rename {m l} (tag : Nat) (w x y : Fin m) (ρ : Fin m → Fin l) :
    (step tag w x y).rename ρ = step tag (ρ w) (ρ x) (ρ y) := by
  simp only [step, Formula.rename, Formula.neg, SyntaxNodeSyntax.constructor_rename, empty_rename]

theorem hasStep_rename {m l} (tag : Nat) (w x : Fin m) (ρ : Fin m → Fin l) :
    (hasStep tag w x).rename ρ = hasStep tag (ρ w) (ρ x) := by
  simp only [hasStep, Formula.rename, step_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem matrix_rel {m} (tag : Nat) (ρ : Fin 1 → Fin m) (x y : Fin m) :
    rel (matrix tag) ρ x y = step tag (ρ 0) x y := by
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

theorem intro_value {m} {Γ : Context m} (tag : Nat) (w x y : Fin m)
    (hy : Derives Γ (step tag w x y)) : Derives Γ (hasStep tag w x) := by
  apply Derives.exI y
  exact of_eq (by simp only [Formula.instantiate, step_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hy

theorem exists_step {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (w x : Fin m)
    (hw : Derives Γ (omega w)) : Derives Γ (hasStep tag w x) := by
  apply SourcePropositional.by_cases (.mem x w) (hasStep tag w x)
  · let M := Formula.mem x w
    let Δ := Context.add M Γ
    have hs := SyntaxConstructors.exists_constructor (ZFContext.add hZ M) 1 tag w (fun _ => x)
      (add hw M) (.conjI (.hyp (Or.inl rfl)) (.eqRefl w))
    let Y := (Formula.mem (Fin.last m) w.castSucc).conj
      (SyntaxNodeSyntax.constructor 1 tag w.castSucc (fun _ => x.castSucc) (Fin.last m))
    let Ξ := Context.add Y (Context.image Formula.raise Δ)
    apply Derives.exE (p := Y) hs
    have hx : Derives Ξ (.mem x.castSucc w.castSucc) := under (Derives.hyp (Γ := Δ) (Or.inl rfl)) Y
    have hY : Derives Ξ Y := .hyp (Or.inl rfl)
    exact of_eq (by simp only [Formula.raise, hasStep_rename])
      (intro_value tag w.castSucc x.castSucc (Fin.last m) (.disjL (.conjI hx (.conjR hY))))
  · let M := (Formula.mem x w).neg
    let Δ := Context.add M Γ
    let Z := (Formula.mem (Fin.last m) w.castSucc).conj (empty (Fin.last m))
    let Ξ := Context.add Z (Context.image Formula.raise Δ)
    have hz : Derives Δ (.ex Z) := add (.conjL (.conjL hw)) M
    apply Derives.exE (p := Z) hz
    have hx : Derives Ξ (Formula.mem x.castSucc w.castSucc).neg := under (Derives.hyp (Γ := Δ) (Or.inl rfl)) Z
    have hZ : Derives Ξ Z := .hyp (Or.inl rfl)
    exact of_eq (by simp only [Formula.raise, hasStep_rename])
      (intro_value tag w.castSucc x.castSucc (Fin.last m) (.disjR (.conjI hx (.conjR hZ))))

theorem functional_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (w x y z : Fin m)
    (hw : Derives Γ (omega w)) (hy : Derives Γ (step tag w x y)) (hz : Derives Γ (step tag w x z)) : Derives Γ (.equal y z) := by
  apply Derives.disjE hy
  · apply Derives.disjE (add hz _)
    · exact SyntaxConstructors.unique (ZFContext.add (ZFContext.add hZ _) _) 1 tag w (fun _ => x) y z
        (add (add hw _) _) (.conjR (.hyp (Or.inr (Or.inl rfl)))) (.conjR (.hyp (Or.inl rfl)))
    · exact .botE (.impE (.conjL (.hyp (Or.inl rfl))) (.conjL (.hyp (Or.inr (Or.inl rfl)))))
  · apply Derives.disjE (add hz _)
    · exact .botE (.impE (.conjL (.hyp (Or.inr (Or.inl rfl)))) (.conjL (.hyp (Or.inl rfl))))
    · exact OmegaUniversal.empty_unique y z (add (add (ZFContext.arithmetic hZ).base.extensionality _) _)
        (.conjR (.hyp (Or.inr (Or.inl rfl)))) (.conjR (.hyp (Or.inl rfl)))

theorem range_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (w x y : Fin m)
    (hw : Derives Γ (omega w)) (hy : Derives Γ (step tag w x y)) : Derives Γ (.mem y w) := by
  apply Derives.disjE hy
  · exact ProofTreeConstructorFacts.range (ZFContext.add hZ _) 1 tag w y (fun _ => x) (add hw _) (.conjR (.hyp (Or.inl rfl)))
  · exact OmegaStructureAlgebra.zero_member w y (add (ZFContext.arithmetic hZ).base.extensionality _) (add hw _) (.conjR (.hyp (Or.inl rfl)))

theorem on_natural {m} {Γ : Context m} (tag : Nat) (w x y : Fin m) (hx : Derives Γ (.mem x w))
    (hy : Derives Γ (step tag w x y)) : Derives Γ (SyntaxNodeSyntax.constructor 1 tag w (fun _ => x) y) := by
  apply Derives.disjE hy
  · exact .conjR (.hyp (Or.inl rfl))
  · exact .botE (.impE (.conjL (.hyp (Or.inl rfl))) (add hx _))

theorem total {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (ρ : Fin 1 → Fin m)
    (hw : Derives Γ (omega (ρ 0))) : Derives Γ (relationTotal (matrix tag) ρ) := by
  simp only [relationTotal, matrix_rel, paramsUp]
  apply Derives.allI
  exact exists_step (ZFContext.rename hZ Fin.castSucc) tag (ρ 0).castSucc (Fin.last m)
    (of_eq (omega_rename (ρ 0) Fin.castSucc) (Derives.rename Fin.castSucc hw))

theorem functional {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (ρ : Fin 1 → Fin m)
    (hw : Derives Γ (omega (ρ 0))) : Derives Γ (relationFunctional (matrix tag) ρ) := by
  simp only [relationFunctional, matrix_rel, paramsUp]
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  have hZ3 := ZFContext.rename (ZFContext.rename (ZFContext.rename hZ Fin.castSucc) Fin.castSucc) Fin.castSucc
  have hw3 : Derives (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ))) (omega (ρ 0).castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, omega_rename] using OrdinalRestriction.raise_three hw
  apply Derives.impI
  apply Derives.impI
  exact functional_point (ZFContext.add (ZFContext.add hZ3 _) _) tag (ρ 0).castSucc.castSucc.castSucc
    (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2)) (add (add hw3 _) _)
    (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem range {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (ρ : Fin 1 → Fin m)
    (hw : Derives Γ (omega (ρ 0))) : Derives Γ (NaturalEvaluationRange.range (matrix tag) ρ (ρ 0)) := by
  simp only [NaturalEvaluationRange.range, matrix_rel, paramsUp]
  apply Derives.allI
  apply Derives.allI
  have hZ2 := ZFContext.rename (ZFContext.rename hZ Fin.castSucc) Fin.castSucc
  have hw2 : Derives (Context.image Formula.raise (Context.image Formula.raise Γ)) (omega (ρ 0).castSucc.castSucc) := by
    simpa only [Formula.raise, omega_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hw)
  apply Derives.impI
  exact range_point (ZFContext.add hZ2 _) tag (ρ 0).castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
    (add hw2 _) (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.SyntaxUnaryIterationStep
