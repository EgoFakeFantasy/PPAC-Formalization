import PPAC.Migration.Internal.SyntaxUnaryIterationStep

/-! Arbitrary internal iteration count; the entire recursion trace is object-existential. -/
namespace PPAC.Migration.Internal.SyntaxUnaryIterationSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

def params {m} (w : Fin m) : Fin 1 → Fin m := fun _ => w

def iterate {m} (tag : Nat) (w a n y : Fin m) : Formula m :=
  NaturalEvaluationSyntax.evaluation (SyntaxUnaryIterationStep.matrix tag) (params w) w a n y

def existsIteration {m} (tag : Nat) (w a n : Fin m) : Formula m := .ex
  ((Formula.mem (Fin.last m) w.castSucc).conj (iterate tag w.castSucc a.castSucc n.castSucc (Fin.last m)))

def fiber {m} (tag : Nat) (w a n : Fin m) : Formula m := .ex
  (((Formula.mem (Fin.last m) w.castSucc).conj (iterate tag w.castSucc a.castSucc n.castSucc (Fin.last m))).conj
    (.all ((iterate tag w.castSucc.castSucc a.castSucc.castSucc n.castSucc.castSucc (Fin.last (m+1))).imp
      (.equal (Fin.last (m+1)) (Fin.last m).castSucc))))

def forallClosure {m} (w a n y : Fin m) : Formula m := iterate 9 w a n y

theorem iterate_rename {m l} (tag : Nat) (w a n y : Fin m) (ρ : Fin m → Fin l) :
    (iterate tag w a n y).rename ρ = iterate tag (ρ w) (ρ a) (ρ n) (ρ y) := by
  simp only [iterate, NaturalEvaluationSyntax.evaluation_rename]
  rfl

theorem existsIteration_rename {m l} (tag : Nat) (w a n : Fin m) (ρ : Fin m → Fin l) :
    (existsIteration tag w a n).rename ρ = existsIteration tag (ρ w) (ρ a) (ρ n) := by
  simp only [existsIteration, Formula.rename, iterate_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem fiber_rename {m l} (tag : Nat) (w a n : Fin m) (ρ : Fin m → Fin l) :
    (fiber tag w a n).rename ρ = fiber tag (ρ w) (ρ a) (ρ n) := by
  simp only [fiber, Formula.rename, iterate_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem forallClosure_rename {m l} (w a n y : Fin m) (ρ : Fin m → Fin l) :
    (forallClosure w a n y).rename ρ = forallClosure (ρ w) (ρ a) (ρ n) (ρ y) := iterate_rename 9 w a n y ρ

theorem output_subst {m} {Γ : Context m} (tag : Nat) (w a n y z : Fin m)
    (he : Derives Γ (.equal y z)) (hy : Derives Γ (iterate tag w a n y)) : Derives Γ (iterate tag w a n z) := by
  let P := iterate tag w.castSucc a.castSucc n.castSucc (Fin.last m)
  have h0 : P.instantiate y = iterate tag w a n y := by simp only [P, Formula.instantiate, iterate_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have h1 : P.instantiate z = iterate tag w a n z := by simp only [P, Formula.instantiate, iterate_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hy))

theorem intro_exists {m} {Γ : Context m} (tag : Nat) (w a n y : Fin m)
    (hn : Derives Γ (.mem y w)) (hy : Derives Γ (iterate tag w a n y)) : Derives Γ (existsIteration tag w a n) := by
  apply Derives.exI y
  exact of_eq (by simp only [Formula.instantiate, Formula.rename, iterate_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hn hy)

end PPAC.Migration.Internal.SyntaxUnaryIterationSyntax
