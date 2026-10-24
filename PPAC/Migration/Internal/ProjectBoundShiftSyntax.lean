import PPAC.Migration.Internal.ObjectSchemaIndex

/-! Internal bound-term shift used by the original Project subset expansion. -/
namespace PPAC.Migration.Internal.ProjectBoundShiftSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)

def matrix {m} (w x y i j : Fin m) : Formula m :=
  (SyntaxVariableSyntax.code true w i x).conj ((successor j i).conj (SyntaxVariableSyntax.code true w j y))

def body {m} (w x y : Fin m) : Formula (m+2) :=
  matrix (old 2 w) (old 2 x) (old 2 y) (slot 2 0) (slot 2 1)

def shifted {m} (w x y : Fin m) : Formula m := existsMany 2 (body w x y)

def existsOutput {m} (w x : Fin m) : Formula m := .ex
  ((Formula.mem (Fin.last m) w.castSucc).conj (shifted w.castSucc x.castSucc (Fin.last m)))

def uniqueOutput {m} (w x y : Fin m) : Formula m := .all
  ((shifted w.castSucc x.castSucc (Fin.last m)).imp (.equal (Fin.last m) y.castSucc))

def fiber {m} (w x : Fin m) : Formula m := .ex
  (((Formula.mem (Fin.last m) w.castSucc).conj (shifted w.castSucc x.castSucc (Fin.last m))).conj
    (uniqueOutput w.castSucc x.castSucc (Fin.last m)))

theorem matrix_rename {m l} (w x y i j : Fin m) (ρ : Fin m → Fin l) :
    (matrix w x y i j).rename ρ = matrix (ρ w) (ρ x) (ρ y) (ρ i) (ρ j) := by
  simp only [matrix, Formula.rename, SyntaxVariableSyntax.code_rename, successor_rename]

theorem body_lift {m l} (w x y : Fin m) (ρ : Fin m → Fin l) :
    (body w x y).rename (lift 2 ρ) = body (ρ w) (ρ x) (ρ y) := by
  simp only [body, matrix_rename, lift_old, lift_slot]

theorem shifted_rename {m l} (w x y : Fin m) (ρ : Fin m → Fin l) :
    (shifted w x y).rename ρ = shifted (ρ w) (ρ x) (ρ y) := by
  simp only [shifted, existsMany_rename, body_lift]

theorem existsOutput_rename {m l} (w x : Fin m) (ρ : Fin m → Fin l) :
    (existsOutput w x).rename ρ = existsOutput (ρ w) (ρ x) := by
  simp only [existsOutput, Formula.rename, shifted_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem uniqueOutput_rename {m l} (w x y : Fin m) (ρ : Fin m → Fin l) :
    (uniqueOutput w x y).rename ρ = uniqueOutput (ρ w) (ρ x) (ρ y) := by
  simp only [uniqueOutput, Formula.rename, shifted_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem fiber_rename {m l} (w x : Fin m) (ρ : Fin m → Fin l) :
    (fiber w x).rename ρ = fiber (ρ w) (ρ x) := by
  simp only [fiber, Formula.rename, shifted_rename, uniqueOutput_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_shifted {m} {Γ : Context m} (w x y i j : Fin m) (hm : Derives Γ (matrix w x y i j)) :
    Derives Γ (shifted w x y) := by
  apply HornBinderRules.intro_many 2 (body w x y) (SyntaxAtomSyntax.two i j)
  exact of_eq (by simp only [body, matrix_rename, assign_old, assign_slot]; rfl) hm

theorem intro_exists {m} {Γ : Context m} (w x y : Fin m) (hy : Derives Γ (.mem y w))
    (hs : Derives Γ (shifted w x y)) : Derives Γ (existsOutput w x) := by
  apply Derives.exI y
  exact of_eq (by simp only [Formula.instantiate, Formula.rename, shifted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hy hs)

end PPAC.Migration.Internal.ProjectBoundShiftSyntax
