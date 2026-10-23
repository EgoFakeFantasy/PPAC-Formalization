import PPAC.Migration.Internal.HornVariableValue

/-! 自由变量后继值的纯对象图；后继和变量码均由实际内部见证表示。 -/
namespace PPAC.Migration.Internal.FreeWeakenValueSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax
open SyntaxRenameQuerySyntax (of_eq)

def shifted {m} (w idx y : Fin m) : Formula m := .ex
  ((successor (Fin.last m) idx.castSucc).conj (SyntaxVariableSyntax.code false w.castSucc (Fin.last m) y.castSucc))

def hasShifted {m} (w idx : Fin m) : Formula m := .ex (shifted w.castSucc idx.castSucc (Fin.last m))

theorem shifted_rename {m k} (w idx y : Fin m) (ρ : Fin m → Fin k) :
    (shifted w idx y).rename ρ = shifted (ρ w) (ρ idx) (ρ y) := by
  simp only [shifted, Formula.rename, successor_rename, SyntaxVariableSyntax.code_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem hasShifted_rename {m k} (w idx : Fin m) (ρ : Fin m → Fin k) :
    (hasShifted w idx).rename ρ = hasShifted (ρ w) (ρ idx) := by
  simp only [hasShifted, Formula.rename, shifted_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_shifted {m} {Γ : Context m} (w idx y s : Fin m) (hs : Derives Γ (successor s idx))
    (hc : Derives Γ (SyntaxVariableSyntax.code false w s y)) : Derives Γ (shifted w idx y) := by
  apply Derives.exI s
  exact of_eq (by simp only [Formula.instantiate, Formula.rename, successor_rename, SyntaxVariableSyntax.code_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hs hc)

theorem successor_input_subst {m} {Γ : Context m} (s i j : Fin m) (he : Derives Γ (.equal i j))
    (hs : Derives Γ (successor s i)) : Derives Γ (successor s j) := by
  let P := successor s.castSucc (Fin.last m)
  have h0 : P.instantiate i = successor s i := by simp only [P, Formula.instantiate, successor_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have h1 : P.instantiate j = successor s j := by simp only [P, Formula.instantiate, successor_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hs))

theorem code_index_subst {m} {Γ : Context m} (w i j y : Fin m) (he : Derives Γ (.equal i j))
    (hc : Derives Γ (SyntaxVariableSyntax.code false w i y)) : Derives Γ (SyntaxVariableSyntax.code false w j y) := by
  let P := SyntaxVariableSyntax.code false w.castSucc (Fin.last m) y.castSucc
  have h0 : P.instantiate i = SyntaxVariableSyntax.code false w i y := by simp only [P, Formula.instantiate, SyntaxVariableSyntax.code_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have h1 : P.instantiate j = SyntaxVariableSyntax.code false w j y := by simp only [P, Formula.instantiate, SyntaxVariableSyntax.code_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hc))

end PPAC.Migration.Internal.FreeWeakenValueSyntax
