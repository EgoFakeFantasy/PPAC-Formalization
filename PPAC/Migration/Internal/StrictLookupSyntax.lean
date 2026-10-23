import PPAC.Migration.Internal.FreeSubstProgramBinder

/-! 严格原查表程序：实际tail递归求值后必须匹配Cons，不能把默认零投影当作成功。 -/
namespace PPAC.Migration.Internal.StrictLookupSyntax
open Source SourceAlgebra SourceLogic StructuralListProjectionSyntax
open SyntaxRenameQuerySyntax (of_eq)

def body {m} (w n i y : Fin m) : Formula (m+1) :=
  (iteration false w.castSucc n.castSucc i.castSucc (Fin.last m)).conj
    (selected true w.castSucc (Fin.last m) y.castSucc)

def returned {m} (w n i y : Fin m) : Formula m := .ex (body w n i y)

def hasOutput {m} (w n i : Fin m) : Formula m := .ex
  (returned w.castSucc n.castSucc i.castSucc (Fin.last m))

def rejected {m} (w n i : Fin m) : Formula m := (hasOutput w n i).neg

def checked {m} (w n i y : Fin m) : Formula m :=
  ((Formula.mem n w).conj (.mem i w)).conj (returned w n i y)

theorem returned_rename {m k} (w n i y : Fin m) (ρ : Fin m → Fin k) :
    (returned w n i y).rename ρ = returned (ρ w) (ρ n) (ρ i) (ρ y) := by
  simp only [returned, body, Formula.rename, iteration_rename, selected_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem hasOutput_rename {m k} (w n i : Fin m) (ρ : Fin m → Fin k) :
    (hasOutput w n i).rename ρ = hasOutput (ρ w) (ρ n) (ρ i) := by
  simp only [hasOutput, Formula.rename, returned_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem rejected_rename {m k} (w n i : Fin m) (ρ : Fin m → Fin k) :
    (rejected w n i).rename ρ = rejected (ρ w) (ρ n) (ρ i) := by
  simp only [rejected, Formula.neg, Formula.rename, hasOutput_rename]

theorem checked_rename {m k} (w n i y : Fin m) (ρ : Fin m → Fin k) :
    (checked w n i y).rename ρ = checked (ρ w) (ρ n) (ρ i) (ρ y) := by
  simp only [checked, Formula.rename, returned_rename]

theorem intro_returned {m} {Γ : Context m} (w n i y t : Fin m)
    (ht : Derives Γ (iteration false w n i t)) (hy : Derives Γ (selected true w t y)) :
    Derives Γ (returned w n i y) := by
  apply Derives.exI t
  exact of_eq (by simp only [body, Formula.instantiate, Formula.rename, iteration_rename, selected_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI ht hy)

theorem intro_hasOutput {m} {Γ : Context m} (w n i y : Fin m) (hy : Derives Γ (returned w n i y)) :
    Derives Γ (hasOutput w n i) := by
  apply Derives.exI y
  exact of_eq (by simp only [Formula.instantiate, returned_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hy

theorem selected_input_subst {m} {Γ : Context m} (head : Bool) (w n t y : Fin m)
    (he : Derives Γ (.equal n t)) (hy : Derives Γ (selected head w n y)) :
    Derives Γ (selected head w t y) := by
  let P := selected head w.castSucc (Fin.last m) y.castSucc
  have e0 : P.instantiate n = selected head w n y := by
    simp only [P, Formula.instantiate, selected_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have e1 : P.instantiate t = selected head w t y := by
    simp only [P, Formula.instantiate, selected_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq e1 (Derives.eqSubst P he (of_eq e0.symm hy))

end PPAC.Migration.Internal.StrictLookupSyntax
