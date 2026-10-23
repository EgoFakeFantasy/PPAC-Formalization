import PPAC.Migration.Internal.OriginalScalarValues

/-! 原kind1行及完整原轨迹的纯签名项执行接口；不以项程序或变量规格为定义。 -/
namespace PPAC.Migration.Internal.OriginalTermTraceSyntax
open Source SourceAlgebra SourceLogic
open SyntaxRenameQuerySyntax (of_eq)

def root {m} (three : Bool) (w depth parameter input output row : Fin m) : Formula m := .ex
  ((SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) (Fin.last m)).conj
    (SyntaxNodeSyntax.constructor 5 1 w.castSucc (HornRowFields.five (Fin.last m) depth.castSucc parameter.castSucc input.castSucc output.castSucc) row.castSucc))

def existsRoot {m} (three : Bool) (w depth parameter input output : Fin m) : Formula m := .ex
  ((Formula.mem (Fin.last m) w.castSucc).conj (root three w.castSucc depth.castSucc parameter.castSucc input.castSucc output.castSucc (Fin.last m)))

def run {m} (three : Bool) (w depth parameter input output : Fin m) : Formula m := .ex
  ((root three w.castSucc depth.castSucc parameter.castSucc input.castSucc output.castSucc (Fin.last m)).conj (HornLookupConditionSyntax.condition w.castSucc (Fin.last m)))

def metadata {m} (w depth parameter : Fin m) : Formula m := (Formula.mem depth w).conj (.mem parameter w)

def inputGuard {m} (w depth parameter a b input : Fin m) : Formula m :=
  (metadata w depth parameter).conj (SyntaxTermSyntax.term w a b input)

def checked {m} (three : Bool) (w depth parameter a b input output : Fin m) : Formula m :=
  (inputGuard w depth parameter a b input).conj (run three w depth parameter input output)

theorem root_rename {m k} (three : Bool) (w depth parameter input output row : Fin m) (ρ : Fin m → Fin k) :
    (root three w depth parameter input output row).rename ρ = root three (ρ w) (ρ depth) (ρ parameter) (ρ input) (ρ output) (ρ row) := by
  simp only [root, Formula.rename, SyntaxNumeralSyntax.numeral_rename, SyntaxNodeSyntax.constructor_rename, FreeWeakenResultSyntax.five_map,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem existsRoot_rename {m k} (three : Bool) (w depth parameter input output : Fin m) (ρ : Fin m → Fin k) :
    (existsRoot three w depth parameter input output).rename ρ = existsRoot three (ρ w) (ρ depth) (ρ parameter) (ρ input) (ρ output) := by
  simp only [existsRoot, Formula.rename, root_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem run_rename {m k} (three : Bool) (w depth parameter input output : Fin m) (ρ : Fin m → Fin k) :
    (run three w depth parameter input output).rename ρ = run three (ρ w) (ρ depth) (ρ parameter) (ρ input) (ρ output) := by
  simp only [run, Formula.rename, root_rename, HornLookupConditionSyntax.condition_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem metadata_rename {m k} (w depth parameter : Fin m) (ρ : Fin m → Fin k) :
    (metadata w depth parameter).rename ρ = metadata (ρ w) (ρ depth) (ρ parameter) := rfl

theorem inputGuard_rename {m k} (w depth parameter a b input : Fin m) (ρ : Fin m → Fin k) :
    (inputGuard w depth parameter a b input).rename ρ = inputGuard (ρ w) (ρ depth) (ρ parameter) (ρ a) (ρ b) (ρ input) := by
  simp only [inputGuard, Formula.rename, metadata_rename, SyntaxTermSyntax.term_rename]

theorem checked_rename {m k} (three : Bool) (w depth parameter a b input output : Fin m) (ρ : Fin m → Fin k) :
    (checked three w depth parameter a b input output).rename ρ = checked three (ρ w) (ρ depth) (ρ parameter) (ρ a) (ρ b) (ρ input) (ρ output) := by
  simp only [checked, Formula.rename, inputGuard_rename, run_rename]

theorem intro_run {m} {Γ : Context m} (three : Bool) (w depth parameter input output row : Fin m)
    (hr : Derives Γ (root three w depth parameter input output row)) (ht : Derives Γ (HornLookupConditionSyntax.condition w row)) :
    Derives Γ (run three w depth parameter input output) := by
  apply Derives.exI row
  exact of_eq (by simp only [Formula.instantiate, Formula.rename, root_rename, HornLookupConditionSyntax.condition_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hr ht)

end PPAC.Migration.Internal.OriginalTermTraceSyntax
