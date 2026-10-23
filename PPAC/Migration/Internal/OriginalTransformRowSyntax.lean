import PPAC.Migration.Internal.ObjectOriginalTermProgram
import PPAC.Migration.Internal.OriginalArgumentsTraceRules

/-! 原项／参数／公式的五字段数值行接口；kind为固定语法索引，其余值均内部。 -/
namespace PPAC.Migration.Internal.OriginalTransformRowSyntax
open Source SourceAlgebra SourceLogic
open SyntaxRenameQuerySyntax (of_eq)

def row {m} (kind : Nat) (w mode depth parameter input output r : Fin m) : Formula m :=
  SyntaxNodeSyntax.constructor 5 kind w (HornRowFields.five mode depth parameter input output) r

def run {m} (kind : Nat) (w mode depth parameter input output : Fin m) : Formula m := .ex
  ((row kind w.castSucc mode.castSucc depth.castSucc parameter.castSucc input.castSucc output.castSucc (Fin.last m)).conj
    (HornLookupConditionSyntax.condition w.castSucc (Fin.last m)))

theorem row_rename {m k} (kind : Nat) (w mode depth parameter input output r : Fin m) (ρ : Fin m → Fin k) :
    (row kind w mode depth parameter input output r).rename ρ = row kind (ρ w) (ρ mode) (ρ depth) (ρ parameter) (ρ input) (ρ output) (ρ r) := by
  simp only [row, SyntaxNodeSyntax.constructor_rename, FreeWeakenResultSyntax.five_map]

theorem run_rename {m k} (kind : Nat) (w mode depth parameter input output : Fin m) (ρ : Fin m → Fin k) :
    (run kind w mode depth parameter input output).rename ρ = run kind (ρ w) (ρ mode) (ρ depth) (ρ parameter) (ρ input) (ρ output) := by
  simp only [run, Formula.rename, row_rename, HornLookupConditionSyntax.condition_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_run {m} {Γ : Context m} (kind : Nat) (w mode depth parameter input output r : Fin m)
    (hr : Derives Γ (row kind w mode depth parameter input output r))
    (ht : Derives Γ (HornLookupConditionSyntax.condition w r)) : Derives Γ (run kind w mode depth parameter input output) := by
  apply Derives.exI r
  exact of_eq (by simp only [Formula.instantiate, Formula.rename, row_rename, HornLookupConditionSyntax.condition_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hr ht)

end PPAC.Migration.Internal.OriginalTransformRowSyntax
