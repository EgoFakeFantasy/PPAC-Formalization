import PPAC.Migration.Internal.AbstractVariableRun

/-! 纯成员语言全部项的内部mode1数值关系；仅两个变量分支，保持真实索引作用域。 -/
namespace PPAC.Migration.Internal.AbstractTermValueSyntax
open Source SourceAlgebra SourceLogic
open SyntaxRenameQuerySyntax (of_eq)

def branch {m} (bound : Bool) (w limit depth n q : Fin m) : Formula m := .ex
  ((Formula.mem (Fin.last m) limit.castSucc).conj
    ((SyntaxVariableSyntax.code bound w.castSucc (Fin.last m) n.castSucc).conj
      (AbstractVariableValueSyntax.valueSpec bound w.castSucc depth.castSucc (Fin.last m) n.castSucc q.castSucc)))

def value {m} (w a b depth n q : Fin m) : Formula m :=
  (SyntaxTermSyntax.contexts w a b).conj ((branch true w a depth n q).disj (branch false w b depth n q))

theorem branch_rename {m l} (bound : Bool) (w limit depth n q : Fin m) (ρ : Fin m → Fin l) :
    (branch bound w limit depth n q).rename ρ = branch bound (ρ w) (ρ limit) (ρ depth) (ρ n) (ρ q) := by
  simp only [branch, Formula.rename, SyntaxVariableSyntax.code_rename, AbstractVariableValueSyntax.valueSpec_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem value_rename {m l} (w a b depth n q : Fin m) (ρ : Fin m → Fin l) :
    (value w a b depth n q).rename ρ = value (ρ w) (ρ a) (ρ b) (ρ depth) (ρ n) (ρ q) := by
  simp only [value, Formula.rename, SyntaxTermSyntax.contexts_rename, branch_rename]

theorem intro_branch {m} {Γ : Context m} (bound : Bool) (w limit depth n q i : Fin m)
    (hi : Derives Γ (.mem i limit)) (hv : Derives Γ (SyntaxVariableSyntax.code bound w i n))
    (hval : Derives Γ (AbstractVariableValueSyntax.valueSpec bound w depth i n q)) :
    Derives Γ (branch bound w limit depth n q) := by
  apply Derives.exI i
  simpa only [Formula.instantiate, Formula.rename, SyntaxVariableSyntax.code_rename, AbstractVariableValueSyntax.valueSpec_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.conjI hi (.conjI hv hval)

end PPAC.Migration.Internal.AbstractTermValueSyntax
