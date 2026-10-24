import PPAC.Migration.Internal.AbstractVariableIndex

/-! 原mode1变量输出的独立内部数值关系，只有成员／后继／变量码，没有原接受器或轨迹预言机。 -/
namespace PPAC.Migration.Internal.AbstractVariableValueSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax
open SyntaxRenameQuerySyntax (of_eq)

def boundShifted {m} (w depth idx y : Fin m) : Formula m := .ex
  ((successor (Fin.last m) idx.castSucc).conj ((Formula.mem depth.castSucc (Fin.last m)).conj
    (SyntaxVariableSyntax.code true w.castSucc (Fin.last m) y.castSucc)))

def boundValue {m} (w depth idx x y : Fin m) : Formula m :=
  ((Formula.mem idx depth).conj (.equal y x)).disj (boundShifted w depth idx y)

def freeTail {m} (w idx y : Fin m) : Formula m := .ex
  ((successor idx.castSucc (Fin.last m)).conj (SyntaxVariableSyntax.code false w.castSucc (Fin.last m) y.castSucc))

def freeValue {m} (w depth idx y : Fin m) : Formula m :=
  ((empty idx).conj (SyntaxVariableSyntax.code true w depth y)).disj (freeTail w idx y)

def valueSpec {m} (bound : Bool) (w depth idx x y : Fin m) : Formula m :=
  if bound then boundValue w depth idx x y else freeValue w depth idx y

theorem valueSpec_rename {m l} (bound : Bool) (w d i x y : Fin m) (ρ : Fin m → Fin l) :
    (valueSpec bound w d i x y).rename ρ = valueSpec bound (ρ w) (ρ d) (ρ i) (ρ x) (ρ y) := by
  cases bound <;> simp only [valueSpec, Bool.false_eq_true, ite_false, ite_true, boundValue, boundShifted, freeValue, freeTail,
    Formula.rename, empty_rename, successor_rename, SyntaxVariableSyntax.code_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem boundShifted_rename {m l} (w d i y : Fin m) (ρ : Fin m → Fin l) :
    (boundShifted w d i y).rename ρ = boundShifted (ρ w) (ρ d) (ρ i) (ρ y) := by
  simp only [boundShifted, Formula.rename, successor_rename, SyntaxVariableSyntax.code_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem boundValue_rename {m l} (w d i x y : Fin m) (ρ : Fin m → Fin l) :
    (boundValue w d i x y).rename ρ = boundValue (ρ w) (ρ d) (ρ i) (ρ x) (ρ y) := by
  simp only [boundValue, Formula.rename, boundShifted_rename]

theorem freeTail_rename {m l} (w i y : Fin m) (ρ : Fin m → Fin l) :
    (freeTail w i y).rename ρ = freeTail (ρ w) (ρ i) (ρ y) := by
  simp only [freeTail, Formula.rename, successor_rename, SyntaxVariableSyntax.code_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem freeValue_rename {m l} (w d i y : Fin m) (ρ : Fin m → Fin l) :
    (freeValue w d i y).rename ρ = freeValue (ρ w) (ρ d) (ρ i) (ρ y) := by
  simp only [freeValue, Formula.rename, empty_rename, SyntaxVariableSyntax.code_rename, freeTail_rename]

theorem intro_boundShifted {m} {Γ : Context m} (w d i y s : Fin m)
    (hs : Derives Γ (successor s i)) (hd : Derives Γ (.mem d s)) (hy : Derives Γ (SyntaxVariableSyntax.code true w s y)) :
    Derives Γ (boundShifted w d i y) := by
  apply Derives.exI s
  simpa only [Formula.instantiate, Formula.rename, successor_rename, SyntaxVariableSyntax.code_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.conjI hs (.conjI hd hy)

theorem intro_freeTail {m} {Γ : Context m} (w i y k : Fin m)
    (hs : Derives Γ (successor i k)) (hy : Derives Γ (SyntaxVariableSyntax.code false w k y)) :
    Derives Γ (freeTail w i y) := by
  apply Derives.exI k
  simpa only [Formula.instantiate, Formula.rename, successor_rename, SyntaxVariableSyntax.code_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.conjI hs hy

end PPAC.Migration.Internal.AbstractVariableValueSyntax
