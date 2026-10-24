import PPAC.Migration.Internal.AbstractVariableIndex

/-! 待编译：独立mode2变量数值规格，仅使用成员／相等／后继／变量码。 -/
namespace PPAC.Migration.Internal.InstantiateVariableValueSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax
open SyntaxRenameQuerySyntax (of_eq)

def boundTail {m} (w depth idx y : Fin m) : Formula m := .ex
  ((successor idx.castSucc (Fin.last m)).conj ((Formula.mem depth.castSucc idx.castSucc).conj
    (SyntaxVariableSyntax.code true w.castSucc (Fin.last m) y.castSucc)))

def boundValue {m} (w depth P idx x y : Fin m) : Formula m :=
  ((Formula.mem idx depth).conj (.equal y x)).disj
    (((Formula.equal idx depth).conj (.equal y P)).disj (boundTail w depth idx y))

def valueSpec {m} (bound : Bool) (w depth P idx x y : Fin m) : Formula m :=
  if bound then boundValue w depth P idx x y else .equal y x

theorem boundTail_rename {m l} (w depth idx y : Fin m) (ρ : Fin m → Fin l) :
    (boundTail w depth idx y).rename ρ = boundTail (ρ w) (ρ depth) (ρ idx) (ρ y) := by
  simp only [boundTail, Formula.rename, successor_rename, SyntaxVariableSyntax.code_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem boundValue_rename {m l} (w depth P idx x y : Fin m) (ρ : Fin m → Fin l) :
    (boundValue w depth P idx x y).rename ρ = boundValue (ρ w) (ρ depth) (ρ P) (ρ idx) (ρ x) (ρ y) := by
  simp only [boundValue, Formula.rename, boundTail_rename]

theorem valueSpec_rename {m l} (bound : Bool) (w depth P idx x y : Fin m) (ρ : Fin m → Fin l) :
    (valueSpec bound w depth P idx x y).rename ρ = valueSpec bound (ρ w) (ρ depth) (ρ P) (ρ idx) (ρ x) (ρ y) := by
  cases bound <;> simp only [valueSpec, Bool.false_eq_true, ite_false, ite_true, Formula.rename, boundValue_rename]

theorem intro_boundTail {m} {Γ : Context m} (w depth idx y k : Fin m)
    (hs : Derives Γ (successor idx k)) (hd : Derives Γ (.mem depth idx))
    (hy : Derives Γ (SyntaxVariableSyntax.code true w k y)) : Derives Γ (boundTail w depth idx y) := by
  apply Derives.exI k
  simpa only [boundTail, Formula.instantiate, Formula.rename, successor_rename, SyntaxVariableSyntax.code_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.conjI hs (.conjI hd hy)

theorem tail_output_natural {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w depth idx y : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (boundTail w depth idx y)) : Derives Γ (.mem y w) := by
  let B := (successor idx.castSucc (Fin.last m)).conj ((Formula.mem depth.castSucc idx.castSucc).conj
    (SyntaxVariableSyntax.code true w.castSucc (Fin.last m) y.castSucc))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) ht
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  exact HornVariableValue.code_natural (ZFContext.under hZ B) true _ _ _ hw1 (.conjR (.conjR hB))

end PPAC.Migration.Internal.InstantiateVariableValueSyntax
