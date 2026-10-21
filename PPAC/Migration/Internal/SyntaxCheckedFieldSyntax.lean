import PPAC.Migration.Internal.SyntaxConstructorSlots

/-! 任意有限纯公式模式检查真实字段值；外部模式保留，不引入内部真值谓词。 -/
namespace PPAC.Migration.Internal.SyntaxCheckedFieldSyntax
open Source SourceAlgebra SourceLogic MinimalPredicates SyntaxSlotSyntax
open ReplacementPredicates (paramsUp)

def checked {n m} (a : Formula (n+1)) (ρ : Fin n → Fin m) (g : Fin m) (j : Nat) : Formula m := .ex
  ((slot g.castSucc j (Fin.last m)).conj (pred a (paramsUp ρ) (Fin.last m)))

theorem checked_rename {n m k} (a : Formula (n+1)) (ρ : Fin n → Fin m) (g : Fin m) (j : Nat) (r : Fin m → Fin k) :
    (checked a ρ g j).rename r = checked a (fun i => r (ρ i)) (r g) j := by
  simp only [checked, Formula.rename, slot_rename, pred_rename, paramsUp,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem pred_subst {n m} {Γ : Context m} (a : Formula (n+1)) (ρ : Fin n → Fin m) (x y : Fin m)
    (he : Derives Γ (.equal x y)) (hp : Derives Γ (pred a ρ x)) : Derives Γ (pred a ρ y) := by
  let Q := pred a (paramsUp ρ) (Fin.last m)
  have hi : Derives Γ (Q.instantiate x) := by
    simpa only [Q, Formula.instantiate, pred_rename, paramsUp, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hp
  have ho := Derives.eqSubst Q he hi
  simpa only [Q, Formula.instantiate, pred_rename, paramsUp, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho

theorem intro_checked {n m} {Γ : Context m} (a : Formula (n+1)) (ρ : Fin n → Fin m) (g : Fin m) (j : Nat) (y : Fin m)
    (hs : Derives Γ (slot g j y)) (hp : Derives Γ (pred a ρ y)) : Derives Γ (checked a ρ g j) := by
  apply Derives.exI y
  simp only [Formula.instantiate, Formula.rename, slot_rename, pred_rename, paramsUp,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI hs hp
end PPAC.Migration.Internal.SyntaxCheckedFieldSyntax
