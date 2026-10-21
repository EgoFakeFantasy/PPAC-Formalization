import PPAC.Migration.GlobalMinimal
import PPAC.Migration.ObjectOrdinalComparison

/-! 任意有限参数公式的最小序数模式；外部模式索引不替换成内部统一真值。 -/
namespace PPAC.Migration.OrdinalLeastSyntax
open Source SourceAlgebra SourceLogic OrdinalSyntax RestrictionSyntax
open MinimalPredicates (pred pred_rename)
open ReplacementPredicates (paramsUp)

def property {n m} (p : Formula (n+1)) (ρ : Fin n → Fin m) (a : Fin m) : Formula m :=
  (ordinal a).conj (pred p ρ a)

def matrix {n} (p : Formula (n+1)) : Formula (n+1) := property p Fin.castSucc (Fin.last n)

def has {n m} (p : Formula (n+1)) (ρ : Fin n → Fin m) : Formula m := .ex
  (property p (paramsUp ρ) (Fin.last m))

def least {n m} (p : Formula (n+1)) (ρ : Fin n → Fin m) (a : Fin m) : Formula m :=
  (property p ρ a).conj (.all ((property p (paramsUp ρ) (Fin.last m)).imp
    ((Formula.equal a.castSucc (Fin.last m)).disj (.mem a.castSucc (Fin.last m)))))

def leastExists {n m} (p : Formula (n+1)) (ρ : Fin n → Fin m) : Formula m := .ex
  (least p (paramsUp ρ) (Fin.last m))

def uniqueLeast {n m} (p : Formula (n+1)) (ρ : Fin n → Fin m) (a : Fin m) : Formula m := .all
  ((least p (paramsUp ρ) (Fin.last m)).imp (.equal (Fin.last m) a.castSucc))

def fiber {n m} (p : Formula (n+1)) (ρ : Fin n → Fin m) : Formula m := .ex
  ((least p (paramsUp ρ) (Fin.last m)).conj (uniqueLeast p (paramsUp ρ) (Fin.last m)))

theorem property_rename {n m k} (p : Formula (n+1)) (ρ : Fin n → Fin m) (a : Fin m) (r : Fin m → Fin k) :
    (property p ρ a).rename r = property p (fun i => r (ρ i)) (r a) := by
  simp only [property, Formula.rename, ordinal_rename, pred_rename]

theorem has_rename {n m k} (p : Formula (n+1)) (ρ : Fin n → Fin m) (r : Fin m → Fin k) :
    (has p ρ).rename r = has p (fun i => r (ρ i)) := by
  simp only [has, Formula.rename, property_rename, paramsUp, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem least_rename {n m k} (p : Formula (n+1)) (ρ : Fin n → Fin m) (a : Fin m) (r : Fin m → Fin k) :
    (least p ρ a).rename r = least p (fun i => r (ρ i)) (r a) := by
  simp only [least, Formula.rename, property_rename, paramsUp, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem leastExists_rename {n m k} (p : Formula (n+1)) (ρ : Fin n → Fin m) (r : Fin m → Fin k) :
    (leastExists p ρ).rename r = leastExists p (fun i => r (ρ i)) := by
  simp only [leastExists, Formula.rename, least_rename, paramsUp, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem uniqueLeast_rename {n m k} (p : Formula (n+1)) (ρ : Fin n → Fin m) (a : Fin m) (r : Fin m → Fin k) :
    (uniqueLeast p ρ a).rename r = uniqueLeast p (fun i => r (ρ i)) (r a) := by
  simp only [uniqueLeast, Formula.rename, least_rename, paramsUp, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem fiber_rename {n m k} (p : Formula (n+1)) (ρ : Fin n → Fin m) (r : Fin m → Fin k) :
    (fiber p ρ).rename r = fiber p (fun i => r (ρ i)) := by
  simp only [fiber, Formula.rename, least_rename, uniqueLeast_rename, paramsUp, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem matrix_pred {n m} (p : Formula (n+1)) (ρ : Fin n → Fin m) (a : Fin m) :
    pred (matrix p) ρ a = property p ρ a := by
  simp only [pred, matrix, property_rename, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem least_at {n m} {Γ : Context m} (p : Formula (n+1)) (ρ : Fin n → Fin m) (a b : Fin m)
    (hl : Derives Γ (least p ρ a)) :
    Derives Γ ((property p ρ b).imp ((Formula.equal a b).disj (.mem a b))) := by
  have hi := Derives.allE b (.conjR hl)
  simpa only [Formula.instantiate, Formula.rename, property_rename, paramsUp,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi
end PPAC.Migration.OrdinalLeastSyntax
