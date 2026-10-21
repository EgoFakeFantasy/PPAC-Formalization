import PPAC.Migration.ObjectOrdinalRecursion

/-! 递推算子在全部有效内部序数/前段图上的对象总性及其实际输出。 -/
namespace PPAC.Migration.OrdinalRecursionTotal
open Source SourceAlgebra SourceLogic GraphSyntax OrdinalSyntax OrdinalRecursionSyntax
open ReplacementPredicates (paramsUp)

def hasValue {n m} (p : Formula (n+3)) (ρ : Fin n → Fin m) (x h : Fin m) : Formula m := .ex
  (operator p (paramsUp ρ) x.castSucc h.castSucc (Fin.last m))

def total {n m} (p : Formula (n+3)) (ρ : Fin n → Fin m) : Formula m := .all (.all
  (((ordinal (Fin.last m).castSucc).conj (functionOn (Fin.last (m+1)) (Fin.last m).castSucc)).imp
    (hasValue p (paramsUp (paramsUp ρ)) (Fin.last m).castSucc (Fin.last (m+1)))))

theorem hasValue_rename {n m k} (p : Formula (n+3)) (ρ : Fin n → Fin m) (x h : Fin m) (r : Fin m → Fin k) :
    (hasValue p ρ x h).rename r = hasValue p (fun i => r (ρ i)) (r x) (r h) := by
  simp only [hasValue, Formula.rename, operator_rename, paramsUp,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem total_rename {n m k} (p : Formula (n+3)) (ρ : Fin n → Fin m) (r : Fin m → Fin k) :
    (total p ρ).rename r = total p (fun i => r (ρ i)) := by
  simp only [total, Formula.rename, ordinal_rename, functionOn_rename, hasValue_rename, paramsUp,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem total_at {n m} {Γ : Context m} (p : Formula (n+3)) (ρ : Fin n → Fin m) (x h : Fin m)
    (ht : Derives Γ (total p ρ)) : Derives Γ (((ordinal x).conj (functionOn h x)).imp (hasValue p ρ x h)) := by
  have hi := Derives.allE h (Derives.allE x ht)
  simpa only [Formula.instantiate, Formula.rename, ordinal_rename, functionOn_rename, hasValue_rename, paramsUp,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi

theorem evaluate {n m} {Γ : Context m} (p : Formula (n+3)) (ρ : Fin n → Fin m) (d f : Fin m)
    (ht : Derives Γ (total p ρ)) (hd : Derives Γ (ordinal d)) (hf : Derives Γ (recursor p ρ f d)) :
    Derives Γ (hasValue p ρ d f) := .impE (total_at p ρ d f ht) (.conjI hd (.conjL hf))
end PPAC.Migration.OrdinalRecursionTotal
