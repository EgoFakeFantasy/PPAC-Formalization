import PPAC.Migration.OrdinalRecursionRestriction

/-! 任意递推矩阵在原序数索引和完整前段函数图上的对象单值性。 -/
namespace PPAC.Migration.OrdinalRecursionDeterminism
open Source SourceAlgebra SourceLogic GraphSyntax OrdinalSyntax OrdinalRecursionSyntax
open ReplacementPredicates (paramsUp)

def functional {n m} (p : Formula (n+3)) (ρ : Fin n → Fin m) (x h : Fin m) : Formula m := .all (.all
  ((operator p (paramsUp (paramsUp ρ)) x.castSucc.castSucc h.castSucc.castSucc (Fin.last m).castSucc).imp
    ((operator p (paramsUp (paramsUp ρ)) x.castSucc.castSucc h.castSucc.castSucc (Fin.last (m+1))).imp
      (.equal (Fin.last m).castSucc (Fin.last (m+1))))))

def deterministic {n m} (p : Formula (n+3)) (ρ : Fin n → Fin m) : Formula m := .all (.all
  (((ordinal (Fin.last m).castSucc).conj (functionOn (Fin.last (m+1)) (Fin.last m).castSucc)).imp
    (functional p (paramsUp (paramsUp ρ)) (Fin.last m).castSucc (Fin.last (m+1)))))

theorem functional_rename {n m k} (p : Formula (n+3)) (ρ : Fin n → Fin m) (x h : Fin m) (r : Fin m → Fin k) :
    (functional p ρ x h).rename r = functional p (fun i => r (ρ i)) (r x) (r h) := by
  simp only [functional, Formula.rename, operator_rename, paramsUp,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem deterministic_rename {n m k} (p : Formula (n+3)) (ρ : Fin n → Fin m) (r : Fin m → Fin k) :
    (deterministic p ρ).rename r = deterministic p (fun i => r (ρ i)) := by
  simp only [deterministic, Formula.rename, ordinal_rename, functionOn_rename, functional_rename, paramsUp,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem functional_at {n m} {Γ : Context m} (p : Formula (n+3)) (ρ : Fin n → Fin m) (x h u v : Fin m)
    (hf : Derives Γ (functional p ρ x h)) : Derives Γ
      ((operator p ρ x h u).imp ((operator p ρ x h v).imp (.equal u v))) := by
  have hi := Derives.allE v (Derives.allE u hf)
  simpa only [Formula.instantiate, Formula.rename, operator_rename, paramsUp,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi

theorem deterministic_at {n m} {Γ : Context m} (p : Formula (n+3)) (ρ : Fin n → Fin m) (x h : Fin m)
    (hf : Derives Γ (deterministic p ρ)) : Derives Γ
      (((ordinal x).conj (functionOn h x)).imp (functional p ρ x h)) := by
  have hi := Derives.allE h (Derives.allE x hf)
  simpa only [Formula.instantiate, Formula.rename, ordinal_rename, functionOn_rename, functional_rename, paramsUp,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi

theorem operator_subst_history {n m} {Γ : Context m} (p : Formula (n+3)) (ρ : Fin n → Fin m) (x h k y : Fin m)
    (he : Derives Γ (.equal h k)) (hp : Derives Γ (operator p ρ x h y)) : Derives Γ (operator p ρ x k y) := by
  have hi : Derives Γ ((operator p (paramsUp ρ) x.castSucc (Fin.last m) y.castSucc).instantiate h) := by
    simpa only [Formula.instantiate, operator_rename, paramsUp, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hp
  have hr := Derives.eqSubst (operator p (paramsUp ρ) x.castSucc (Fin.last m) y.castSucc) he hi
  simpa only [Formula.instantiate, operator_rename, paramsUp, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hr
end PPAC.Migration.OrdinalRecursionDeterminism
