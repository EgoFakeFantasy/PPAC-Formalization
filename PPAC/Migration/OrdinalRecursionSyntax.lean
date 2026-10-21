import PPAC.Migration.ObjectOrdinalUnion

/-! 任意参数三元递推公式的原对象递归图；每步显式存在实际前段图。 -/
namespace PPAC.Migration.OrdinalRecursionSyntax
open Source SourceAlgebra SourceLogic GraphSyntax RestrictionSyntax
open ReplacementPredicates (paramsUp)

/-- p的最后三槽依次为索引x、实际前段图h和输出y。 -/
def operator {n m} (p : Formula (n+3)) (ρ : Fin n → Fin m) (x h y : Fin m) : Formula m :=
  p.rename (Fin.lastCases y (Fin.lastCases h (Fin.lastCases x ρ)))

/-- 每一步保留真实的前段限制集合见证，不把它当宿主函数。 -/
def history {n m} (p : Formula (n+3)) (ρ : Fin n → Fin m) (f x y : Fin m) : Formula m := .ex
  ((restrict (Fin.last m) f.castSucc x.castSucc).conj
    (operator p (paramsUp ρ) x.castSucc (Fin.last m) y.castSucc))

def equations {n m} (p : Formula (n+3)) (ρ : Fin n → Fin m) (f d : Fin m) : Formula m := .all
  ((Formula.mem (Fin.last m) d.castSucc).imp (.all
    ((edge f.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).imp
      (history p (paramsUp (paramsUp ρ)) f.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))))))

def recursor {n m} (p : Formula (n+3)) (ρ : Fin n → Fin m) (f d : Fin m) : Formula m :=
  (functionOn f d).conj (equations p ρ f d)

def recursorExists {n m} (p : Formula (n+3)) (ρ : Fin n → Fin m) (d : Fin m) : Formula m := .ex
  (recursor p (paramsUp ρ) (Fin.last m) d.castSucc)

theorem operator_rename {n m k} (p : Formula (n+3)) (ρ : Fin n → Fin m) (x h y : Fin m) (r : Fin m → Fin k) :
    (operator p ρ x h y).rename r = operator p (fun i => r (ρ i)) (r x) (r h) (r y) := by
  rw [operator, rename_comp, operator]
  congr 1
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.lastCases_last]
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [Fin.lastCases_last, Fin.lastCases_castSucc]
    · refine Fin.lastCases ?_ (fun j => ?_) j <;> simp only [Fin.lastCases_last, Fin.lastCases_castSucc]

theorem history_rename {n m k} (p : Formula (n+3)) (ρ : Fin n → Fin m) (f x y : Fin m) (r : Fin m → Fin k) :
    (history p ρ f x y).rename r = history p (fun i => r (ρ i)) (r f) (r x) (r y) := by
  simp only [history, Formula.rename, restrict_rename, operator_rename, paramsUp,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem equations_rename {n m k} (p : Formula (n+3)) (ρ : Fin n → Fin m) (f d : Fin m) (r : Fin m → Fin k) :
    (equations p ρ f d).rename r = equations p (fun i => r (ρ i)) (r f) (r d) := by
  simp only [equations, Formula.rename, edge_rename, history_rename, paramsUp,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem recursor_rename {n m k} (p : Formula (n+3)) (ρ : Fin n → Fin m) (f d : Fin m) (r : Fin m → Fin k) :
    (recursor p ρ f d).rename r = recursor p (fun i => r (ρ i)) (r f) (r d) := by
  simp only [recursor, Formula.rename, functionOn_rename, equations_rename]

theorem recursorExists_rename {n m k} (p : Formula (n+3)) (ρ : Fin n → Fin m) (d : Fin m) (r : Fin m → Fin k) :
    (recursorExists p ρ d).rename r = recursorExists p (fun i => r (ρ i)) (r d) := by
  simp only [recursorExists, Formula.rename, recursor_rename, paramsUp,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem equations_at {n m} {Γ : Context m} (p : Formula (n+3)) (ρ : Fin n → Fin m) (f d x y : Fin m)
    (h : Derives Γ (equations p ρ f d)) :
    Derives Γ ((Formula.mem x d).imp ((edge f x y).imp (history p ρ f x y))) := by
  have hx := Derives.allE x h
  have hxx : Derives Γ ((Formula.mem x d).imp (.all
      ((edge f.castSucc x.castSucc (Fin.last m)).imp (history p (paramsUp ρ) f.castSucc x.castSucc (Fin.last m))))) := by
    simpa only [Formula.instantiate, Formula.rename, edge_rename, history_rename, paramsUp,
      Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hx
  apply Derives.impI
  have hi := Derives.allE y (Derives.impE (add hxx _) (.hyp (Or.inl rfl)))
  simpa only [Formula.instantiate, Formula.rename, edge_rename, history_rename, paramsUp,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi

theorem history_intro {n m} {Γ : Context m} (p : Formula (n+3)) (ρ : Fin n → Fin m) (f x h y : Fin m)
    (hr : Derives Γ (restrict h f x)) (hp : Derives Γ (operator p ρ x h y)) : Derives Γ (history p ρ f x y) := by
  apply Derives.exI h
  simpa only [Formula.instantiate, Formula.rename, restrict_rename, operator_rename, paramsUp,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.conjI hr hp
end PPAC.Migration.OrdinalRecursionSyntax
