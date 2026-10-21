import PPAC.Migration.OrdinalRecursionUnion

/-! 全部内部原序数上的递归存在与唯一存在模式，不以外部序数递归替代。 -/
namespace PPAC.Migration.OrdinalRecursionExistenceSyntax
open Source SourceAlgebra SourceLogic OrdinalSyntax OrdinalRecursionSyntax
open ReplacementPredicates (paramsUp)

def existsAt {n m} (p : Formula (n+3)) (ρ : Fin n → Fin m) (a : Fin m) : Formula m :=
  (ordinal a).imp (recursorExists p ρ a)

def existenceMatrix {n} (p : Formula (n+3)) : Formula (n+1) := existsAt p Fin.castSucc (Fin.last n)

def holds {n m} (p : Formula (n+3)) (ρ : Fin n → Fin m) : Formula m := .all
  (existsAt p (paramsUp ρ) (Fin.last m))

def uniqueAt {n m} (p : Formula (n+3)) (ρ : Fin n → Fin m) (a f : Fin m) : Formula m := .all
  ((recursor p (paramsUp ρ) (Fin.last m) a.castSucc).imp (.equal (Fin.last m) f.castSucc))

def fiber {n m} (p : Formula (n+3)) (ρ : Fin n → Fin m) (a : Fin m) : Formula m := .ex
  ((recursor p (paramsUp ρ) (Fin.last m) a.castSucc).conj (uniqueAt p (paramsUp ρ) a.castSucc (Fin.last m)))

def allUnique {n m} (p : Formula (n+3)) (ρ : Fin n → Fin m) : Formula m := .all
  ((ordinal (Fin.last m)).imp (fiber p (paramsUp ρ) (Fin.last m)))

theorem existsAt_rename {n m k} (p : Formula (n+3)) (ρ : Fin n → Fin m) (a : Fin m) (r : Fin m → Fin k) :
    (existsAt p ρ a).rename r = existsAt p (fun i => r (ρ i)) (r a) := by
  simp only [existsAt, Formula.rename, ordinal_rename, recursorExists_rename]


theorem holds_rename {n m k} (p : Formula (n+3)) (ρ : Fin n → Fin m) (r : Fin m → Fin k) :
    (holds p ρ).rename r = holds p (fun i => r (ρ i)) := by
  simp only [holds, Formula.rename, existsAt_rename, paramsUp, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]


theorem uniqueAt_rename {n m k} (p : Formula (n+3)) (ρ : Fin n → Fin m) (a f : Fin m) (r : Fin m → Fin k) :
    (uniqueAt p ρ a f).rename r = uniqueAt p (fun i => r (ρ i)) (r a) (r f) := by
  simp only [uniqueAt, Formula.rename, recursor_rename, paramsUp, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]


theorem fiber_rename {n m k} (p : Formula (n+3)) (ρ : Fin n → Fin m) (a : Fin m) (r : Fin m → Fin k) :
    (fiber p ρ a).rename r = fiber p (fun i => r (ρ i)) (r a) := by
  simp only [fiber, Formula.rename, recursor_rename, uniqueAt_rename, paramsUp, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]


theorem allUnique_rename {n m k} (p : Formula (n+3)) (ρ : Fin n → Fin m) (r : Fin m → Fin k) :
    (allUnique p ρ).rename r = allUnique p (fun i => r (ρ i)) := by
  simp only [allUnique, Formula.rename, ordinal_rename, fiber_rename, paramsUp, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem existence_pred {n m} (p : Formula (n+3)) (ρ : Fin n → Fin m) (a : Fin m) :
    MinimalPredicates.pred (existenceMatrix p) ρ a = existsAt p ρ a := by
  simp only [MinimalPredicates.pred, existenceMatrix, existsAt_rename, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem holds_at {n m} {Γ : Context m} (p : Formula (n+3)) (ρ : Fin n → Fin m) (a : Fin m)
    (hh : Derives Γ (holds p ρ)) : Derives Γ (existsAt p ρ a) := by
  have hi := Derives.allE a hh
  simpa only [Formula.instantiate, existsAt_rename, paramsUp, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi
end PPAC.Migration.OrdinalRecursionExistenceSyntax
