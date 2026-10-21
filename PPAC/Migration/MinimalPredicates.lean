import PPAC.Migration.ReplacementPredicates

/-! 成员关系极小见证的纯对象公式；没有外部良基性或秩假设。 -/
namespace PPAC.Migration.MinimalPredicates
open Source SourceAlgebra
open ReplacementPredicates (paramsUp)

def pred {n m} (p : Formula (n+1)) (ρ : Fin n → Fin m) (x : Fin m) : Formula m :=
  p.rename (Fin.lastCases x ρ)

def satisfying {n m} (p : Formula (n+1)) (ρ : Fin n → Fin m) (a x : Fin m) : Formula m :=
  (Formula.mem x a).conj (pred p ρ x)

def has {n m} (p : Formula (n+1)) (ρ : Fin n → Fin m) (a : Fin m) : Formula m :=
  .ex (satisfying p (paramsUp ρ) a.castSucc (Fin.last m))

def minimal {n m} (p : Formula (n+1)) (ρ : Fin n → Fin m) (a x : Fin m) : Formula m :=
  (satisfying p ρ a x).conj (.all ((satisfying p (paramsUp ρ) a.castSucc (Fin.last m)).imp
    (Formula.mem (Fin.last m) x.castSucc).neg))

def minimalExists {n m} (p : Formula (n+1)) (ρ : Fin n → Fin m) (a : Fin m) : Formula m :=
  .ex (minimal p (paramsUp ρ) a.castSucc (Fin.last m))

def separated {n m} (p : Formula (n+1)) (ρ : Fin n → Fin m) (a c : Fin m) : Formula m :=
  .all ((Formula.mem (Fin.last m) c.castSucc).iff
    (satisfying p (paramsUp ρ) a.castSucc (Fin.last m)))

def separationExists {n m} (p : Formula (n+1)) (ρ : Fin n → Fin m) (a : Fin m) : Formula m :=
  .ex (separated p (paramsUp ρ) a.castSucc (Fin.last m))

def inhabited {m} (c : Fin m) : Formula m := .ex (.mem (Fin.last m) c.castSucc)

def setMinimal {m} (c x : Fin m) : Formula m :=
  (Formula.mem x c).conj (.all ((Formula.mem (Fin.last m) x.castSucc).imp
    (Formula.mem (Fin.last m) c.castSucc).neg))

def regular {m} (c : Fin m) : Formula m := .ex (setMinimal c.castSucc (Fin.last m))

theorem pred_rename {n m k} (p : Formula (n+1)) (ρ : Fin n → Fin m) (x : Fin m) (r : Fin m → Fin k) :
    (pred p ρ x).rename r = pred p (fun i => r (ρ i)) (r x) := by
  rw [pred, rename_comp, pred]
  congr 1
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;>
    simp only [Fin.lastCases_last, Fin.lastCases_castSucc]

theorem satisfying_rename {n m k} (p : Formula (n+1)) (ρ : Fin n → Fin m) (a x : Fin m)
    (r : Fin m → Fin k) :
    (satisfying p ρ a x).rename r = satisfying p (fun i => r (ρ i)) (r a) (r x) := by
  simp only [satisfying, Formula.rename, pred_rename]

theorem has_rename {n m k} (p : Formula (n+1)) (ρ : Fin n → Fin m) (a : Fin m)
    (r : Fin m → Fin k) :
    (has p ρ a).rename r = has p (fun i => r (ρ i)) (r a) := by
  simp only [has, Formula.rename, satisfying_rename, paramsUp, Formula.liftRen,
    Fin.lastCases_last, Fin.lastCases_castSucc]

theorem minimal_rename {n m k} (p : Formula (n+1)) (ρ : Fin n → Fin m) (a x : Fin m)
    (r : Fin m → Fin k) :
    (minimal p ρ a x).rename r = minimal p (fun i => r (ρ i)) (r a) (r x) := by
  simp only [minimal, Formula.rename, satisfying_rename, paramsUp, Formula.liftRen,
    Fin.lastCases_last, Fin.lastCases_castSucc]

theorem minimalExists_rename {n m k} (p : Formula (n+1)) (ρ : Fin n → Fin m) (a : Fin m)
    (r : Fin m → Fin k) :
    (minimalExists p ρ a).rename r = minimalExists p (fun i => r (ρ i)) (r a) := by
  simp only [minimalExists, Formula.rename, minimal_rename, paramsUp, Formula.liftRen,
    Fin.lastCases_last, Fin.lastCases_castSucc]

theorem separated_rename {n m k} (p : Formula (n+1)) (ρ : Fin n → Fin m) (a c : Fin m)
    (r : Fin m → Fin k) :
    (separated p ρ a c).rename r = separated p (fun i => r (ρ i)) (r a) (r c) := by
  simp only [separated, Formula.rename, satisfying_rename, paramsUp, Formula.liftRen,
    Fin.lastCases_last, Fin.lastCases_castSucc]

theorem separationExists_rename {n m k} (p : Formula (n+1)) (ρ : Fin n → Fin m) (a : Fin m)
    (r : Fin m → Fin k) :
    (separationExists p ρ a).rename r = separationExists p (fun i => r (ρ i)) (r a) := by
  simp only [separationExists, Formula.rename, separated_rename, paramsUp, Formula.liftRen,
    Fin.lastCases_last, Fin.lastCases_castSucc]

theorem inhabited_rename {m k} (c : Fin m) (r : Fin m → Fin k) :
    (inhabited c).rename r = inhabited (r c) := by
  simp only [inhabited, Formula.rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem setMinimal_rename {m k} (c x : Fin m) (r : Fin m → Fin k) :
    (setMinimal c x).rename r = setMinimal (r c) (r x) := by
  simp only [setMinimal, Formula.rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem regular_rename {m k} (c : Fin m) (r : Fin m → Fin k) :
    (regular c).rename r = regular (r c) := by
  simp only [regular, Formula.rename, setMinimal_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem specialize_separated {n m} {Γ : Context m} (p : Formula (n+1)) (ρ : Fin n → Fin m)
    (a c x : Fin m) (h : Derives Γ (separated p ρ a c)) :
    Derives Γ ((Formula.mem x c).iff (satisfying p ρ a x)) := by
  have hi := Derives.allE x h
  simpa only [Formula.instantiate, Formula.rename, satisfying_rename, paramsUp,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi

theorem specialize_setMinimal {m} {Γ : Context m} (c x y : Fin m)
    (h : Derives Γ (setMinimal c x)) :
    Derives Γ ((Formula.mem y x).imp (Formula.mem y c).neg) := by
  have hi := Derives.allE y (Derives.conjR h)
  simpa only [Formula.instantiate, Formula.rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi

theorem specialize_minimal {n m} {Γ : Context m} (p : Formula (n+1)) (ρ : Fin n → Fin m)
    (a x y : Fin m) (h : Derives Γ (minimal p ρ a x)) :
    Derives Γ ((satisfying p ρ a y).imp (Formula.mem y x).neg) := by
  have hi := Derives.allE y (Derives.conjR h)
  simpa only [Formula.instantiate, Formula.rename, satisfying_rename, paramsUp,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi

theorem pred_neg {n m} (p : Formula (n+1)) (ρ : Fin n → Fin m) (x : Fin m) :
    pred p.neg ρ x = (pred p ρ x).neg := rfl
end PPAC.Migration.MinimalPredicates
