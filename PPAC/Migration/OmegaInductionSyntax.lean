import PPAC.Migration.OmegaAlgebra

/-! 任意参数和任意矩阵的对象ω后继归纳模式，不引入统一真值谓词。 -/
namespace PPAC.Migration.OmegaInductionSyntax
open Source SourceAlgebra OmegaSyntax MinimalPredicates
open ReplacementPredicates (paramsUp)

def base {n m} (p : Formula (n+1)) (ρ : Fin n → Fin m) : Formula m :=
  .all ((empty (Fin.last m)).imp (pred p (paramsUp ρ) (Fin.last m)))

def step {n m} (p : Formula (n+1)) (ρ : Fin n → Fin m) (w : Fin m) : Formula m :=
  .all (.all ((Formula.mem (Fin.last m).castSucc w.castSucc.castSucc).imp
    ((pred p (paramsUp (paramsUp ρ)) (Fin.last m).castSucc).imp
      ((successor (Fin.last (m+1)) (Fin.last m).castSucc).imp (pred p (paramsUp (paramsUp ρ)) (Fin.last (m+1)))))))

def holds {n m} (p : Formula (n+1)) (ρ : Fin n → Fin m) (w : Fin m) : Formula m :=
  .all ((Formula.mem (Fin.last m) w.castSucc).imp (pred p (paramsUp ρ) (Fin.last m)))

def sentence {n} (p : Formula (n+1)) : Source.Sentence :=
  (Formula.all ((omega (Fin.last n)).imp ((base p Fin.castSucc).imp
    ((step p Fin.castSucc (Fin.last n)).imp (holds p Fin.castSucc (Fin.last n)))))).close

theorem base_rename {n m k} (p : Formula (n+1)) (ρ : Fin n → Fin m) (r : Fin m → Fin k) :
    (base p ρ).rename r = base p (fun i => r (ρ i)) := by
  simp only [base, Formula.rename, empty_rename, pred_rename, paramsUp, Formula.liftRen,
    Fin.lastCases_last, Fin.lastCases_castSucc]

theorem step_rename {n m k} (p : Formula (n+1)) (ρ : Fin n → Fin m) (w : Fin m) (r : Fin m → Fin k) :
    (step p ρ w).rename r = step p (fun i => r (ρ i)) (r w) := by
  simp only [step, Formula.rename, successor_rename, pred_rename, paramsUp, Formula.liftRen,
    Fin.lastCases_last, Fin.lastCases_castSucc]

theorem holds_rename {n m k} (p : Formula (n+1)) (ρ : Fin n → Fin m) (w : Fin m) (r : Fin m → Fin k) :
    (holds p ρ w).rename r = holds p (fun i => r (ρ i)) (r w) := by
  simp only [holds, Formula.rename, pred_rename, paramsUp, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem base_at {n m} {Γ : Context m} (p : Formula (n+1)) (ρ : Fin n → Fin m) (z : Fin m)
    (h : Derives Γ (base p ρ)) : Derives Γ ((empty z).imp (pred p ρ z)) := by
  have hi := Derives.allE z h
  simpa only [Formula.instantiate, Formula.rename, empty_rename, pred_rename, paramsUp,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi

theorem step_at {n m} {Γ : Context m} (p : Formula (n+1)) (ρ : Fin n → Fin m) (w x s : Fin m)
    (h : Derives Γ (step p ρ w)) :
    Derives Γ ((Formula.mem x w).imp ((pred p ρ x).imp ((successor s x).imp (pred p ρ s)))) := by
  have hi := Derives.allE s (Derives.allE x h)
  simpa only [Formula.instantiate, Formula.rename, successor_rename, pred_rename, paramsUp, Formula.liftRen,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi
end PPAC.Migration.OmegaInductionSyntax
