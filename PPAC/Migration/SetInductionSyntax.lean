import PPAC.Migration.ObjectTransitiveCover
import PPAC.Migration.BoundedInduction

/-! 无界集合归纳的全参数纯对象模式；不引入内部统一真值谓词。 -/
namespace PPAC.Migration.SetInductionSyntax
open Source SourceAlgebra MinimalPredicates
open ReplacementPredicates (paramsUp)

def below {n m} (p : Formula (n+1)) (ρ : Fin n → Fin m) (x : Fin m) : Formula m :=
  .all ((Formula.mem (Fin.last m) x.castSucc).imp (pred p (paramsUp ρ) (Fin.last m)))

def progressive {n m} (p : Formula (n+1)) (ρ : Fin n → Fin m) : Formula m :=
  .all ((below p (paramsUp ρ) (Fin.last m)).imp (pred p (paramsUp ρ) (Fin.last m)))

def holds {n m} (p : Formula (n+1)) (ρ : Fin n → Fin m) : Formula m :=
  .all (pred p (paramsUp ρ) (Fin.last m))

def sentence {n} (p : Formula (n+1)) : Source.Sentence := ((progressive p id).imp (holds p id)).close

theorem below_rename {n m k} (p : Formula (n+1)) (ρ : Fin n → Fin m) (x : Fin m) (r : Fin m → Fin k) :
    (below p ρ x).rename r = below p (fun i => r (ρ i)) (r x) := by
  simp only [below, Formula.rename, pred_rename, paramsUp, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem progressive_rename {n m k} (p : Formula (n+1)) (ρ : Fin n → Fin m) (r : Fin m → Fin k) :
    (progressive p ρ).rename r = progressive p (fun i => r (ρ i)) := by
  simp only [progressive, Formula.rename, below_rename, pred_rename, paramsUp, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem holds_rename {n m k} (p : Formula (n+1)) (ρ : Fin n → Fin m) (r : Fin m → Fin k) :
    (holds p ρ).rename r = holds p (fun i => r (ρ i)) := by
  simp only [holds, Formula.rename, pred_rename, paramsUp, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem below_at {n m} {Γ : Context m} (p : Formula (n+1)) (ρ : Fin n → Fin m) (x y : Fin m)
    (h : Derives Γ (below p ρ x)) : Derives Γ ((Formula.mem y x).imp (pred p ρ y)) := by
  have hi := Derives.allE y h
  simpa only [Formula.instantiate, Formula.rename, pred_rename, paramsUp, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi

theorem progressive_at {n m} {Γ : Context m} (p : Formula (n+1)) (ρ : Fin n → Fin m) (x : Fin m)
    (h : Derives Γ (progressive p ρ)) : Derives Γ ((below p ρ x).imp (pred p ρ x)) := by
  have hi := Derives.allE x h
  simpa only [Formula.instantiate, Formula.rename, below_rename, pred_rename, paramsUp, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi

theorem holds_at {n m} {Γ : Context m} (p : Formula (n+1)) (ρ : Fin n → Fin m) (x : Fin m)
    (h : Derives Γ (holds p ρ)) : Derives Γ (pred p ρ x) := by
  have hi := Derives.allE x h
  simpa only [Formula.instantiate, pred_rename, paramsUp, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi
end PPAC.Migration.SetInductionSyntax
