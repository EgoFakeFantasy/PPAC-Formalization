import PPAC.Migration.SetInduction

/-! 任意非空可定义性质的全局成员极小元模式，不添加对象类或统一真值谓词。 -/
namespace PPAC.Migration.GlobalMinimalSyntax
open Source SourceAlgebra MinimalPredicates
open ReplacementPredicates (paramsUp)

def has {n m} (p : Formula (n+1)) (ρ : Fin n → Fin m) : Formula m :=
  .ex (pred p (paramsUp ρ) (Fin.last m))

def minimal {n m} (p : Formula (n+1)) (ρ : Fin n → Fin m) (x : Fin m) : Formula m :=
  (pred p ρ x).conj (SetInductionSyntax.below p.neg ρ x)

def minimalExists {n m} (p : Formula (n+1)) (ρ : Fin n → Fin m) : Formula m :=
  .ex (minimal p (paramsUp ρ) (Fin.last m))

def sentence {n} (p : Formula (n+1)) : Source.Sentence := ((has p id).imp (minimalExists p id)).close

theorem has_rename {n m k} (p : Formula (n+1)) (ρ : Fin n → Fin m) (r : Fin m → Fin k) :
    (has p ρ).rename r = has p (fun i => r (ρ i)) := by
  simp only [has, Formula.rename, pred_rename, paramsUp, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem minimal_rename {n m k} (p : Formula (n+1)) (ρ : Fin n → Fin m) (x : Fin m) (r : Fin m → Fin k) :
    (minimal p ρ x).rename r = minimal p (fun i => r (ρ i)) (r x) := by
  simp only [minimal, Formula.rename, pred_rename, SetInductionSyntax.below_rename]

theorem minimalExists_rename {n m k} (p : Formula (n+1)) (ρ : Fin n → Fin m) (r : Fin m → Fin k) :
    (minimalExists p ρ).rename r = minimalExists p (fun i => r (ρ i)) := by
  simp only [minimalExists, Formula.rename, minimal_rename, paramsUp, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]
end PPAC.Migration.GlobalMinimalSyntax
