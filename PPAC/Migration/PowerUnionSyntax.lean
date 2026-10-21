import PPAC.Migration.PowerValueCollection

/-! 历史输出幂集精确像的实际并，作为三元对象递推算子。 -/
namespace PPAC.Migration.PowerUnionSyntax
open Source SourceAlgebra SourceLogic PowerValueSyntax InsertSyntax

def operation {m} (a h y : Fin m) : Formula m := .ex
  ((PowerValueSyntax.range (Fin.last m) a.castSucc h.castSucc).conj (unionOf y.castSucc (Fin.last m)))

def existsOperation {m} (a h : Fin m) : Formula m := .ex (operation a.castSucc h.castSucc (Fin.last m))

def matrix : Formula 3 := operation 0 1 2

theorem operation_rename {m k} (a h y : Fin m) (r : Fin m → Fin k) :
    (operation a h y).rename r = operation (r a) (r h) (r y) := by
  simp only [operation, Formula.rename, PowerValueSyntax.range_rename, unionOf_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem existsOperation_rename {m k} (a h : Fin m) (r : Fin m → Fin k) :
    (existsOperation a h).rename r = existsOperation (r a) (r h) := by
  simp only [existsOperation, Formula.rename, operation_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem matrix_operator {m} (ρ : Fin 0 → Fin m) (a h y : Fin m) :
    OrdinalRecursionSyntax.operator matrix ρ a h y = operation a h y := by
  have h0 : Fin.lastCases y (Fin.lastCases h (Fin.lastCases a ρ)) (0 : Fin 3) = a := by
    change Fin.lastCases y (Fin.lastCases h (Fin.lastCases a ρ)) (Fin.last 0).castSucc.castSucc = a
    simp only [Fin.lastCases_last, Fin.lastCases_castSucc]
  have h1 : Fin.lastCases y (Fin.lastCases h (Fin.lastCases a ρ)) (1 : Fin 3) = h := by
    change Fin.lastCases y (Fin.lastCases h (Fin.lastCases a ρ)) (Fin.last 1).castSucc = h
    simp only [Fin.lastCases_last, Fin.lastCases_castSucc]
  have h2 : Fin.lastCases y (Fin.lastCases h (Fin.lastCases a ρ)) (2 : Fin 3) = y := by
    change Fin.lastCases y (Fin.lastCases h (Fin.lastCases a ρ)) (Fin.last 2) = y
    exact Fin.lastCases_last
  simp only [OrdinalRecursionSyntax.operator, matrix, operation_rename, h0, h1, h2]

theorem intro_operation {m} {Γ : Context m} (c a h y : Fin m)
    (hr : Derives Γ (PowerValueSyntax.range c a h)) (hu : Derives Γ (unionOf y c)) : Derives Γ (operation a h y) := by
  apply Derives.exI c
  simpa only [Formula.instantiate, Formula.rename, PowerValueSyntax.range_rename, unionOf_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.conjI hr hu
end PPAC.Migration.PowerUnionSyntax
