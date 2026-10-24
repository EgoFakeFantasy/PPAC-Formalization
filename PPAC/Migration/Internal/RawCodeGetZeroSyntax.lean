import PPAC.Migration.Internal.RawCodeGetLaws

/-! 输入零码的全候选输出性质与内部索引归纳矩阵。 -/
namespace PPAC.Migration.Internal.RawCodeGetZeroSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax RawCodeGetSyntax

def correct {m} (w z i : Fin m) : Formula m := .all
  ((get w.castSucc z.castSucc i.castSucc (Fin.last m)).imp (empty (Fin.last m)))
def matrix : Formula 3 := correct 0 1 2

theorem correct_rename {m l} (w z i : Fin m) (ρ : Fin m → Fin l) :
    (correct w z i).rename ρ = correct (ρ w) (ρ z) (ρ i) := by
  simp only [correct, Formula.rename, get_rename, empty_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem matrix_pred {m} (ρ : Fin 2 → Fin m) (i : Fin m) :
    MinimalPredicates.pred matrix ρ i = correct (ρ 0) (ρ 1) i := by
  have h0 : Fin.lastCases i ρ (0 : Fin 3) = ρ 0 := by
    change Fin.lastCases i ρ (0 : Fin 2).castSucc = ρ 0
    exact Fin.lastCases_castSucc _
  have h1 : Fin.lastCases i ρ (1 : Fin 3) = ρ 1 := by
    change Fin.lastCases i ρ (1 : Fin 2).castSucc = ρ 1
    exact Fin.lastCases_castSucc _
  have h2 : Fin.lastCases i ρ (2 : Fin 3) = i := by
    change Fin.lastCases i ρ (Fin.last 2) = i
    exact Fin.lastCases_last
  simp only [MinimalPredicates.pred, matrix, correct_rename, h0, h1, h2]

theorem at_value {m} {Γ : Context m} (w z i y : Fin m) (hc : Derives Γ (correct w z i))
    (hy : Derives Γ (get w z i y)) : Derives Γ (empty y) := by
  have hp : Derives Γ ((get w z i y).imp (empty y)) := by
    simpa only [correct, Formula.instantiate, Formula.rename, get_rename, empty_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.allE y hc
  exact .impE hp hy

end PPAC.Migration.Internal.RawCodeGetZeroSyntax
