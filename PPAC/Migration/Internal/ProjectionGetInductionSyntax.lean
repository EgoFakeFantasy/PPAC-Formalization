import PPAC.Migration.Internal.ProjectionGetZeroIndex

/-! 内部索引归纳的全输入／全输出正确性公式；该公式不进入独立get接受定义。 -/
namespace PPAC.Migration.Internal.ProjectionGetInductionSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax

def point {m} (w x i y : Fin m) : Formula m := (ProjectionTraceSyntax.get w x i y).iff
  ((Formula.mem x w).conj (RawCodeGetSyntax.get w x i y))

def correct {m} (w i : Fin m) : Formula m := .all (.all
  (point w.castSucc.castSucc (Fin.last m).castSucc i.castSucc.castSucc (Fin.last (m+1))))

def matrix : Formula 2 := correct 0 1

theorem point_rename {m l} (w x i y : Fin m) (ρ : Fin m → Fin l) :
    (point w x i y).rename ρ = point (ρ w) (ρ x) (ρ i) (ρ y) := by
  simp only [point, Formula.iff, Formula.rename, ProjectionTraceSyntax.get_rename, RawCodeGetSyntax.get_rename]

theorem correct_rename {m l} (w i : Fin m) (ρ : Fin m → Fin l) :
    (correct w i).rename ρ = correct (ρ w) (ρ i) := by
  simp only [correct, Formula.rename, point_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem matrix_pred {m} (ρ : Fin 1 → Fin m) (i : Fin m) : MinimalPredicates.pred matrix ρ i = correct (ρ 0) i := by
  have h0 : Fin.lastCases i ρ (0 : Fin 2) = ρ 0 := by
    change Fin.lastCases i ρ (0 : Fin 1).castSucc = ρ 0
    exact Fin.lastCases_castSucc _
  have h1 : Fin.lastCases i ρ (1 : Fin 2) = i := by
    change Fin.lastCases i ρ (Fin.last 1) = i
    exact Fin.lastCases_last
  simp only [MinimalPredicates.pred, matrix, correct_rename, h0, h1]

theorem at_value {m} {Γ : Context m} (w i x y : Fin m) (hc : Derives Γ (correct w i)) : Derives Γ (point w x i y) := by
  have h0 := Derives.allE x hc
  have h1 := Derives.allE y h0
  simpa only [correct, Formula.instantiate, Formula.rename, point_rename, Formula.liftRen,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using h1

theorem index_subst {m} {Γ : Context m} (w i j : Fin m) (he : Derives Γ (.equal i j))
    (hi : Derives Γ (correct w i)) : Derives Γ (correct w j) := by
  have hin : Derives Γ ((correct w.castSucc (Fin.last m)).instantiate i) := by
    simpa only [Formula.instantiate, correct_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi
  have ho := Derives.eqSubst (correct w.castSucc (Fin.last m)) he hin
  simpa only [Formula.instantiate, correct_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho

end PPAC.Migration.Internal.ProjectionGetInductionSyntax
