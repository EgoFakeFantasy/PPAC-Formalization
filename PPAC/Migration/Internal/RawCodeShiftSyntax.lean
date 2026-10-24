import PPAC.Migration.Internal.RawCodeIterationTransport

/-! 两条真实投影轨迹在同一内部自然索引上的步关系；归纳矩阵仅为纯对象公式。 -/
namespace PPAC.Migration.Internal.RawCodeShiftSyntax
open Source SourceAlgebra SourceLogic RawCodeProjectionSyntax

def coupled {m} (head : Bool) (w a b r : Fin m) : Formula m := .all (.all
  ((iteration head w.castSucc.castSucc a.castSucc.castSucc r.castSucc.castSucc (Fin.last m).castSucc).imp
    ((iteration head w.castSucc.castSucc b.castSucc.castSucc r.castSucc.castSucc (Fin.last (m+1))).imp
      (step head w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))))))

def matrix (head : Bool) : Formula 4 := coupled head 0 1 2 3

theorem coupled_rename {m k} (head : Bool) (w a b r : Fin m) (s : Fin m → Fin k) :
    (coupled head w a b r).rename s = coupled head (s w) (s a) (s b) (s r) := by
  simp only [coupled, Formula.rename, iteration_rename, step_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem matrix_pred {m} (head : Bool) (ρ : Fin 3 → Fin m) (x : Fin m) :
    MinimalPredicates.pred (matrix head) ρ x = coupled head (ρ 0) (ρ 1) (ρ 2) x := by
  have h0 : Fin.lastCases x ρ (0 : Fin 4) = ρ 0 := by
    change Fin.lastCases x ρ (0 : Fin 3).castSucc = ρ 0
    exact Fin.lastCases_castSucc _
  have h1 : Fin.lastCases x ρ (1 : Fin 4) = ρ 1 := by
    change Fin.lastCases x ρ (1 : Fin 3).castSucc = ρ 1
    exact Fin.lastCases_castSucc _
  have h2 : Fin.lastCases x ρ (2 : Fin 4) = ρ 2 := by
    change Fin.lastCases x ρ (2 : Fin 3).castSucc = ρ 2
    exact Fin.lastCases_castSucc _
  have h3 : Fin.lastCases x ρ (3 : Fin 4) = x := by
    change Fin.lastCases x ρ (Fin.last 3) = x
    exact Fin.lastCases_last
  simp only [MinimalPredicates.pred, matrix, coupled_rename, h0, h1, h2, h3]

theorem at_values {m} {Γ : Context m} (head : Bool) (w a b r u v : Fin m)
    (hc : Derives Γ (coupled head w a b r)) (hu : Derives Γ (iteration head w a r u))
    (hv : Derives Γ (iteration head w b r v)) : Derives Γ (step head w u v) := by
  have h : Derives Γ ((iteration head w a r u).imp ((iteration head w b r v).imp (step head w u v))) := by
    simpa only [coupled, Formula.instantiate, Formula.rename, iteration_rename, step_rename,
      Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.allE v (Derives.allE u hc)
  exact .impE (.impE h hu) hv
end PPAC.Migration.Internal.RawCodeShiftSyntax
