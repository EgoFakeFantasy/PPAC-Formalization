import PPAC.Migration.Internal.StructuralListCheckPreservationStep

/-! 首次终端以前的真实执行保持原Valid的内部索引归纳性质。 -/
namespace PPAC.Migration.Internal.StructuralListCheckInvariantSyntax
open Source SourceAlgebra SourceLogic StructuralListProjectionSyntax StructuralListCheckSyntax
open StructuralListTraceSyntax (valid valid_rename)

def invariant {m} (w n r : Fin m) : Formula m := (before w n r).imp (.all
  ((iteration false w.castSucc n.castSucc r.castSucc (Fin.last m)).imp
    ((valid w.castSucc n.castSucc).iff (valid w.castSucc (Fin.last m)))))

def matrix : Formula 3 := invariant 0 1 2

theorem invariant_rename {m k} (w n r : Fin m) (s : Fin m → Fin k) : (invariant w n r).rename s = invariant (s w) (s n) (s r) := by
  simp only [invariant, Formula.rename, Formula.iff, before_rename, iteration_rename, valid_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem matrix_pred {m} (ρ : Fin 2 → Fin m) (x : Fin m) : MinimalPredicates.pred matrix ρ x = invariant (ρ 0) (ρ 1) x := by
  have h0 : Fin.lastCases x ρ (0 : Fin 3) = ρ 0 := by
    change Fin.lastCases x ρ (0 : Fin 2).castSucc = ρ 0
    exact Fin.lastCases_castSucc _
  have h1 : Fin.lastCases x ρ (1 : Fin 3) = ρ 1 := by
    change Fin.lastCases x ρ (1 : Fin 2).castSucc = ρ 1
    exact Fin.lastCases_castSucc _
  have h2 : Fin.lastCases x ρ (2 : Fin 3) = x := by
    change Fin.lastCases x ρ (Fin.last 2) = x
    exact Fin.lastCases_last
  simp only [MinimalPredicates.pred, matrix, invariant_rename, h0, h1, h2]

theorem at_value {m} {Γ : Context m} (w n r b : Fin m) (hi : Derives Γ (invariant w n r))
    (hf : Derives Γ (before w n r)) (hb : Derives Γ (iteration false w n r b)) : Derives Γ ((valid w n).iff (valid w b)) := by
  have h : Derives Γ ((iteration false w n r b).imp ((valid w n).iff (valid w b))) := by
    simpa only [Formula.instantiate, Formula.rename, Formula.iff, iteration_rename, valid_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.allE b (.impE hi hf)
  exact .impE h hb
end PPAC.Migration.Internal.StructuralListCheckInvariantSyntax
