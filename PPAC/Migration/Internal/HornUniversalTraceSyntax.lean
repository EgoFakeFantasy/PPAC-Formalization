import PPAC.Migration.Internal.HornTraceExtension

/-! 全部实际原闭轨迹根的Separation集合；仅用于构造见证，不改变独立原执行定义。 -/
namespace PPAC.Migration.Internal.HornUniversalTraceSyntax
open Source SourceAlgebra SourceLogic
open SyntaxRenameQuerySyntax (of_eq)

def matrix : Formula 2 := HornLookupConditionSyntax.condition (0 : Fin 1).castSucc (Fin.last 1)

def one {m} (w : Fin m) : Fin 1 → Fin m := fun _ => w

def value {m} (w V : Fin m) : Formula m := MinimalPredicates.separated matrix (one w) w V

def existsValue {m} (w : Fin m) : Formula m := .ex (value w.castSucc (Fin.last m))

theorem matrix_pred {m} (ρ : Fin 1 → Fin m) (r : Fin m) :
    MinimalPredicates.pred matrix ρ r = HornLookupConditionSyntax.condition (ρ 0) r := by
  simp only [matrix, MinimalPredicates.pred, HornLookupConditionSyntax.condition_rename, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem value_rename {m k} (w V : Fin m) (ρ : Fin m → Fin k) :
    (value w V).rename ρ = value (ρ w) (ρ V) := by
  simp only [value, MinimalPredicates.separated_rename]
  rfl

theorem existsValue_rename {m k} (w : Fin m) (ρ : Fin m → Fin k) :
    (existsValue w).rename ρ = existsValue (ρ w) := by
  simp only [existsValue, Formula.rename, value_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem value_at {m} {Γ : Context m} (w V r : Fin m) (hv : Derives Γ (value w V)) :
    Derives Γ ((Formula.mem r V).iff ((Formula.mem r w).conj (HornLookupConditionSyntax.condition w r))) := by
  have hh := MinimalPredicates.specialize_separated matrix (one w) w V r hv
  exact of_eq (by simp only [MinimalPredicates.satisfying, matrix_pred, one]) hh

end PPAC.Migration.Internal.HornUniversalTraceSyntax
