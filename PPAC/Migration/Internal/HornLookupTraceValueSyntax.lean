import PPAC.Migration.Internal.HornLookupSoundInduction

/-! 全部成功原lookup行的对象定义和实际Separation集合值，不选择外部运行轨迹。 -/
namespace PPAC.Migration.Internal.HornLookupTraceValueSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax HornLookupRowSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)

def goodBody {m} (w r : Fin m) : Formula (m+3) :=
  (row (old 3 w) (slot 3 0) (slot 3 1) (slot 3 2) (old 3 r)).conj
    (LookupTableExecutionSyntax.executed (old 3 w) (slot 3 0) (slot 3 1) (slot 3 2))

def goodRow {m} (w r : Fin m) : Formula m := existsMany 3 (goodBody w r)

def matrix : Formula 2 := goodRow (0 : Fin 1).castSucc (Fin.last 1)

def one {m} (w : Fin m) : Fin 1 → Fin m := fun _ => w

def value {m} (w R : Fin m) : Formula m := MinimalPredicates.separated matrix (one w) w R

def existsValue {m} (w : Fin m) : Formula m := .ex (value w.castSucc (Fin.last m))

theorem goodBody_lift {m k} (w r : Fin m) (ρ : Fin m → Fin k) :
    (goodBody w r).rename (lift 3 ρ) = goodBody (ρ w) (ρ r) := by
  simp only [goodBody, Formula.rename, row_rename, LookupTableExecutionSyntax.executed_rename, lift_old, lift_slot]

theorem goodRow_rename {m k} (w r : Fin m) (ρ : Fin m → Fin k) :
    (goodRow w r).rename ρ = goodRow (ρ w) (ρ r) := by simp only [goodRow, existsMany_rename, goodBody_lift]

theorem matrix_pred {m} (ρ : Fin 1 → Fin m) (r : Fin m) : MinimalPredicates.pred matrix ρ r = goodRow (ρ 0) r := by
  simp only [matrix, MinimalPredicates.pred, goodRow_rename, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem value_rename {m k} (w R : Fin m) (ρ : Fin m → Fin k) :
    (value w R).rename ρ = value (ρ w) (ρ R) := by
  simp only [value, MinimalPredicates.separated_rename]
  rfl

theorem existsValue_rename {m k} (w : Fin m) (ρ : Fin m → Fin k) :
    (existsValue w).rename ρ = existsValue (ρ w) := by
  simp only [existsValue, Formula.rename, value_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_good {m} {Γ : Context m} (w n i y r : Fin m) (hr : Derives Γ (row w n i y r))
    (he : Derives Γ (LookupTableExecutionSyntax.executed w n i y)) : Derives Γ (goodRow w r) := by
  apply HornBinderRules.intro_many 3 (goodBody w r) (OriginalLookupExpr.rowFields n i y)
  exact of_eq (by simp only [goodBody, Formula.rename, row_rename, LookupTableExecutionSyntax.executed_rename, assign_old, assign_slot]; rfl) (.conjI hr he)

theorem value_at {m} {Γ : Context m} (w R r : Fin m) (hv : Derives Γ (value w R)) :
    Derives Γ ((Formula.mem r R).iff ((Formula.mem r w).conj (goodRow w r))) := by
  have hh := MinimalPredicates.specialize_separated matrix (one w) w R r hv
  exact of_eq (by simp only [MinimalPredicates.satisfying, matrix_pred, one]) hh

end PPAC.Migration.Internal.HornLookupTraceValueSyntax
