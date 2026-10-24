import PPAC.Migration.Internal.PacketAffineDispatchData

/-! Separation over internal omega collects exactly the accepted roots of the explicit table. -/
namespace PPAC.Migration.Internal.HornClosedTraceValueSyntax
open Source SourceAlgebra SourceLogic
open YesMetaZFC.Automation.ObjectHorn (Rule)

def matrix (rules : List Rule) : Formula 2 := HornClosedTraceSyntax.condition rules (0 : Fin 1).castSucc (Fin.last 1)

def one {m} (w : Fin m) : Fin 1 → Fin m := fun _ => w

def value {m} (rules : List Rule) (w V : Fin m) : Formula m := MinimalPredicates.separated (matrix rules) (one w) w V

def existsValue {m} (rules : List Rule) (w : Fin m) : Formula m := .ex (value rules w.castSucc (Fin.last m))

theorem matrix_pred {m} (rules : List Rule) (ρ : Fin 1 → Fin m) (r : Fin m) :
    MinimalPredicates.pred (matrix rules) ρ r = HornClosedTraceSyntax.condition rules (ρ 0) r := by
  simp only [matrix, MinimalPredicates.pred, HornClosedTraceSyntax.condition_rename, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem value_rename {m j} (rules : List Rule) (w V : Fin m) (ρ : Fin m → Fin j) :
    (value rules w V).rename ρ = value rules (ρ w) (ρ V) := by
  simp only [value, MinimalPredicates.separated_rename]
  rfl

theorem existsValue_rename {m j} (rules : List Rule) (w : Fin m) (ρ : Fin m → Fin j) :
    (existsValue rules w).rename ρ = existsValue rules (ρ w) := by
  simp only [existsValue, Formula.rename, value_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem value_at {m} {Γ : Context m} (rules : List Rule) (w V r : Fin m) (hv : Derives Γ (value rules w V)) :
    Derives Γ ((Formula.mem r V).iff ((Formula.mem r w).conj (HornClosedTraceSyntax.condition rules w r))) := by
  have hh := MinimalPredicates.specialize_separated (matrix rules) (one w) w V r hv
  simpa only [MinimalPredicates.satisfying, matrix_pred, one] using hh

end PPAC.Migration.Internal.HornClosedTraceValueSyntax
