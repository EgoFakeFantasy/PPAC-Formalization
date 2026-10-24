import PPAC.Migration.Internal.ProofTreeTraceExtension

/-! 全部实际原闭轨迹根的Separation集合；仅用于构造见证，不改变独立原执行定义。 -/
namespace PPAC.Migration.Internal.ProofTreeUniversalSyntax
open Source SourceAlgebra SourceLogic
open SyntaxRenameQuerySyntax (of_eq)

def matrix (test : Formula 1) : Formula 2 := ProofTreeTraceSyntax.condition test (0 : Fin 1).castSucc (Fin.last 1)

def one {m} (w : Fin m) : Fin 1 → Fin m := fun _ => w

def value {m} (test : Formula 1) (w V : Fin m) : Formula m := MinimalPredicates.separated (matrix test) (one w) w V

def existsValue {m} (test : Formula 1) (w : Fin m) : Formula m := .ex (value test w.castSucc (Fin.last m))

theorem matrix_pred {m} (test : Formula 1) (ρ : Fin 1 → Fin m) (r : Fin m) :
    MinimalPredicates.pred (matrix test) ρ r = ProofTreeTraceSyntax.condition test (ρ 0) r := by
  simp only [matrix, MinimalPredicates.pred, ProofTreeTraceSyntax.condition_rename test, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem value_rename {m k} (test : Formula 1) (w V : Fin m) (ρ : Fin m → Fin k) :
    (value test w V).rename ρ = value test (ρ w) (ρ V) := by
  simp only [value, MinimalPredicates.separated_rename]
  rfl

theorem existsValue_rename {m k} (test : Formula 1) (w : Fin m) (ρ : Fin m → Fin k) :
    (existsValue test w).rename ρ = existsValue test (ρ w) := by
  simp only [existsValue, Formula.rename, value_rename test, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem value_at {m} {Γ : Context m} (test : Formula 1) (w V r : Fin m) (hv : Derives Γ (value test w V)) :
    Derives Γ ((Formula.mem r V).iff ((Formula.mem r w).conj (ProofTreeTraceSyntax.condition test w r))) := by
  have hh := MinimalPredicates.specialize_separated (matrix test) (one w) w V r hv
  exact of_eq (by simp only [MinimalPredicates.satisfying, matrix_pred test, one]) hh

end PPAC.Migration.Internal.ProofTreeUniversalSyntax
