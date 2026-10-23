import PPAC.Migration.Internal.OriginalOperationFrameRules

/-! 固定有限全称块仅由原allI／allE构成，用于把所有运行参数保留在对象公式内部。 -/
namespace PPAC.Migration.Internal.OriginalUniversalBlock
open Source SourceAlgebra SourceLogic HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)

def allMany {m} : (k : Nat) → Formula (m+k) → Formula m
  | 0, p => p
  | k+1, p => allMany k (.all p)

theorem allMany_rename {m j} (k : Nat) (p : Formula (m+k)) (ρ : Fin m → Fin j) :
    (allMany k p).rename ρ = allMany k (p.rename (lift k ρ)) := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih (.all p)

theorem intro_many {m} {Γ : Context m} (k : Nat) (p : Formula (m+k))
    (hp : Derives (raisedContext k Γ) p) : Derives Γ (allMany k p) := by
  induction k with
  | zero => exact hp
  | succ k ih => exact ih (.all p) (.allI hp)

theorem at_many {m} {Γ : Context m} (k : Nat) (p : Formula (m+k)) (env : Fin k → Fin m)
    (hp : Derives Γ (allMany k p)) : Derives Γ (p.rename (assign k env)) := by
  induction k with
  | zero => exact of_eq (Reverse.source_rename_id p).symm hp
  | succ k ih =>
    have he := Derives.allE (env (Fin.last k)) (ih (.all p) (fun i => env i.castSucc) hp)
    exact of_eq (by simp only [Formula.instantiate, rename_comp]; exact congrArg (fun ρ => p.rename ρ) (assign_step k env)) he

end PPAC.Migration.Internal.OriginalUniversalBlock
