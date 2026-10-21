import PPAC.Migration.Internal.FormulaCodeFieldArity

/-! 原11标签及精确字段数的内部数码分类；候选标签/长度均为任意对象变量。 -/
namespace PPAC.Migration.Internal.FormulaCodeAllowedAritySyntax
open Source SourceAlgebra SourceLogic SyntaxNumeralSyntax

def expectedArity (tag : Nat) : Nat :=
  if tag = 0 ∨ tag = 1 then 0 else if tag = 2 then 3 else if tag = 3 ∨ (5 ≤ tag ∧ tag ≤ 8) then 2 else 1

def allowed {m} : Nat → Fin m → Fin m → Formula m
  | 0, _, _ => .bot
  | k+1, t, l => (allowed k t l).disj ((numeral k t).conj (numeral (expectedArity k) l))

theorem allowed_rename {m n} (k : Nat) (t l : Fin m) (r : Fin m → Fin n) :
    (allowed k t l).rename r = allowed k (r t) (r l) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [allowed, Formula.rename, numeral_rename, ih]

theorem intro_allowed {m} {Γ : Context m} (k tag : Nat) (hk : tag < k) (t l : Fin m)
    (ht : Derives Γ (numeral tag t)) (hl : Derives Γ (numeral (expectedArity tag) l)) :
    Derives Γ (allowed k t l) := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases he : tag = k
    · subst tag
      exact .disjR (.conjI ht hl)
    · exact .disjL (ih (by omega))
end PPAC.Migration.Internal.FormulaCodeAllowedAritySyntax
