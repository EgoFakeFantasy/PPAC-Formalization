import PPAC.Migration.Internal.ObjectFormulaCodeConstruction

/-! 原有限字段向量的完整位置析取；索引和值候选均为对象变量，不是宿主解码结果。 -/
namespace PPAC.Migration.Internal.SyntaxPositionSyntax
open Source SourceAlgebra SourceLogic SyntaxNumeralSyntax

def below {m} : Nat → Fin m → Formula m
  | 0, _ => .bot
  | k+1, i => (below k i).disj (numeral k i)

def positions {m} : (k : Nat) → (Fin k → Fin m) → Fin m → Fin m → Formula m
  | 0, _, _, _ => .bot
  | k+1, xs, i, y => (positions k (fun j => xs j.castSucc) i y).disj
      ((numeral k i).conj (.equal y (xs (Fin.last k))))

theorem below_rename {m n} (k : Nat) (i : Fin m) (r : Fin m → Fin n) :
    (below k i).rename r = below k (r i) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [below, Formula.rename, numeral_rename, ih]

theorem positions_rename {m n} (k : Nat) (xs : Fin k → Fin m) (i y : Fin m) (r : Fin m → Fin n) :
    (positions k xs i y).rename r = positions k (fun j => r (xs j)) (r i) (r y) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [positions, Formula.rename, numeral_rename, ih]

theorem intro_below {m} {Γ : Context m} (k : Nat) (j : Fin k) (i : Fin m)
    (hi : Derives Γ (numeral j.val i)) : Derives Γ (below k i) := by
  induction k with
  | zero => exact Fin.elim0 j
  | succ k ih =>
    revert hi
    refine Fin.lastCases ?_ (fun a => ?_) j
    · intro hi; exact .disjR hi
    · intro hi; exact .disjL (ih a hi)

theorem intro_position {m} {Γ : Context m} (k : Nat) (xs : Fin k → Fin m) (j : Fin k) (i y : Fin m)
    (hi : Derives Γ (numeral j.val i)) (hy : Derives Γ (.equal y (xs j))) :
    Derives Γ (positions k xs i y) := by
  induction k with
  | zero => exact Fin.elim0 j
  | succ k ih =>
    revert hi hy
    refine Fin.lastCases ?_ (fun a => ?_) j
    · intro hi hy; exact .disjR (.conjI hi hy)
    · intro hi hy; exact .disjL (ih (fun q => xs q.castSucc) a hi hy)

theorem below_imp {m} {Γ : Context m} (k : Nat) (i : Fin m) (q : Formula m)
    (hh : ∀ j : Fin k, Derives Γ ((numeral j.val i).imp q)) :
    Derives Γ ((below k i).imp q) := by
  induction k with
  | zero => exact .impI (.botE (.hyp (Or.inl rfl)))
  | succ k ih =>
    exact FormulaCodeCaseLogic.disj_imp (ih (fun j => hh j.castSucc)) (hh (Fin.last k))

theorem positions_imp {m} {Γ : Context m} (k : Nat) (xs : Fin k → Fin m) (i y : Fin m) (q : Formula m)
    (hh : ∀ j : Fin k, Derives Γ (((numeral j.val i).conj (.equal y (xs j))).imp q)) :
    Derives Γ ((positions k xs i y).imp q) := by
  induction k with
  | zero => exact .impI (.botE (.hyp (Or.inl rfl)))
  | succ k ih =>
    exact FormulaCodeCaseLogic.disj_imp (ih (fun a => xs a.castSucc) (fun j => hh j.castSucc)) (hh (Fin.last k))
end PPAC.Migration.Internal.SyntaxPositionSyntax
