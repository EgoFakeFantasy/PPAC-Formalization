import PPAC.Migration.Internal.ObjectStructuralTreeEncode

/-! 有限语法标签的纯对象数码；外部k仅索引有限公式，候选值是任意内部集合。 -/
namespace PPAC.Migration.Internal.SyntaxNumeralSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax

def numeral {m} : Nat → Fin m → Formula m
  | 0, x => empty x
  | k+1, x => .ex ((numeral k (Fin.last m)).conj (successor x.castSucc (Fin.last m)))

def existsNumeral {m} (w : Fin m) (k : Nat) : Formula m := .ex
  ((Formula.mem (Fin.last m) w.castSucc).conj (numeral k (Fin.last m)))

theorem numeral_rename {m n} (k : Nat) (x : Fin m) (s : Fin m → Fin n) : (numeral k x).rename s = numeral k (s x) := by
  induction k generalizing m n with
  | zero => exact empty_rename x s
  | succ k ih => simp only [numeral, Formula.rename, ih, successor_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem existsNumeral_rename {m n} (w : Fin m) (k : Nat) (s : Fin m → Fin n) : (existsNumeral w k).rename s = existsNumeral (s w) k := by
  simp only [existsNumeral, Formula.rename, numeral_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_succ {m} {Γ : Context m} (k : Nat) (x p : Fin m) (hp : Derives Γ (numeral k p))
    (hs : Derives Γ (successor x p)) : Derives Γ (numeral (k+1) x) := by
  apply Derives.exI p
  simp only [Formula.instantiate, Formula.rename, numeral_rename, successor_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI hp hs

theorem eliminate_succ {m} {Γ : Context m} (k : Nat) (x : Fin m) (q : Formula m) (hx : Derives Γ (numeral (k+1) x))
    (hc : Derives (Context.add ((numeral k (Fin.last m)).conj (successor x.castSucc (Fin.last m))) (Context.image Formula.raise Γ)) q.raise) : Derives Γ q := .exE hx hc

theorem output_subst {m} {Γ : Context m} (k : Nat) (x y : Fin m) (he : Derives Γ (.equal x y))
    (hx : Derives Γ (numeral k x)) : Derives Γ (numeral k y) := by
  have hi : Derives Γ ((numeral k (Fin.last m)).instantiate x) := by
    simpa only [Formula.instantiate, numeral_rename, Fin.lastCases_last] using hx
  have ho := Derives.eqSubst (numeral k (Fin.last m)) he hi
  simpa only [Formula.instantiate, numeral_rename, Fin.lastCases_last] using ho
end PPAC.Migration.Internal.SyntaxNumeralSyntax
