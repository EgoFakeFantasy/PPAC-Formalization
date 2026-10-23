import PPAC.Migration.Internal.ObjectOriginalLookupRules

/-! 任意固定有限赋值块的原源存在量词；末槽绑定，无新推导规则。 -/
namespace PPAC.Migration.Internal.HornBinderSyntax
open Source SourceAlgebra SourceLogic

def old {m} : (n : Nat) → Fin m → Fin (m+n)
  | 0, i => i
  | n+1, i => (old n i).castSucc

def slot {m} : (n : Nat) → Fin n → Fin (m+n)
  | 0, i => Fin.elim0 i
  | n+1, i => Fin.lastCases (Fin.last (m+n)) (fun j => (slot n j).castSucc) i

def lift {m k} : (n : Nat) → (Fin m → Fin k) → Fin (m+n) → Fin (k+n)
  | 0, ρ => ρ
  | n+1, ρ => Formula.liftRen (lift n ρ)

def assign {m} : (n : Nat) → (Fin n → Fin m) → Fin (m+n) → Fin m
  | 0, _ => id
  | n+1, env => Fin.lastCases (env (Fin.last n)) (assign n (fun i => env i.castSucc))

def existsMany {m} : (n : Nat) → Formula (m+n) → Formula m
  | 0, p => p
  | n+1, p => existsMany n (.ex p)

def raisedContext {m} : (n : Nat) → Context m → Context (m+n)
  | 0, Γ => Γ
  | n+1, Γ => Context.image Formula.raise (raisedContext n Γ)

theorem lift_old {m k} (n : Nat) (ρ : Fin m → Fin k) (i : Fin m) : lift n ρ (old n i) = old n (ρ i) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [lift, old, Formula.liftRen, Fin.lastCases_castSucc, ih]

theorem lift_slot {m k} (n : Nat) (ρ : Fin m → Fin k) (i : Fin n) : lift n ρ (slot n i) = slot n i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [slot, lift, Formula.liftRen]
    · simp only [slot, Fin.lastCases_castSucc, lift, Formula.liftRen, ih]

theorem assign_old {m} (n : Nat) (env : Fin n → Fin m) (i : Fin m) : assign n env (old n i) = i := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [assign, old, Fin.lastCases_castSucc, ih]

theorem assign_slot {m} (n : Nat) (env : Fin n → Fin m) (i : Fin n) : assign n env (slot n i) = env i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [slot, assign]
    · simp only [slot, assign, Fin.lastCases_castSucc, ih]

theorem assign_step {m} (n : Nat) (env : Fin (n+1) → Fin m) :
    (fun i => Fin.lastCases (env (Fin.last n)) id (Formula.liftRen (assign n (fun j => env j.castSucc)) i)) = assign (n+1) env := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;>
    simp [Formula.liftRen, assign]

theorem existsMany_rename {m k} (n : Nat) (B : Formula (m+n)) (ρ : Fin m → Fin k) :
    (existsMany n B).rename ρ = existsMany n (B.rename (lift n ρ)) := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih (.ex B)

theorem raise_old {m} (n : Nat) (p : Formula m) : (p.rename (old n)).raise = p.rename (old (n+1)) := by
  simp only [Formula.raise, rename_comp, old]

end PPAC.Migration.Internal.HornBinderSyntax
