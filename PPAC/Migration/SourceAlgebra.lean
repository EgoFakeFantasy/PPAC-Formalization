import PPAC.Migration.SourceDerivation
import PPAC.Migration.ReverseSyntax

/-! 源规则的结构句法与派生规则；不增加输入规则，不修改目标可信核。 -/
namespace PPAC.Migration.SourceAlgebra
open Source

theorem lift_comp {n m k} (r : Fin n → Fin m) (s : Fin m → Fin k) :
    (fun i => Formula.liftRen s (Formula.liftRen r i)) = Formula.liftRen (fun i => s (r i)) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;>
    simp only [Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem rename_comp {n m k} (p : Formula n) (r : Fin n → Fin m) (s : Fin m → Fin k) :
    (p.rename r).rename s = p.rename (fun i => s (r i)) := by
  induction p generalizing m k with
  | bot | mem | equal => rfl
  | imp p q ihp ihq | conj p q ihp ihq | disj p q ihp ihq =>
      simp only [Formula.rename, ihp, ihq]
  | all p ih | ex p ih => simp only [Formula.rename, ih, lift_comp]

theorem rename_raise {n m} (p : Formula n) (r : Fin n → Fin m) :
    p.raise.rename (Formula.liftRen r) = (p.rename r).raise := by
  simp only [Formula.raise, rename_comp]
  congr 1
  funext i
  exact Fin.lastCases_castSucc i

theorem instantiate_raise {n} (p : Formula n) (t : Fin n) : p.raise.instantiate t = p := by
  rw [Formula.instantiate, Formula.raise, rename_comp]
  have he : (fun i : Fin n => Fin.lastCases t id i.castSucc) = id := by
    funext i
    exact Fin.lastCases_castSucc i
  rw [he, Reverse.source_rename_id]

theorem instantiate_rename {n m} (p : Formula (n+1)) (r : Fin n → Fin m) (t : Fin n) :
    (p.rename (Formula.liftRen r)).instantiate (r t) = (p.instantiate t).rename r := by
  simp only [Formula.instantiate, rename_comp]
  congr 1
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;>
    simp only [Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]

theorem closed_rename {m n} (p : Sentence) (r : Fin m → Fin n) :
    (p.rename (Fin.elim0 : Fin 0 → Fin m)).rename r = p.rename Fin.elim0 := by
  rw [rename_comp]
  congr 1
  funext i
  exact Fin.elim0 i

/-- 由全称闭合句在任意源变量环境中实例化全部参数。 -/
theorem specialize_close {m n} {Γ : Context m} (p : Formula n) (ρ : Fin n → Fin m)
    (h : Derives Γ (p.close.rename Fin.elim0)) : Derives Γ (p.rename ρ) := by
  induction n with
  | zero =>
      have e : ρ = Fin.elim0 := by funext i; exact Fin.elim0 i
      simpa only [Formula.close, e] using h
  | succ n ih =>
      have hall := ih (.all p) (fun i => ρ i.castSucc) h
      have hi := Derives.allE (ρ (Fin.last n)) hall
      change Derives Γ ((p.rename (Formula.liftRen (fun i => ρ i.castSucc))).instantiate (ρ (Fin.last n))) at hi
      rw [Formula.instantiate, rename_comp] at hi
      have e : (fun i => Fin.lastCases (ρ (Fin.last n)) id
          (Formula.liftRen (fun i => ρ i.castSucc) i)) = ρ := by
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i <;>
          simp only [Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
      simpa only [e] using hi

theorem theory_at_raise (T : Theory) (n : Nat) :
    Context.image Formula.raise (T.at n) = T.at (n+1) := by
  funext q
  apply propext
  constructor
  · rintro ⟨r, ⟨p, hp, rfl⟩, rfl⟩
    exact ⟨p, hp, (closed_rename p Fin.castSucc).symm⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p.rename Fin.elim0, ⟨p, hp, rfl⟩, closed_rename p Fin.castSucc⟩

/-- 源理论只有闭公理；参数闭合直接使用原19规则中的allI。 -/
theorem close_derives {T : Theory} {n} {p : Formula n} (h : Derives (T.at n) p) :
    Derives (T.at 0) p.close := by
  induction n with
  | zero => exact h
  | succ n ih =>
      apply ih
      apply Derives.allI
      rw [theory_at_raise]
      exact h
end PPAC.Migration.SourceAlgebra
