import PPAC.Migration.SourceStatements
import YesMetaZFC.SetTheory.Language
import YesMetaZFC.Model.FirstOrder.Semantics

/-! 源末变量 binder 到原生首变量 binder 的翻译。仅作语言桥接。 -/
namespace PPAC.Migration
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder
open YesMetaZFC.SetTheory
namespace Translation
abbrev Scope := FirstOrder.SortContext ℒ

def lift {S : Type u} {sort : S} {n : Nat} {bound : List S}
    (ρ : Fin n → Variable bound sort) :
    Fin (n + 1) → Variable (sort :: bound) sort :=
  Fin.lastCases .here (fun i => .there (ρ i))

def formula {n : Nat} {bound : Scope}
    (ρ : Fin n → Variable bound SetSort.set) :
    Source.Formula n → FirstOrder.Formula ℒ bound []
  | .bot => .falsum
  | .mem x y => .rel RelationSymbol.membership
      (.cons (.bvar (ρ x)) (.cons (.bvar (ρ y)) .nil))
  | .equal x y => .equal (.bvar (ρ x)) (.bvar (ρ y))
  | .imp p q => .imp (formula ρ p) (formula ρ q)
  | .conj p q => .conj (formula ρ p) (formula ρ q)
  | .disj p q => .disj (formula ρ p) (formula ρ q)
  | .all p => .forallE SetSort.set (formula (lift ρ) p)
  | .ex p => .existsE SetSort.set (formula (lift ρ) p)

def sentence (p : Source.Sentence) : FirstOrder.Sentence ℒ :=
  formula Fin.elim0 p

/-- 新 binder 恰好解释源末变量，其他变量保持原赋值。 -/
theorem lift_assignment {σ : Signature.{u, v, w}} (M : FirstOrder.Structure σ)
    {n : Nat} {sort : σ.SortSymbol} {bound : FirstOrder.SortContext σ}
    (env : FirstOrder.Env M bound []) (ρ : Fin n → Variable bound sort)
    (x : M.Carrier sort) :
    (fun i => (env.pushBound x).boundVal (lift ρ i)) =
      Fin.lastCases x (fun i => env.boundVal (ρ i)) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa only [lift, Fin.lastCases_last] using FirstOrder.Env.pushBound_bound_here env x
  · simpa only [lift, Fin.lastCases_castSucc] using FirstOrder.Env.pushBound_bound_there env x (ρ j)

/-- 任意关系结构上的全公式保真；不要求传递、外部良基或 ZF。 -/
theorem realizes_formula (M : FirstOrder.Structure ℒ)
    {n : Nat} {bound : Scope} (ρ : Fin n → Variable bound SetSort.set)
    (env : FirstOrder.Env M bound []) (p : Source.Formula n) :
    FirstOrder.Formula.satisfies env (formula ρ p) ↔
      Source.Formula.Realize
        (fun a b => M.relInterp RelationSymbol.membership (.cons a (.cons b .nil)))
        (fun i => env.boundVal (ρ i)) p := by
  induction p generalizing bound with
  | bot => rfl
  | mem => rfl
  | equal => rfl
  | imp p q hp hq => simp only [formula, FirstOrder.Formula.satisfies, Source.Formula.Realize, hp, hq]
  | conj p q hp hq => simp only [formula, FirstOrder.Formula.satisfies, Source.Formula.Realize, hp, hq]
  | disj p q hp hq => simp only [formula, FirstOrder.Formula.satisfies, Source.Formula.Realize, hp, hq]
  | all p hp =>
      change (∀ x, FirstOrder.Formula.satisfies (env.pushBound x) (formula (lift ρ) p)) ↔ _
      apply forall_congr'
      intro x
      have h := hp (lift ρ) (env.pushBound x)
      have e := lift_assignment M env ρ x
      exact h.trans (Iff.of_eq (congrArg (fun v =>
        Source.Formula.Realize
          (fun a b => M.relInterp RelationSymbol.membership (.cons a (.cons b .nil))) v p) e))
  | ex p hp =>
      change (∃ x, FirstOrder.Formula.satisfies (env.pushBound x) (formula (lift ρ) p)) ↔ _
      apply exists_congr
      intro x
      have h := hp (lift ρ) (env.pushBound x)
      have e := lift_assignment M env ρ x
      exact h.trans (Iff.of_eq (congrArg (fun v =>
        Source.Formula.Realize
          (fun a b => M.relInterp RelationSymbol.membership (.cons a (.cons b .nil))) v p) e))

theorem realizes_sentence (M : FirstOrder.Structure ℒ) (p : Source.Sentence) :
    FirstOrder.Formula.satisfies (FirstOrder.Env.empty (M := M)) (sentence p) ↔
      Source.Formula.Realize
        (fun a b => M.relInterp RelationSymbol.membership (.cons a (.cons b .nil)))
        Fin.elim0 p := by
  have h := realizes_formula M Fin.elim0 FirstOrder.Env.empty p
  have he : (fun i : Fin 0 => (FirstOrder.Env.empty (M := M)).boundVal (Fin.elim0 i)) =
      (Fin.elim0 : Fin 0 → M.Carrier SetSort.set) := by
    funext i
    exact Fin.elim0 i
  rw [he] at h
  exact h
end Translation
end PPAC.Migration
