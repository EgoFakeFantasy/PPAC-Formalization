import Std
/-! 源有限变量语法；末变量绑定。固定来源与许可证见 docs/SOURCE_LOCK.json、NOTICE。
本摘录不复制源 Derives，也不替换 YesMetaZFC 推导核。 -/
namespace PPAC.Migration.Source
inductive Formula : Nat → Type where
  | bot {n} : Formula n
  | mem {n} (x y : Fin n) : Formula n
  | equal {n} (x y : Fin n) : Formula n
  | imp {n} (p q : Formula n) : Formula n
  | conj {n} (p q : Formula n) : Formula n
  | disj {n} (p q : Formula n) : Formula n
  | all {n} (p : Formula (n + 1)) : Formula n
  | ex {n} (p : Formula (n + 1)) : Formula n
  deriving DecidableEq

namespace Formula

abbrev neg {n} (p : Formula n) : Formula n := p.imp .bot
abbrev iff {n} (p q : Formula n) : Formula n := (p.imp q).conj (q.imp p)

/-- Under a binder, a renaming leaves the newly bound variable bound. -/
def liftRen {n m} (r : Fin n → Fin m) : Fin (n + 1) → Fin (m + 1) :=
  Fin.lastCases (Fin.last m) (fun i => (r i).castSucc)

/-- Capture-avoiding renaming; in this relational language all terms are variables. -/
def rename {n m} (r : Fin n → Fin m) : Formula n → Formula m
  | .bot => .bot
  | .mem x y => .mem (r x) (r y)
  | .equal x y => .equal (r x) (r y)
  | .imp p q => .imp (rename r p) (rename r q)
  | .conj p q => .conj (rename r p) (rename r q)
  | .disj p q => .disj (rename r p) (rename r q)
  | .all p => .all (rename (liftRen r) p)
  | .ex p => .ex (rename (liftRen r) p)

abbrev raise {n} (p : Formula n) : Formula (n + 1) := rename Fin.castSucc p

/-- Substitution of a variable term for the variable just quantified. -/
def instantiate {n} (p : Formula (n + 1)) (x : Fin n) : Formula n :=
  rename (Fin.lastCases x id) p

/-- Universal closure of all the free variables. -/
def close : {n : Nat} → Formula n → Formula 0
  | 0, p => p
  | _ + 1, p => close (.all p)

end Formula

abbrev Sentence := Formula 0

namespace Formula
def Realize {M : Type u} (E : M → M → Prop) {n} (v : Fin n → M) : Formula n → Prop
  | .bot => False
  | .mem x y => E (v x) (v y)
  | .equal x y => v x = v y
  | .imp p q => Realize E v p → Realize E v q
  | .conj p q => Realize E v p ∧ Realize E v q
  | .disj p q => Realize E v p ∨ Realize E v q
  | .all p => ∀ x : M, Realize E (Fin.lastCases x v) p
  | .ex p => ∃ x : M, Realize E (Fin.lastCases x v) p
end Formula
end PPAC.Migration.Source
