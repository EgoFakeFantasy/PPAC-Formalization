import PPAC.Migration.SourceSyntax
/-! 固定OpenAI源自然演绎的19条输入规则；Set记号展开为谓词。
它不是目标可信核；输出证书只使用原YesMetaZFC HilbertDerivation。 -/
namespace PPAC.Migration.Source
abbrev Context (n : Nat) := Formula n → Prop
namespace Context
def add {n} (p : Formula n) (Γ : Context n) : Context n :=
  fun q => q = p ∨ Γ q
def image {n m} (f : Formula n → Formula m) (Γ : Context n) : Context m :=
  fun q => ∃ p, Γ p ∧ f p = q
end Context
inductive Derives : {n : Nat} → Context n → Formula n → Prop where
  | hyp {n} {Γ : Context n} {p} : Γ p → Derives Γ p
  | weaken {n} {Γ Δ : Context n} {p} :
      (∀ q, Γ q → Δ q) → Derives Γ p → Derives Δ p
  | impI {n} {Γ : Context n} {p q} :
      Derives (Context.add p Γ) q → Derives Γ (.imp p q)
  | impE {n} {Γ : Context n} {p q} :
      Derives Γ (.imp p q) → Derives Γ p → Derives Γ q
  | botE {n} {Γ : Context n} {p} : Derives Γ .bot → Derives Γ p
  | classical {n} {Γ : Context n} {p} :
      Derives (Context.add p.neg Γ) .bot → Derives Γ p
  | conjI {n} {Γ : Context n} {p q} :
      Derives Γ p → Derives Γ q → Derives Γ (.conj p q)
  | conjL {n} {Γ : Context n} {p q} :
      Derives Γ (.conj p q) → Derives Γ p
  | conjR {n} {Γ : Context n} {p q} :
      Derives Γ (.conj p q) → Derives Γ q
  | disjL {n} {Γ : Context n} {p q} :
      Derives Γ p → Derives Γ (.disj p q)
  | disjR {n} {Γ : Context n} {p q} :
      Derives Γ q → Derives Γ (.disj p q)
  | disjE {n} {Γ : Context n} {p q r} :
      Derives Γ (.disj p q) → Derives (Context.add p Γ) r →
      Derives (Context.add q Γ) r → Derives Γ r
  | allI {n} {Γ : Context n} {p : Formula (n + 1)} :
      Derives (Context.image Formula.raise Γ) p → Derives Γ (.all p)
  | allE {n} {Γ : Context n} {p : Formula (n + 1)} (t : Fin n) :
      Derives Γ (.all p) → Derives Γ (p.instantiate t)
  | exI {n} {Γ : Context n} {p : Formula (n + 1)} (t : Fin n) :
      Derives Γ (p.instantiate t) → Derives Γ (.ex p)
  | exE {n} {Γ : Context n} {p : Formula (n + 1)} {q : Formula n} :
      Derives Γ (.ex p) → Derives (Context.add p (Context.image Formula.raise Γ)) q.raise →
      Derives Γ q
  | eqRefl {n} {Γ : Context n} (t : Fin n) : Derives Γ (.equal t t)
  | eqSubst {n} {Γ : Context n} {s t : Fin n} (p : Formula (n + 1)) :
      Derives Γ (.equal s t) → Derives Γ (p.instantiate s) →
      Derives Γ (p.instantiate t)
  | rename {n m} {Γ : Context n} {p : Formula n} (r : Fin n → Fin m) :
      Derives Γ p → Derives (Context.image (Formula.rename r) Γ) (Formula.rename r p)


abbrev Theory := Sentence → Prop
def Theory.at (T : Theory) (n : Nat) : Context n :=
  Context.image (Formula.rename Fin.elim0) T
def Consistent (T : Theory) : Prop := ∀ n, ¬ Derives (T.at n) .bot
end PPAC.Migration.Source
