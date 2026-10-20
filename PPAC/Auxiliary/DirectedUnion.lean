/-! 从原 Repair/Forcing 中提取的纯关系有向并辅助。
保留原 PPAC.Repair 命名空间便于来源核对；没有实际 forcing 或内部集合解释。 -/
namespace PPAC.Repair
def jrelOf {B A : Type} {C : Type} (rel : C → B → A → Prop) (G : C → Prop)
    (b : B) (a : A) : Prop :=
  ∃ p : C, G p ∧ rel p b a

/-- The union is functional, given per-condition functionality and
directedness of `G`. -/
theorem jrelOf_fun {B A : Type} {C : Type} {rel : C → B → A → Prop} {G : C → Prop}
    (hfuni : ∀ p b a a', rel p b a → rel p b a' → a = a')
    (hdir : ∀ p p', G p → G p' → ∃ p'' : C, G p'' ∧
      (∀ b a, rel p b a → rel p'' b a) ∧ (∀ b a, rel p' b a → rel p'' b a))
    {b : B} {a a' : A} (h₁ : jrelOf rel G b a) (h₂ : jrelOf rel G b a') : a = a' := by
  cases h₁ with
  | intro p hp =>
    cases h₂ with
    | intro p' hp' =>
      cases hdir p p' hp.1 hp'.1 with
      | intro p'' hp'' =>
        exact hfuni p'' b a a' (hp''.2.1 b a hp.2) (hp''.2.2 b a' hp'.2)

/-- The union stays inside `q`'s section constraint. -/
theorem jrelOf_sec {B A : Type} {q : A → B} {C : Type} {rel : C → B → A → Prop}
    {G : C → Prop} (hsec : ∀ p b a, rel p b a → q a = b)
    {b : B} {a : A} (h : jrelOf rel G b a) : q a = b := by
  cases h with
  | intro p hp => exact hsec p b a hp.2

/-- The union is injective as a relation (backward), via the section
constraint. -/
theorem jrelOf_inj {B A : Type} {q : A → B} {C : Type} {rel : C → B → A → Prop}
    {G : C → Prop} (hsec : ∀ p b a, rel p b a → q a = b)
    {b b' : B} {a : A} (h₁ : jrelOf rel G b a) (h₂ : jrelOf rel G b' a) : b = b' := by
  cases h₁ with
  | intro p hp =>
    cases h₂ with
    | intro p' hp' =>
      exact (hsec p b a hp.2).symm.trans (hsec p' b' a hp'.2)

/-- The union is injective as a relation (backward), via per-condition
backward injectivity and directedness (for free partial injections, where
no section constraint is available). -/
theorem jrelOf_injDir {B A : Type} {C : Type} {rel : C → B → A → Prop} {G : C → Prop}
    (hinj : ∀ p b b' a, rel p b a → rel p b' a → b = b')
    (hdir : ∀ p p', G p → G p' → ∃ p'' : C, G p'' ∧
      (∀ b a, rel p b a → rel p'' b a) ∧ (∀ b a, rel p' b a → rel p'' b a))
    {b b' : B} {a : A} (h₁ : jrelOf rel G b a) (h₂ : jrelOf rel G b' a) : b = b' := by
  cases h₁ with
  | intro p hp =>
    cases h₂ with
    | intro p' hp' =>
      cases hdir p p' hp.1 hp'.1 with
      | intro p'' hp'' =>
        exact hinj p'' b b' a (hp''.2.1 b a hp.2) (hp''.2.2 b' a hp'.2)

/-- Meeting the density requirement `∃ a, rel p b a` makes the union
total at `b`. -/
theorem jrelOf_total {B A : Type} {C : Type} {rel : C → B → A → Prop} {G : C → Prop}
    {b : B} (hmeet : ∃ p : C, G p ∧ ∃ a, rel p b a) : ∃ a, jrelOf rel G b a := by
  cases hmeet with
  | intro p hp =>
    cases hp.2 with
    | intro a ha => exact ⟨a, p, hp.1, ha⟩

/-! ## Finite partial sections (list representation) -/


end PPAC.Repair
