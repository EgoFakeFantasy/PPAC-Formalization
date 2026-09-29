/-
PPAC/Repair/Forcing.lean — Batch 3, semantic forcing primitives.

Minimal host-layer machinery for the repair-forcing notes (sources:
`Feferman可数部分注入修复直接恢复AC_核查.md`, `定向枚举截面修复与完美集障碍_核查.md`,
`可数闭非截面注入修复强迫_核查.md`, all 2026-09-27, read-only research
directory). Conditions are RELATIONAL (graphs of partial functions), so
generic unions are defined without any data extraction, and the
countability bookkeeping uses the coverage form `∃ D, Countable D ∧
w : D → B` covering the domain, which is closed under the extensions used
here without any decision procedure.

BOUNDARY: `AC_omega_count` is an explicit hypothesis (the AC_ω content of
"countable union of countables is countable" in ZF+DC); it is never proven
here and never declared an axiom. Filters are represented by membership
predicates with an explicit directedness hypothesis. Finite sums of
countable types and injective pullbacks of countability are PROVED here
(Prop-level elimination, no choice).

Axiom discipline: no `sorry`, no custom `axiom`, no `Classical.choice`.
-/

import Init
import PPAC.Choice.Splitting

namespace PPAC.Repair

/-! ## Countability bookkeeping -/

/-- Countability: some injection into `Nat`. This is the batch's own
Prop-level rendition of "injectable into ω"; Lean core (without batteries)
has no `Countable` class. -/
def Countable (X : Type) : Prop := ∃ f : X → Nat, Function.Injective f

/-- Data content of AC_ω needed for σ-closure: countably many countable
types have a countable sigma-type. Hypothesis only. -/
def AC_omega_count : Prop :=
  ∀ (D : Nat → Type), (∀ n, Countable (D n)) → Countable (Σ n : Nat, D n)

/-- Countable types are closed under finite sums (Prop-level elimination
of the enumerations; no choice). -/
theorem countable_sum {D₁ D₂ : Type} (h₁ : Countable D₁) (h₂ : Countable D₂) :
    Countable (D₁ ⊕ D₂) := by
  cases h₁ with
  | intro e₁ he₁ =>
    cases h₂ with
    | intro e₂ he₂ =>
      exists fun x => Sum.elim (fun d => 2 * e₁ d) (fun d => 2 * e₂ d + 1) x
      intro x y hxy
      cases x with
      | inl x =>
        cases y with
        | inl y =>
          have h : 2 * e₁ x = 2 * e₁ y := hxy
          exact congrArg Sum.inl (he₁ (Nat.eq_of_mul_eq_mul_left (by decide) h))
        | inr y =>
          have h : 2 * e₁ x = 2 * e₂ y + 1 := hxy
          exfalso
          cases Nat.le_total (e₁ x) (e₂ y) with
          | inl hl => omega
          | inr hr => omega
      | inr x =>
        cases y with
        | inl y =>
          have h : 2 * e₂ x + 1 = 2 * e₁ y := hxy
          exfalso
          cases Nat.le_total (e₂ x) (e₁ y) with
          | inl hl => omega
          | inr hr => omega
        | inr y =>
          have h : 2 * e₂ x + 1 = 2 * e₂ y + 1 := hxy
          have h2 : e₂ x = e₂ y := by omega
          exact congrArg Sum.inr (he₂ h2)
/-- A type injecting into a countable type is countable. -/
theorem countable_of_injective {X Y : Type} (f : X → Y) (hinj : Function.Injective f)
    (hY : Countable Y) : Countable X := by
  cases hY with
  | intro e he =>
    exact ⟨fun x => e (f x), fun x x' hx => hinj (he hx)⟩

/-! ## The generic union of a directed family of conditions -/

/-- The generic union of a directed family `G` of `rel`-conditions, as a
relation (the graph of `⋃ G`). -/
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

/-- A finite partial section of `q : A → B`: a list of pairs, each pair
satisfying `q a = b`, with no repeated first coordinate. Backward
injectivity is free (`q a = b` and `q a = b'` give `b = b'`). -/
structure SecList (B A : Type) (q : A → B) where
  l : List (B × A)
  sec : ∀ b a, (b, a) ∈ l → q a = b
  funi : ∀ b a a', (b, a) ∈ l → (b, a') ∈ l → a = a'

/-- Extension order on finite sections (stronger = more pairs). -/
def SecListLe {B A : Type} {q : A → B} (p p' : SecList B A q) : Prop :=
  ∀ b a, (b, a) ∈ p.l → (b, a) ∈ p'.l

/-- Appending pairs to a finite section: if the news are section pairs,
compatible with the old pairs and internally functional, the appended list
is a valid stronger condition. -/
theorem secList_grow {B A : Type} {q : A → B} (p : SecList B A q)
    (news : List (B × A))
    (hsec : ∀ b a, (b, a) ∈ news → q a = b)
    (hold : ∀ b a a', (b, a) ∈ p.l → (b, a') ∈ news → a = a')
    (hnew : ∀ b a a', (b, a) ∈ news → (b, a') ∈ news → a = a') :
    ∃ p' : SecList B A q, SecListLe p p' ∧ ∀ x, x ∈ news → x ∈ p'.l := by
  refine ⟨⟨p.l ++ news, ?_, ?_⟩, ?_, ?_⟩
  · intro b a hba
    show q a = b
    rw [List.mem_append] at hba
    cases hba with
    | inl h => exact p.sec b a h
    | inr h => exact hsec b a h
  · intro b a a' h₁ h₂
    show a = a'
    rw [List.mem_append] at h₁ h₂
    cases h₁ with
    | inl h₁ =>
      cases h₂ with
      | inl h₂ => exact p.funi b a a' h₁ h₂
      | inr h₂ => exact hold b a a' h₁ h₂
    | inr h₁ =>
      cases h₂ with
      | inl h₂ => exact (hold b a' a h₂ h₁).symm
      | inr h₂ => exact hnew b a a' h₁ h₂
  · intro b a hba
    show (b, a) ∈ p.l ++ news
    rw [List.mem_append]
    exact Or.inl hba
  · intro x hx
    show x ∈ p.l ++ news
    rw [List.mem_append]
    exact Or.inr hx

/-! ## Countable partial sections (relational, coverage-form) -/

/-- A countable cover: a countable type `D` whose image under `w`
covers the relevant elements. -/
structure Cover (B : Type) where
  D : Type
  hD : Countable D
  w : D → B

/-- A countable partial section of `q : A → B`, relationally, with the
domain covered by a countable cover. -/
structure SecCnt (B A : Type) (q : A → B) where
  rel : B → A → Prop
  funi : ∀ b a a', rel b a → rel b a' → a = a'
  sec : ∀ b a, rel b a → q a = b
  cnt : ∃ c : Cover B, ∀ b a, rel b a → ∃ d, c.w d = b

/-- Extension order on countable sections. -/
def SecCntLe {B A : Type} {q : A → B} (p p' : SecCnt B A q) : Prop :=
  ∀ b a, p.rel b a → p'.rel b a

/-- Countable partial functions into `X` (target of the parity
projection). -/
structure CntPartFun (I X : Type) where
  rel : I → X → Prop
  funi : ∀ i x x', rel i x → rel i x' → x = x'
  cnt : ∃ c : Cover I, ∀ i x, rel i x → ∃ d, c.w d = i

/-- Extension order on countable partial functions. -/
def CPFLe {I X : Type} (p p' : CntPartFun I X) : Prop :=
  ∀ i x, p.rel i x → p'.rel i x

end PPAC.Repair
