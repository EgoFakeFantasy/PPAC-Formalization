/-
Finite-list approximation/support lemmas and host well-order transport.
This module does not construct random forcing, a measure algebra or the
R139 counterexample. CategoryAcc is unused scaffolding; missing instances
are not evidence for a negative mathematical statement. See GAPS.md.
-/

import PPAC.Cohen.Locality

namespace PPAC.Random

open PPAC.Repair PPAC.ClassObstruction PPAC.Cohen PPAC.Choice

/-! ## 1. Finite approximation -/

/-- A random-side condition: a finite partial bit-assignment (a list of
`(index, Bool)` pairs with no repeated index). -/
structure FinBit (I : Type) where
  l : List (I × Bool)
  nd : ∀ i x x', (i, x) ∈ l → (i, x') ∈ l → x = x'

/-- Extension order on finite bit-assignments. -/
def FinBitLe {I : Type} (p p' : FinBit I) : Prop :=
  ∀ i x, (i, x) ∈ p.l → (i, x) ∈ p'.l

/-- Appending compatible fresh pairs yields a valid stronger condition. -/
theorem finBit_grow {I : Type} (p : FinBit I) (news : List (I × Bool))
    (hnd : ∀ i x x', (i, x) ∈ news → (i, x') ∈ news → x = x')
    (hold : ∀ i x x', (i, x) ∈ p.l → (i, x') ∈ news → x = x') :
    ∃ p' : FinBit I, FinBitLe p p' ∧ ∀ y, y ∈ news → y ∈ p'.l := by
  refine ⟨⟨p.l ++ news, ?_⟩, ?_, ?_⟩
  · intro i x x' h₁ h₂
    rw [List.mem_append] at h₁ h₂
    cases h₁ with
    | inl h₁ =>
      cases h₂ with
      | inl h₂ => exact p.nd i x x' h₁ h₂
      | inr h₂ => exact hold i x x' h₁ h₂
    | inr h₁ =>
      cases h₂ with
      | inl h₂ => exact (hold i x' x h₂ h₁).symm
      | inr h₂ => exact hnd i x x' h₁ h₂
  · intro i x hmem
    show (i, x) ∈ p.l ++ news
    rw [List.mem_append]
    exact Or.inl hmem
  · intro y hy
    show y ∈ p.l ++ news
    rw [List.mem_append]
    exact Or.inr hy

/-- Every element of a finite list of naturals is bounded by the
foldr-maximum (constructive, by list induction; `omega` closes the
arithmetic). -/
theorem list_le_foldr_max (L : List Nat) : ∀ m, m ∈ L → m ≤ L.foldr max 0 := by
  intro m hm
  induction L with
  | nil => cases hm
  | cons a L' ih =>
    show m ≤ max a (L'.foldr max 0)
    rw [List.mem_cons] at hm
    cases hm with
    | inl he =>
      rw [he]
      omega
    | inr hm' =>
      have h1 := ih hm'
      omega

/-- Every finite list of naturals misses some index (constructive, via the
foldr-maximum bound). -/
theorem exists_fresh_nat (L : List Nat) : ∃ n, n ∉ L := by
  refine ⟨L.foldr max 0 + 1, ?_⟩
  intro hmem
  have h1 := list_le_foldr_max L _ hmem
  omega

/-- **有限逼近.** For the random-bit conditions on `ω`, every finite
approximation requirement at a fresh index is extendable. -/
theorem rand_finite_approx (p : FinBit Nat) (i : Nat) (v : Bool)
    (hfresh : ∀ x, (i, x) ∉ p.l) :
    ∃ p' : FinBit Nat, FinBitLe p p' ∧ (i, v) ∈ p'.l := by
  cases finBit_grow p [(i, v)]
    (hnd := fun i₁ x x' h₁ h₂ => by
      have e1 : (i₁, x) = (i, v) := List.mem_singleton.mp h₁
      have e2 : (i₁, x') = (i, v) := List.mem_singleton.mp h₂
      have hx1 : x = v := congrArg Prod.snd e1
      have hx2 : x' = v := congrArg Prod.snd e2
      rw [hx1, hx2])
    (hold := fun i₁ x x' hmem_old hmem_new => by
      have e : (i₁, x') = (i, v) := List.mem_singleton.mp hmem_new
      have hb : i₁ = i := congrArg Prod.fst e
      have h' : (i, x) ∈ p.l := by rw [← hb]; exact hmem_old
      have hFalse : False := absurd h' (hfresh x)
      exact hFalse.elim)
  with
  | intro p' hp' =>
    refine ⟨p', hp'.1, ?_⟩
    exact hp'.2 (i, v) (List.mem_singleton.mpr rfl)

/-! ## 2. Support localization -/

/-- **支持定位.** Extensions keep their support inside the old support
plus a prescribed countable localization cover. -/
theorem support_localize {I : Type} (p : FinBit I) (loc : Cover I)
    (news : List (I × Bool))
    (hnd : ∀ i x x', (i, x) ∈ news → (i, x') ∈ news → x = x')
    (hold : ∀ i x x', (i, x) ∈ p.l → (i, x') ∈ news → x = x')
    (hloc : ∀ pr, pr ∈ news → ∃ d, loc.w d = pr.1) :
    ∃ p' : FinBit I, FinBitLe p p' ∧ (∀ y, y ∈ news → y ∈ p'.l) ∧
      (∀ i x, (i, x) ∈ p'.l → (∃ x', (i, x') ∈ p.l) ∨ ∃ d, loc.w d = i) := by
  refine ⟨⟨p.l ++ news, ?nd⟩, ?le, ?mem, ?loc⟩
  case nd =>
    intro i x x' h₁ h₂
    rw [List.mem_append] at h₁ h₂
    cases h₁ with
    | inl h₁ =>
      cases h₂ with
      | inl h₂ => exact p.nd i x x' h₁ h₂
      | inr h₂ => exact hold i x x' h₁ h₂
    | inr h₁ =>
      cases h₂ with
      | inl h₂ => exact (hold i x' x h₂ h₁).symm
      | inr h₂ => exact hnd i x x' h₁ h₂
  case le =>
    intro i x hmem
    show (i, x) ∈ p.l ++ news
    rw [List.mem_append]
    exact Or.inl hmem
  case mem =>
    intro y hy
    show y ∈ p.l ++ news
    rw [List.mem_append]
    exact Or.inr hy
  case loc =>
    intro i x hmem
    show (∃ x', (i, x') ∈ p.l) ∨ ∃ d, loc.w d = i
    rw [List.mem_append] at hmem
    cases hmem with
    | inl h => exact Or.inl ⟨x, h⟩
    | inr h => exact Or.inr (hloc (i, x) h)

/-! ## 3. Choice recovery -/

/-- **选择恢复.** The recovery direction of the paper: a data surjection
from the fixed seed `S` times an ordinal-like index `α` onto a new set `X`
well-orders `X` (the batch-3 `wo_of_surjection`, instantiated as the
random-model recovery step). -/
theorem choice_recovery {S A X : Type} (rS : WOrd S) (rA : OrdIndex A)
    (σ : S × A → X) (hsurj : Function.Surjective σ) : WO X :=
  wo_of_surjection rS rA σ hsurj

/-! ## 4. R139 negative boundary -/

/-- Placeholder data consisting of a Boolean function and a well-founded
relation. It contains no Baire/category/measurability condition. Absence of
an instance proves nothing about random forcing or the R139 counterexample;
that counterexample is not formalized in this repository. -/
structure CategoryAcc (Q : Type) (aux : Q → Q → Prop) where
  color : Q → Bool
  accWf : WellFounded aux

end PPAC.Random
