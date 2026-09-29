/-
Relational components motivated by finite-support partial-section forcing.

This file checks monotonicity, coding-density and conditional coverage
statements with explicit freshness/coding/genericity data. It does not prove
the full lifting property of a forcing projection or construct a forcing
extension. The type Nat -> Bool contains all ambient reals; it does not
represent the old reals of an inner model. Consequently the hypotheses of
a coverage implication must not be advertised as an actual model instance.
An old-real carrier and the ground/extension interpretation are still needed.
See THEOREM_COVERAGE.md and GAPS.md for the publication scope.
-/

import PPAC.Repair.Forcing

namespace PPAC.Repair

/-! ## Swap-coding interface -/

/-- Old-model data coding every old real `r : Nat → Bool` into the wide
fiber `q⁻¹(g n)` of the fixed `n`-th point `g n`, together with an old
decoder defined on all of `A` (extended arbitrarily off the coding) and
the freshness interface for the range of `g`. -/
structure SwapCoding (A B : Type) (q : A → B) (g : Nat → B) where
  code : Nat → (Nat → Bool) → A
  code_fiber : ∀ n r, q (code n r) = g n
  decode : Nat → A → (Nat → Bool)
  decode_code : ∀ n r, decode n (code n r) = r
  listFresh : ∀ L : List B, ∃ n, g n ∉ L

/-! ## The generic union relation for list-sections -/

/-- The generic union of a directed family of finite sections, as a
relation. -/
def jrelSec {A B : Type} {q : A → B} (G : SecList B A q → Prop) (b : B) (a : A) : Prop :=
  ∃ p : SecList B A q, G p ∧ (b, a) ∈ p.l

/-! ## The relational projection -/

/-- The projected condition: `n ↦ decode n (p(g n))`, relationally. -/
def projRel {A B : Type} {q : A → B} {g : Nat → B} (SC : SwapCoding A B q g)
    (p : SecList B A q) (n : Nat) (r : Nat → Bool) : Prop :=
  ∃ a, (g n, a) ∈ p.l ∧ SC.decode n a = r

/-- The projection is order-preserving. -/
theorem projRel_mono {A B : Type} {q : A → B} {g : Nat → B} (SC : SwapCoding A B q g)
    {p p' : SecList B A q} (hle : SecListLe p p') {n : Nat} {r : Nat → Bool}
    (h : projRel SC p n r) : projRel SC p' n r := by
  cases h with
  | intro a ha => exact ⟨a, hle (g n) a ha.1, ha.2⟩

/-- **Density of the coding requirements** `D_r = {p : ∃ n a, (g n, a) ∈ p.l ∧
decode n a = r}`: from any condition, a fresh index `n` (the whole range of
`g` avoids any finite list) admits the extension assigning `code n r`. -/
theorem denseD_r {A B : Type} {q : A → B} {g : Nat → B} (SC : SwapCoding A B q g)
    (p : SecList B A q) (r : Nat → Bool) :
    ∃ p' : SecList B A q, SecListLe p p' ∧
      ∃ n a, (g n, a) ∈ p'.l ∧ SC.decode n a = r := by
  cases SC.listFresh (p.l.map Prod.fst) with
  | intro n hn =>
    have hfresh : ∀ a, (g n, a) ∉ p.l := by
      intro a hmem
      exact hn (List.mem_map.mpr ⟨(g n, a), hmem, rfl⟩)
    cases secList_grow p [(g n, SC.code n r)]
      (hsec := fun b a hmem => by
        have e : (b, a) = (g n, SC.code n r) := List.mem_singleton.mp hmem
        have hb : b = g n := congrArg Prod.fst e
        have ha : a = SC.code n r := congrArg Prod.snd e
        rw [ha, hb]
        exact SC.code_fiber n r)
      (hold := fun b a a' hmem_old hmem_new => by
        have e : (b, a') = (g n, SC.code n r) := List.mem_singleton.mp hmem_new
        have hb : b = g n := congrArg Prod.fst e
        have h' : (g n, a) ∈ p.l := by rw [← hb]; exact hmem_old
        exact absurd h' (hfresh a))
      (hnew := fun b a a' h₁ h₂ => by
        have e1 : (b, a) = (g n, SC.code n r) := List.mem_singleton.mp h₁
        have e2 : (b, a') = (g n, SC.code n r) := List.mem_singleton.mp h₂
        have h1a : a = SC.code n r := congrArg Prod.snd e1
        have h2a : a' = SC.code n r := congrArg Prod.snd e2
        rw [h1a, h2a])
    with
    | intro p' hp' =>
      refine ⟨p', hp'.1, n, SC.code n r, ?_, SC.decode_code n r⟩
      exact hp'.2 (g n, SC.code n r) (List.mem_singleton.mpr rfl)

/-- **Collapse (relational).** A directed family `G` meeting every coding
requirement makes the decoded generic sequence cover all old reals: for
each `r` there are `n` and a value `a` in the generic union at `g n` with
`decode n a = r`. Internally this is the statement that `n ↦ decode n
(j(g n))` is a surjection `ω ↠ R_old`, i.e. `R_old` becomes countable. -/
theorem collapse_fin {A B : Type} {q : A → B} {g : Nat → B} (SC : SwapCoding A B q g)
    (G : SecList B A q → Prop)
    (hdir : ∀ p p', G p → G p' → ∃ p'' : SecList B A q, G p'' ∧
      SecListLe p p'' ∧ SecListLe p' p'')
    (hmeet : ∀ r : Nat → Bool, ∃ p, G p ∧ ∃ n a, (g n, a) ∈ p.l ∧ SC.decode n a = r) :
    ∀ r : Nat → Bool, ∃ n a, jrelSec G (g n) a ∧ SC.decode n a = r := by
  intro r
  cases hmeet r with
  | intro p hp =>
    cases hp.2 with
    | intro n ha =>
      cases ha with
      | intro a ha' =>
        cases ha' with
        | intro hmem hdec =>
          exact ⟨n, a, Exists.intro p (And.intro hp.1 hmem), hdec⟩

/-- The decoded generic values are unique per index (functionality of the
internal map `n ↦ decode n (j(g n))`). -/
theorem collapse_fin_fun {A B : Type} {q : A → B} {g : Nat → B} (SC : SwapCoding A B q g)
    (G : SecList B A q → Prop)
    (hdir : ∀ p p', G p → G p' → ∃ p'' : SecList B A q, G p'' ∧
      SecListLe p p'' ∧ SecListLe p' p'')
    {n : Nat} {r r' : Nat → Bool}
    (h₁ : ∃ a, jrelSec G (g n) a ∧ SC.decode n a = r)
    (h₂ : ∃ a, jrelSec G (g n) a ∧ SC.decode n a = r') : r = r' := by
  cases h₁ with
  | intro a ha =>
    cases h₂ with
    | intro a' ha' =>
      cases ha.1 with
      | intro p hp =>
        cases ha'.1 with
        | intro p' hp' =>
          cases hdir p p' hp.1 hp'.1 with
          | intro p'' hp'' =>
            have hle1 : SecListLe p p'' := hp''.2.1
            have hle2 : SecListLe p' p'' := hp''.2.2
            have hmem1 : (g n, a) ∈ p''.l := hle1 (g n) a hp.2
            have hmem2 : (g n, a') ∈ p''.l := hle2 (g n) a' hp'.2
            have hval : a = a' := p''.funi (g n) a a' hmem1 hmem2
            rw [← ha.2, ← ha'.2, hval]

end PPAC.Repair
