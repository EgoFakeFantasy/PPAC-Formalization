/-
PPAC/Choice/Splice.lean — Batch 2, ordinal-index splicing engine.

Given a map `f : S → I` partitioning `S` into fibers `{s // f s = β}` and a
well-order on the ordinal-like index `I`, splicing arbitrary well-orders of
the fibers (chosen by `AC_WO`) yields a well-order of `S`. This is the
two-place engine used by the splitting lemma: once for the fibers
`F_{s,β}` of a fixed `s`, once for the index classes `A_β`.

Representation note: a fiber relation is carried as
`ρ : ∀ β, (x y : S) → f x = β → f y = β → Prop` (explicit membership
proofs) so that index transport is proof-irrelevance; `rho_transport` is
the only helper needed. Everything here is axiom-free.

Axiom discipline: no `sorry`, no custom `axiom`, no `Classical.choice`.
-/

import PPAC.Choice.Basic

namespace PPAC.Choice

/-! ## Fiber relations and transport -/

/-- A fiber-indexed relation with explicit membership proofs. -/
def FiberRel {S I : Type} (f : S → I)
    (ρ : ∀ β, (x y : S) → f x = β → f y = β → Prop)
    (β : I) : {s : S // f s = β} → {s : S // f s = β} → Prop :=
  fun a b => ρ β a.1 b.1 a.2 b.2

/-- Transport of a fiber relation along an index equality. The transported
membership proofs are proofs of the same propositions, so this closes by
proof irrelevance; no axioms are involved. -/
theorem rho_transport {S I : Type} (f : S → I)
    (ρ : ∀ β, (x y : S) → f x = β → f y = β → Prop)
    {x y : S} {β₁ β₂ : I} (h : β₁ = β₂)
    (hx : f x = β₁) (hy : f y = β₁) (hp : ρ β₁ x y hx hy) :
    ρ β₂ x y (h ▸ hx) (h ▸ hy) := by
  cases h
  exact hp

/-! ## The spliced relation -/

/-- Spliced order: compare by index first; within one fiber use `ρ`. -/
def spliceRel {S I : Type} (rI : I → I → Prop) (f : S → I)
    (ρ : ∀ β, (x y : S) → f x = β → f y = β → Prop) (x y : S) : Prop :=
  rI (f x) (f y) ∨ ∃ h : f x = f y, ρ (f x) x y rfl h.symm

/-- Constructor: index comparison. -/
theorem spliceRel_index {S I : Type} (rI : I → I → Prop) (f : S → I)
    (ρ : ∀ β, (x y : S) → f x = β → f y = β → Prop) {x y : S} (h : rI (f x) (f y)) :
    spliceRel rI f ρ x y := Or.inl h

/-- Constructor: same-fiber comparison. -/
theorem spliceRel_fiber {S I : Type} (rI : I → I → Prop) (f : S → I)
    (ρ : ∀ β, (x y : S) → f x = β → f y = β → Prop) {x y : S} (h : f x = f y)
    (hp : ρ (f x) x y rfl h.symm) : spliceRel rI f ρ x y := Or.inr ⟨h, hp⟩

/-- Trichotomy of the spliced order. -/
theorem splice_trich {S I : Type} (rI : I → I → Prop) (f : S → I)
    (ρ : ∀ β, (x y : S) → f x = β → f y = β → Prop)
    (htriI : Trich rI) (hρtri : ∀ β, Trich (FiberRel f ρ β)) :
    Trich (spliceRel rI f ρ) := by
  intro x y
  cases htriI (f x) (f y) with
  | inl h => exact Or.inl (spliceRel_index rI f ρ h)
  | inr h =>
    cases h with
    | inl h => -- f x = f y: compare inside the fiber
      cases hρtri (f x) ⟨x, rfl⟩ ⟨y, h.symm⟩ with
      | inl hr => exact Or.inl (spliceRel_fiber rI f ρ h hr)
      | inr hr =>
        cases hr with
        | inl he => exact Or.inr (Or.inl (congrArg Subtype.val he))
        | inr hr =>
          exact Or.inr (Or.inr
            (spliceRel_fiber rI f ρ h.symm (rho_transport f ρ h h.symm rfl hr)))
    | inr h => exact Or.inr (Or.inr (spliceRel_index rI f ρ h))

/-- Well-foundedness of the spliced order: lexicographic induction, outer
along the index, inner along the fiber. -/
theorem splice_wf {S I : Type} (rI : I → I → Prop) (f : S → I)
    (ρ : ∀ β, (x y : S) → f x = β → f y = β → Prop)
    (hwfI : WellFounded rI) (hρwf : ∀ β, WellFounded (FiberRel f ρ β)) :
    WellFounded (spliceRel rI f ρ) := by
  have key : ∀ β, Acc rI β → ∀ y, f y = β → Acc (spliceRel rI f ρ) y := by
    intro β accI
    induction accI with
    | intro β' _ ih =>
      intro y hy
      have inner : ∀ u : {s : S // f s = β'}, Acc (FiberRel f ρ β') u →
          Acc (spliceRel rI f ρ) u.1 := by
        intro u accU
        induction accU with
        | intro v hv ih2 =>
          refine Acc.intro v.1 (fun z hz => ?_)
          cases hz with
          | inl hz1 =>
            have hz1' : rI (f z) β' := by rw [← v.2]; exact hz1
            exact ih (f z) hz1' z rfl
          | inr hz2 =>
            cases hz2 with
            | intro h hp =>
              have hz' : f z = β' := Eq.trans h v.2
              exact ih2 ⟨z, hz'⟩ (rho_transport f ρ hz' rfl h.symm hp)
      exact inner ⟨y, hy⟩ ((hρwf β').apply ⟨y, hy⟩)
  exact ⟨fun y => key (f y) (hwfI.apply (f y)) y rfl⟩

/-! ## Splicing theorem -/

/-- If every fiber `{s // f s = β}` is well-orderable and `I` is an
ordinal-like index, then `S` is well-orderable — the fiber well-orders are
selected by `AC_WO` and spliced along `I`. This is the contrapositive
engine for "if `S` is not well-orderable, some fiber is not". -/
theorem partition_splice_wo {S I : Type} (rI : I → I → Prop)
    (htriI : Trich rI) (hwfI : WellFounded rI) (f : S → I)
    (hAC : AC_WO I) (h : ∀ β, WO {s : S // f s = β}) : WO S := by
  have hne : ∀ β, Nonempty
      {r : {s : S // f s = β} → {s : S // f s = β} → Prop // Trich r ∧ WellFounded r} := by
    intro β
    cases h β with
    | intro r hr => exact ⟨⟨r, hr⟩⟩
  have ρall := hAC
    (fun β => {r : {s : S // f s = β} → {s : S // f s = β} → Prop // Trich r ∧ WellFounded r})
    hne
  refine ⟨spliceRel rI f
      (fun β a b ha hb => (ρall β).1 ⟨a, ha⟩ ⟨b, hb⟩), ?_, ?_⟩
  · exact splice_trich rI f
      (fun β a b ha hb => (ρall β).1 ⟨a, ha⟩ ⟨b, hb⟩) htriI
      (fun β => (ρall β).2.1)
  · exact splice_wf rI f
      (fun β a b ha hb => (ρall β).1 ⟨a, ha⟩ ⟨b, hb⟩) hwfI
      (fun β => (ρall β).2.2)

end PPAC.Choice
