/-
PPAC/Pullback.lean — Batch 1, part A.

Pulling a "new" subset of the codomain back along an old surjection.

Universe bound: `A` and `B` are ordinary Lean types (universes `u`, `v`).
Subsets are predicate-valued (`X → Prop`); no ZF coding, Replacement or
Separation is performed or claimed in this module. The closure hypothesis
`ImageClosed` is an abstract assumption; supplying it from actual model
subsets inside ZF is a remaining bridge (see docs/FORMALIZATION_SCOPE.md).

Axiom discipline: no `sorry`, no custom `axiom`, no `Classical.choice`.
Only `propext` and `Quot.sound` may appear (via `funext`/`propext`); the
exact footprints are printed in `Audit.lean`.
-/

namespace PPAC

/-! ## Direct image, preimage, surjectivity -/

/-- Direct image of a predicate `T : A → Prop` along `h : A → B`. -/
def image {A : Type u} {B : Type v} (h : A → B) (T : A → Prop) : B → Prop :=
  fun b => ∃ a, h a = b ∧ T a

/-- Preimage (pullback) of a predicate `T : B → Prop` along `h : A → B`. -/
def preimage {A : Type u} {B : Type v} (h : A → B) (T : B → Prop) : A → Prop :=
  fun a => T (h a)

/-! ## The pullback identity `h[preimage(h, T)] = T` -/

/-- Pointwise form: a surjective `h` makes `b ∈ h[h⁻¹[T]] ↔ b ∈ T` hold for
every `b`. Both directions are constructive: the required witness `a` is
obtained by eliminating the existential supplied by surjectivity. -/
theorem image_preimage_iff {A : Type u} {B : Type v} {h : A → B}
    (hsurj : Function.Surjective h) (T : B → Prop) (b : B) :
    image h (preimage h T) b ↔ T b := by
  show (∃ a, h a = b ∧ T (h a)) ↔ T b
  constructor
  · intro himg
    cases himg with
    | intro a hpair =>
      cases hpair with
      | intro hab hTa => rw [← hab]; exact hTa
  · intro hTb
    cases hsurj b with
    | intro a hab =>
      subst hab
      exact ⟨a, rfl, hTb⟩

/-- The pullback identity as an equality of predicates:
`h[preimage(h, T)] = T`. Uses `funext` and `propext` only. -/
theorem image_preimage_eq {A : Type u} {B : Type v} {h : A → B}
    (hsurj : Function.Surjective h) (T : B → Prop) :
    image h (preimage h T) = T :=
  funext fun b => propext (image_preimage_iff hsurj T b)

/-! ## Old families closed under direct image, and the contrapositive -/

/-- Closure hypothesis: the family `OldA` of subsets of `A` is carried into
the family `OldB` of subsets of `B` by the direct image of `h`.

This is an *abstract* assumption. Deriving it for actual model subsets from
ZF Replacement/Separation is NOT part of this batch. -/
def ImageClosed {A : Type u} {B : Type v} (h : A → B)
    (OldA : (A → Prop) → Prop) (OldB : (B → Prop) → Prop) : Prop :=
  ∀ T, OldA T → OldB (image h T)

/-- Pullback contrapositive: under image-closure, a subset `T` of `B` that is
not old pulls back to a subset of `A` that is not old. Substantive proof: it
combines the closure instance for `preimage h T` with `image_preimage_eq`. -/
theorem notOld_preimage {A : Type u} {B : Type v} {h : A → B}
    (hsurj : Function.Surjective h)
    {OldA : (A → Prop) → Prop} {OldB : (B → Prop) → Prop}
    (hcl : ImageClosed h OldA OldB) {T : B → Prop} (hT : ¬ OldB T) :
    ¬ OldA (preimage h T) := by
  intro hOld
  have hIm : OldB (image h (preimage h T)) := hcl _ hOld
  rw [image_preimage_eq hsurj T] at hIm
  exact hT hIm

/-! ## Nonvacuity examples -/

/-- A nonempty two-point surjection: `Bool ↠ Unit`. Shows the identity's
hypotheses are satisfiable by a genuinely nonempty surjection (excluding the
vacuous empty-type instance). -/
theorem two_point_surjection_example :
    Function.Surjective (fun _ : Bool => ()) := fun b =>
  ⟨true, by cases b; rfl⟩

/-- The pullback identity holds for the concrete two-point surjection and the
maximal subset `T = ⊤`. -/
theorem pullback_identity_example :
    image (fun _ : Bool => ()) (preimage (fun _ : Bool => ()) (fun _ => True))
      = (fun _ => True) :=
  image_preimage_eq two_point_surjection_example _

/-- A concrete image-closed pair of old families: the "empty subset" families
on both sides. -/
theorem image_closed_empty_example :
    ImageClosed (fun _ : Bool => ())
      (fun T' : Bool → Prop => ∀ a, ¬ T' a)
      (fun T' : Unit → Prop => ∀ b, ¬ T' b) := by
  intro T hOld b hImg
  cases hImg with
  | intro a hpair =>
    cases hpair with
    | intro _ hTa => exact hOld a hTa

/-- Nonvacuity of the contrapositive: `T = ⊤` is not old (not the empty
family), and indeed its pullback is not old. -/
theorem notOld_example :
    ¬ ((fun T' : Bool → Prop => ∀ a, ¬ T' a)
        (preimage (fun _ : Bool => ()) (fun _ => True))) := by
  intro hIn
  exact hIn true trivial

end PPAC
