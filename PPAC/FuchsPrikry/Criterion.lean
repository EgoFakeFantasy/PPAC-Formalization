/-
Experimental host-type scaffolding inspired by the Fuchs-Prikry notes.
The only choice-transport result here is `criterion_forward`: a surjective
image of a carrier equipped with WOrd data is WO. It does not use
PosIdeal or IdealMax, and is NOT the support-ideal choice criterion.
PosIdeal supplies two abstract relations but does not construct a support
ideal, finite-difference quotient, translation group or symmetric model.
IdealMax.belowMax uses finMod; it must not be interpreted as a proof of
being greatest in an almost-inclusion order.
DC is a pointed host-level dependent-choice statement. No equivalence
between AC_omega and DC is proved. AC_omega does not imply DC in general;
any special-model converse requires separate hypotheses and proof.
-/

import PPAC.Random.Approx

namespace PPAC.FuchsPrikry

open PPAC.Repair PPAC.ClassObstruction PPAC.Cohen PPAC.Random PPAC.Choice

/-! ## Dependent choice -/

/-- Dependent choice for a total relation on `Q`: the model-level DC
equivalent of the criterion enters through this interface. -/
def DC (Q : Type) (R : Q → Q → Prop) : Prop :=
  (∀ x, ∃ y, R x y) → ∀ x0 : Q,
    ∃ f : Nat → Q, f 0 = x0 ∧ ∀ n, R (f n) (f (n + 1))

 /-! The DC-based exclusion engine (DC + WF + a descending step everywhere
⟹ False) is a listed bridge: the Acc-induction form is not completed in
this batch. -/

/-! ## The position ideal and the maximum-support criterion -/

/-- A position ideal: a family of index-supports, downward closed and
closed under the finite modifications (the relation `finMod`), with a
countable-cover rendition of its members. -/
structure PosIdeal (P : Type) where
  mem : P → Prop
  le : P → P → Prop
  down : ∀ a b, le a b → mem b → mem a
  finMod : P → P → Prop
  finClosed : ∀ a b, mem a → finMod a b → mem b

/-- The criterion's left side: the ideal has a maximum support mod finite
— every member is a finite modification of the maximum `E`. -/
structure IdealMax (P : Type) (I : PosIdeal P) where
  E : P
  memE : I.mem E
  belowMax : ∀ J, I.mem J → I.finMod J E

/-- The orbit-family interface: the elements of `Q` are, up to the
finite-difference equivalence, represented by the support-restricted
copies of a carrier `P` — the surjection `hξ` is the E-representation
(§: 轨道选择). -/
structure OrbitFamily (Q P : Type) where
  hξ : P → Q
  hsurj : Function.Surjective hξ

/-- The ordinal-like index structure on `Unit`: a one-point index with
the least-element selector and the classical field (both trivially
constructive for `Unit`). -/
def ordIndexUnit : OrdIndex Unit := by
  refine ⟨fun _ _ => False, ?_, ⟨fun a => Acc.intro a (fun b hb => False.elim hb)⟩, ?_, ?_⟩
  · intro a b
    exact Or.inr (Or.inl (Subsingleton.elim a b))
  · intro p h
    have hp0 : p () := by
      cases h with
      | intro i hi => rw [Subsingleton.elim i ()] at hi; exact hi
    exact Subtype.mk () (And.intro hp0 (fun i' h' h'' => False.elim h''))
  · intro p h
    have h' : ¬ p () := fun hx => h fun _ => hx
    exact Exists.intro () h'

/-- Surjective well-order transport only. Neither PosIdeal nor IdealMax
is a parameter or dependency; no Fuchs-Prikry criterion follows here. -/
theorem criterion_forward {Q P : Type} (OF : OrbitFamily Q P) (rP : WOrd P) :
    WO Q := by
  have hord : OrdIndex Unit := ordIndexUnit
  refine wo_of_surjection rP hord (fun z => OF.hξ z.1) ?_
  intro q
  cases OF.hsurj q with
  | intro p hp => exact ⟨(p, ()), hp⟩

/-- Regression: pointed dependent choice does not require an element of Empty. -/
theorem dc_empty : DC Empty (fun _ _ => False) := by
  intro _ x0
  cases x0

end PPAC.FuchsPrikry
