/-
Host-type interfaces, not a formal interpretation of ZF.
WO X quantifies over ALL host relations on X; it is not an abstract
predicate for well-orders belonging to an inner model. In classical Lean
with choice every host type is well-orderable, so hypotheses `not WO X`
do not exhibit a choiceless model. Choice-free proof terms below record
conditional proof patterns only. OrdIndex includes explicit data selectors;
absence of Classical.choice in an axiom footprint does not remove the
choice content supplied by these parameters. PP, AC_WO, and SVC likewise
range over host types/functions. No internal-model adapter is provided.
-/

namespace PPAC.Choice

/-! ## Well-orderability -/

/-- Trichotomy for an abstract relation. -/
def Trich {X : Type} (r : X → X → Prop) : Prop :=
  ∀ a b, r a b ∨ a = b ∨ r b a

/-- Host well-orderability: existence of a trichotomous well-founded
relation. This does not restrict relations to members of an inner model. -/
def WO (X : Type) : Prop :=
  ∃ r : X → X → Prop, Trich r ∧ WellFounded r

/-- The empty type is well-orderable (empty relation). -/
theorem wo_empty : WO Empty := by
  refine ⟨fun _ _ => False, ?_, ?_⟩
  · intro a b
    exact Empty.elim a
  · exact ⟨fun a => Empty.elim a⟩

/-- Any subsingleton type is well-orderable. -/
theorem wo_subsingleton {X : Type} [Subsingleton X] : WO X := by
  refine ⟨fun _ _ => False, ?_, ?_⟩
  · intro a b
    exact Or.inr (Or.inl (Subsingleton.elim a b))
  · exact ⟨fun a => Acc.intro a (fun b hb => False.elim hb)⟩

/-- A least element is unique (description, not choice): the interface
field `OrdIndex.leastSel` is therefore a definite description. -/
theorem least_unique {I : Type} {r : I → I → Prop} (htri : Trich r) {p : I → Prop}
    {m m' : I} (hm : p m ∧ ∀ i, p i → ¬ r i m) (hm' : p m' ∧ ∀ i, p i → ¬ r i m') :
    m = m' := by
  cases htri m m' with
  | inl h => exact absurd h (hm'.2 m hm.1)
  | inr h =>
    cases h with
    | inl h => exact h
    | inr h => exact absurd h (hm.2 m' hm'.1)

/-! ## Injections, surjections, PP -/

/-- Partition Principle at the type level: every surjection `A ↠ B`
admits an injection `B ↪ A`. Object-level rendition boundary: this is the
type-level statement; its internal (ZF) meaning and the Pincus/Higasikawa
bridge `PP ⇒ AC_WO` are cited, not formalized, in this batch. -/
def PP : Prop :=
  ∀ (A B : Type) (f : A → B), Function.Surjective f → ∃ g : B → A, Function.Injective g

/-! ## Ordinal-like index and AC_WO -/

/-- Ordinal-like index interface: a trichotomous well-founded relation
together with the two object-level properties of ordinals used by the
splitting argument.

`leastSel`: every nonempty definable family has a least element, provided
as data. The selector is *description, not choice*: any two values of the
subtype are equal (both are least, and the relation is trichotomous), so
this mirrors the object-level definite description of `min{β : p β}`
inside ZF. It is a hypothesis, never an axiom.

`classical`: set-many classical logic for `I`-indexed families
(`¬∀ → ∃¬`), provable in ZF, stated here as an interface hypothesis. -/
structure OrdIndex (I : Type) where
  r : I → I → Prop
  r_trich : Trich r
  r_wf : WellFounded r
  leastSel : ∀ p : I → Prop, (∃ i, p i) → {m : I // p m ∧ ∀ i, p i → ¬ r i m}
  classical : ∀ p : I → Prop, ¬ (∀ i, p i) → ∃ i, ¬ p i

/-- `AC_WO` interface for the index type `I`: choice for `I`-indexed
families of nonempty types.

The content is *data* (a dependent choice function), so the interface is
Sort-valued and is always passed as an explicit hypothesis of the theorems
that use it — the host-layer rendition of fixing witnesses by existential
elimination while working inside `ZF + AC_WO`. It is never instantiated
and never declared as an axiom. -/
def AC_WO (I : Type) : Type 1 :=
  (F : I → Type) → (∀ i, Nonempty (F i)) → (∀ i, F i)

/-! ## SVC -/

/-- `SVC(S)`: every type is a surjective image of `S × I` for some
ordinal-like index `I`. Object-level boundary: the ZF adapter (internal
sets, actual ordinals) is not formalized in this batch; this is the
type-level semantic interface. -/
def SVC (S : Type) : Prop :=
  ∀ X : Type, ∃ (I : Type) (_ : OrdIndex I) (f : S × I → X), Function.Surjective f

end PPAC.Choice
