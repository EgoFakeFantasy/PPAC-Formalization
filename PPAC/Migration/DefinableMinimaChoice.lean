/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0; see third_party/constructible-universe/LICENSE.
Original author: Zike Liu. Object-kernel adaptation: PPAC migration contributors.

Adapted from lean-constructible-universe at 7f5a7d03d63d9769172f17350bbe8303996e5b53:
ConstructibleUniverse/SetTheory/ZFC/Constructible/Choice.lean and InternalWellOrder.lean (least-member separation and the
family-local unique-minimum argument), and Def.lean (renaming semantics).
The existing five-constructor formulas become the already accepted Source
syntax. The same separation argument now works in every nativeZF model,
and existing completeness/reverse/relativization interfaces return original
Derives certificates. The actual L stage-order/minimum theorem is a separate obligation.
The principle uses one internal relation parameter per family, not a global
choice of relations or a uniform minimum relation on the whole universe.
-/
import PPAC.Migration.ModelTransfer
import PPAC.Migration.SeparationSyntax
import PPAC.Migration.ObjectSelectorGraphChoice
import PPAC.Migration.ReverseZFReplay
import PPAC.Migration.Relativization

namespace PPAC.Migration.DefinableMinimaChoice
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open Source.SetLanguage (args3)
attribute [local implicit_reducible] SetTheory.signature
set_option autoImplicit false
universe u
variable {A : Type u}

theorem lift_assignment {n m : Nat} (r : Fin n → Fin m) (v : Fin m → A) (x : A) :
    (fun i => Fin.lastCases x v (Source.Formula.liftRen r i)) =
      Fin.lastCases x (fun i => v (r i)) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;>
    simp only [Source.Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem realize_rename (E : A → A → Prop) {n m : Nat} (p : Source.Formula n)
    (r : Fin n → Fin m) (v : Fin m → A) :
    Source.Formula.Realize E v (p.rename r) ↔
      Source.Formula.Realize E (fun i => v (r i)) p := by
  induction p generalizing m with
  | bot => rfl
  | mem => rfl
  | equal => rfl
  | imp p q hp hq | conj p q hp hq | disj p q hp hq =>
      simp only [Source.Formula.rename, Source.Formula.Realize, hp, hq]
  | all p hp | ex p hp =>
      simp only [Source.Formula.rename, Source.Formula.Realize, hp, lift_assignment]

/-- In context (r,x,y), y belongs to x and no z in x precedes y by lt(r,z,y). -/
def least (lt : Source.Formula 3) : Source.Formula 3 :=
  .conj (.mem 2 1) (.all ((Source.Formula.mem 3 1).imp
    ((lt.rename (args3 0 3 2)).neg)))

/-- For each family a there is an internal parameter r selecting unique minima
for its nonempty members. Both quantifiers are in the object sentence. -/
def minimumPrinciple (lt : Source.Formula 3) : Source.Sentence :=
  .all (.ex (.all ((Source.Formula.mem 2 0).imp
    ((Source.SetLanguage.nonempty 2).imp (.ex
      (((least lt).rename (args3 1 2 3)).conj
        (.all (((least lt).rename (args3 1 2 4)).imp (.equal 4 3)))))))))

/-- The existing L construction, in context (r,a,y). -/
def selected (lt : Source.Formula 3) : Source.Formula 3 :=
  .ex ((Source.Formula.mem 3 1).conj ((least lt).rename (args3 0 3 2)))

theorem selected_semantics (E : A → A → Prop) (lt : Source.Formula 3)
    (v : Fin 3 → A) :
    Source.Formula.Realize E v (selected lt) ↔
      ∃ x, E x (v 1) ∧ Source.Formula.Realize E (args3 (v 0) x (v 2)) (least lt) := by
  simp only [selected, Source.Formula.Realize, realize_rename]
  have he (x : A) : (fun i => Fin.lastCases x v (args3 0 3 2 i)) = args3 (v 0) x (v 2) := by
    funext i
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k =>
      Fin.cases ?_ (fun l => Fin.elim0 l) k) j) i <;> rfl
  simp only [he]
  rfl

theorem minimum_semantics (E : A → A → Prop) (lt : Source.Formula 3) :
    Source.Formula.Realize E Fin.elim0 (minimumPrinciple lt) ↔
      ∀ a, ∃ r, ∀ x, E x a → (∃ y, E y x) → ∃ y,
        Source.Formula.Realize E (args3 r x y) (least lt) ∧
        ∀ z, Source.Formula.Realize E (args3 r x z) (least lt) → z = y := by
  simp only [minimumPrinciple, Source.SetLanguage.nonempty,
    Source.Formula.Realize, realize_rename]
  have hPair (a r x y : A) :
      (fun i => Fin.lastCases y (Fin.lastCases x (Fin.lastCases r
        (Fin.lastCases a Fin.elim0))) (args3 1 2 3 i)) = args3 r x y := by
    funext i
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k =>
      Fin.cases ?_ (fun l => Fin.elim0 l) k) j) i <;> rfl
  have hPair3 (a r x y z : A) :
      (fun i => Fin.lastCases z (Fin.lastCases y (Fin.lastCases x
        (Fin.lastCases r (Fin.lastCases a Fin.elim0)))) (args3 1 2 4 i)) = args3 r x z := by
    funext i
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k =>
      Fin.cases ?_ (fun l => Fin.elim0 l) k) j) i <;> rfl
  simp only [hPair, hPair3]
  rfl

theorem separation_semantics (E : A → A → Prop) (p : Source.Formula 3) :
    Source.Formula.Realize E Fin.elim0 (Source.SetLanguage.separation p) ↔
      ∀ r a u, ∃ c, ∀ y, E y c ↔ E y u ∧ Source.Formula.Realize E (args3 r a y) p := by
  simp only [Source.SetLanguage.separation, Source.Formula.close,
    Source.Formula.Realize, realize_rename]
  have he (r a u c y : A) :
      (fun i => Fin.lastCases y (Fin.lastCases c (Fin.lastCases u
        (Fin.lastCases a (Fin.lastCases r Fin.elim0)))) (SeparationSyntax.matrixIndex i)) = args3 r a y := by
    funext i
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k =>
      Fin.cases ?_ (fun l => Fin.elim0 l) k) j) i <;> rfl
  apply forall_congr'
  intro r
  apply forall_congr'
  intro a
  apply forall_congr'
  intro u
  apply exists_congr
  intro c
  apply forall_congr'
  intro y
  change ((E y c → E y u ∧ Source.Formula.Realize E
    (fun i => Fin.lastCases y (Fin.lastCases c (Fin.lastCases u
      (Fin.lastCases a (Fin.lastCases r Fin.elim0)))) (SeparationSyntax.matrixIndex i)) p) ∧
    ((E y u ∧ Source.Formula.Realize E
    (fun i => Fin.lastCases y (Fin.lastCases c (Fin.lastCases u
      (Fin.lastCases a (Fin.lastCases r Fin.elim0)))) (SeparationSyntax.matrixIndex i)) p) → E y c)) ↔ _
  rw [he]
  exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.mp, h.mpr⟩⟩

/-- Reuse separation on the union of the family in every nativeZF model. -/
theorem selector_models (lt : Source.Formula 3)
    {M : FirstOrder.Structure.{0,0,0,u} ℒ} (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence ((minimumPrinciple lt).imp ChoiceSyntax.selectorAC)).TrueIn M := by
  change (Translation.sentence (minimumPrinciple lt)).TrueIn M →
    (Translation.sentence ChoiceSyntax.selectorAC).TrueIn M
  intro hMinimum
  let E : M.Carrier .set → M.Carrier .set → Prop := fun x y =>
    M.relInterp .membership (.cons x (.cons y .nil))
  have hmin := (minimum_semantics E lt).mp
    ((Translation.realizes_sentence M _).mp hMinimum)
  have hUnion := (Translation.realizes_sentence M Source.SetLanguage.union).mp
    (ZFEquivalence.source_union.semantically_entails M hM)
  change ∀ a, ∃ u, ∀ y, (E y u → ∃ x, E x a ∧ E y x) ∧
    ((∃ x, E x a ∧ E y x) → E y u) at hUnion
  have hSep := (separation_semantics E (selected lt)).mp
    ((Translation.realizes_sentence M _).mp
      ((SeparationSyntax.source_separation (selected lt)).semantically_entails M hM))
  apply (Translation.realizes_sentence M _).mpr
  change ∀ a, ((∀ x, E x a → ∃ y, E y x) ∧
    (∀ x, E x a → ∀ x', E x' a → x ≠ x' → ¬ ∃ z, E z x ∧ E z x')) →
    ∃ c, ∀ x, E x a → ∃ y, (E y c ∧ E y x) ∧
      ∀ z, (E z c ∧ E z x) → z = y
  rintro a ⟨hNonempty, hDisjoint⟩
  obtain ⟨r, hr⟩ := hmin a
  obtain ⟨u, hu⟩ := hUnion a
  obtain ⟨c, hc⟩ := hSep r a u
  refine ⟨c, ?_⟩
  intro x hxa
  obtain ⟨y, hy, hyUnique⟩ := hr x hxa (hNonempty x hxa)
  have hyx : E y x := hy.1
  refine ⟨y, ⟨?_, hyx⟩, ?_⟩
  · apply (hc y).mpr
    refine ⟨(hu y).2 ⟨x, hxa, hyx⟩, ?_⟩
    exact (selected_semantics E lt (args3 r a y)).mpr ⟨x, hxa, hy⟩
  · rintro z ⟨hzc, hzx⟩
    obtain ⟨x', hx'a, hzMin⟩ :=
      (selected_semantics E lt (args3 r a z)).mp ((hc z).mp hzc).2
    have hxx' : x = x' := by
      apply Classical.byContradiction
      intro hne
      exact hDisjoint x hxa x' hx'a hne ⟨z, hzx, hzMin.1⟩
    subst x'
    exact hyUnique z hzMin

theorem selector_kernel_certificate (lt : Source.Formula 3) :
    FirstOrder.Derives nativeZF []
      (Translation.sentence ((minimumPrinciple lt).imp ChoiceSyntax.selectorAC)) :=
  ModelTransfer.derives (fun _ hM => selector_models lt hM)

/-- A closed original-ZF derivation with the family minimum principle as antecedent. -/
theorem kernel_certificate (lt : Source.Formula 3) :
    FirstOrder.Derives nativeZF []
      (Translation.sentence ((minimumPrinciple lt).imp Source.SetLanguage.AC)) := by
  apply FirstOrder.Derives.imp_intro
  have hSelector := FirstOrder.Derives.imp_elim
    (selector_kernel_certificate lt).context_weaken_cons
    (FirstOrder.Derives.assumption List.mem_cons_self)
  exact FirstOrder.Derives.imp_elim
    ObjectSelectorGraphChoice.native_reverse.context_weaken_cons hSelector

theorem source_certificate (lt : Source.Formula 3) :
    Source.Derives (Source.SetLanguage.ZF.at 1)
      (((minimumPrinciple lt).imp Source.SetLanguage.AC).rename Fin.elim0) :=
  ReverseZFReplay.source_sentence (kernel_certificate lt)

/-- Original interpretation compiler: relative ZF and domain nonemptiness are explicit. -/
theorem relative_kernel_certificate (D : Source.Formula 1) (lt : Source.Formula 3) :
    FirstOrder.Derives
      (TheoryTransport.theory (Relativization.theory D Source.SetLanguage.ZF)) []
      (Translation.sentence ((Source.Formula.ex D).imp
        ((Relativization.formula D (minimumPrinciple lt)).imp
          (Relativization.formula D Source.SetLanguage.AC)))) :=
  Relativization.kernel_certificate D (source_certificate lt)

end PPAC.Migration.DefinableMinimaChoice
