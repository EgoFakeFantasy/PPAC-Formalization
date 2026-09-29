/-
PPAC/ClassObstruction/Obstruction.lean — Batch 4, the fixed-seed
pollution obstruction.

Source: `固定SVC种子下保留禁用集的类修复障碍_核查.md` (2026-09-27), building
on batches 1–3. Formalizes, at the host-type level:

1. **Two-branch density** of the `R_ω(A,B)` conditions `(f, F)` (countable
   partial injection + countable forbidden set, disjoint): for any old
   predicate `Y` of the ground family on the non-well-orderable slice `X`
   and any condition, some stronger condition decides the generic trace
   against `Y` at a fresh point — pairing branch (`x ∈ Y`: pair a fresh
   `b ↦ x`) or forbidding branch (`x ∉ Y`: add `x` to `F`). The classical
   case split `x ∈ Y ∨ x ∉ Y` is the object-level classical logic of `M`,
   carried by the `PredFamily.ymdec` interface field.
2. **Trace newness**: a directed family meeting the deciding requirements
   has its generic trace `T_G` (the forbidden side, = `F_G ∩ X`, since
   generically `F_G = A \ ran(j)`) different from every old predicate.
3. **Pullback newness**: for an old surjection `hξ : S → X` of the slice,
   the preimage `U_G := hξ⁻¹[T_G]` differs from every old predicate on `S`
   — otherwise `T_G = hξ[U_G]` (surjectivity) would be old, via the
   Replacement interface `img_cover`.
4. **Stage-freeze contradiction**: cofinally many fresh subsets of `S` (one
   per repair stage) contradict the eventual freezing of the `S`-subsets in
   a stage-union final model.

BOUNDARY: the old-predicate families (`PredFamily`) with classical
membership and the `img_cover` Replacement field, the freshness/decision
interfaces, and the stage-chain data are hypotheses standing in for the
ground model `M ⊨ ZF + SVC(S) + AC_WO`. The class-length iteration is
represented only through the abstract stage-freeze interfaces — a proper
class of stages is NOT impersonated by a host small type beyond this
interface (真类索引的对象层适配不得以宿主小类型冒充). Static products and
dynamic iterations are kept apart: this file formalizes the single-repair
pollution step and its stage-freeze consequence, not a class iteration.
No claim of `PP ⇒ AC`, no countermodel, no priority.

Axiom discipline: no `sorry`, no custom `axiom`, no `Classical.choice`.
-/

import PPAC.Repair.NameEval

namespace PPAC.ClassObstruction

open PPAC.Repair

/-! ## Old-predicate families -/

/-- The ground-model subsets of a type, as a family with classical
membership (the object-level classical logic of `M ⊨ ZF`). -/
structure PredFamily (X : Type) where
  YM : Type
  ym : YM → X → Prop
  ymdec : ∀ y x, ym y x ∨ ¬ ym y x

theorem countable_unit : Countable Unit :=
  ⟨fun _ => 0, fun x y _ => Subsingleton.elim x y⟩

/-! ## The two-component repair conditions `(f, F)` -/

/-- An `R_ω`-style condition: a countable partial injection `rel` together
with a countable forbidden set `F` disjoint from the range. The domain,
range and forbidden set carry countable covers (the range cover is the
host rendition of "the range of a countable-domain injection is countable",
whose derivation from the domain cover uses AC_ω internally). -/
structure RCond (B A : Type) where
  rel : B → A → Prop
  funi : ∀ b a a', rel b a → rel b a' → a = a'
  inj : ∀ b b' a, rel b a → rel b' a → b = b'
  F : A → Prop
  disj : ∀ b a, rel b a → ¬ F a
  domC : Cover B
  domCov : ∀ b a, rel b a → ∃ d, domC.w d = b
  ranC : Cover A
  ranCov : ∀ b a, rel b a → ∃ d, ranC.w d = a
  FC : Cover A
  FCov : ∀ a, F a → ∃ d, FC.w d = a

/-- Extension order: both components grow. -/
def RCondLe {B A : Type} (p p' : RCond B A) : Prop :=
  (∀ b a, p.rel b a → p'.rel b a) ∧ (∀ a, p.F a → p'.F a)

/-- Every condition has an unused domain point — derived internally from
"the ground model contains no injection `B ↪ A`" (a total condition would
be one); interface here. -/
structure DomFresh (B A : Type) where
  domFresh : ∀ p : RCond B A, ∃ b, ∀ a, ¬ p.rel b a

/-- The freshness interface for the slice `X ⊆ A`: no countable family of
`A`-points exhausts the slice (host rendition of "the non-well-orderable
slice is uncountable"). -/
structure SliceFresh (A X : Type) (XA : X → A) where
  fresh : ∀ (D : Type) (_ : Countable D) (u : D → A), ∃ x : X, ∀ d, u d ≠ XA x

/-! ## The two extension primitives -/

/-- Adding a fresh pair `(b, a)`: both points unused, `a` not forbidden.
The covers grow by a fresh `Unit` summand each. -/
def RCond.pairExt (p : RCond B A) (b : B) (a : A)
    (hb : ∀ a', ¬ p.rel b a') (ha : ∀ b', ¬ p.rel b' a) (hF : ¬ p.F a) :
    RCond B A :=
  { rel := fun bb a' => p.rel bb a' ∨ (bb = b ∧ a' = a)
    funi := by
      intro bb a' a'' h₁ h₂
      cases h₁ with
      | inl h₁ =>
        cases h₂ with
        | inl h₂ => exact p.funi bb a' a'' h₁ h₂
        | inr h₂ => exact absurd (h₂.1 ▸ h₁) (hb a')
      | inr h₁ =>
        cases h₂ with
        | inl h₂ => exact absurd (h₁.1 ▸ h₂) (hb a'')
        | inr h₂ => rw [h₁.2, h₂.2]
    inj := by
      intro bb bb' a' h₁ h₂
      cases h₁ with
      | inl h₁ =>
        cases h₂ with
        | inl h₂ => exact p.inj bb bb' a' h₁ h₂
        | inr h₂ =>
          have h₁' : p.rel bb a := by rw [← h₂.2]; exact h₁
          exact absurd h₁' (ha bb)
      | inr h₁ =>
        cases h₂ with
        | inl h₂ =>
          have h₂' : p.rel bb' a := by rw [← h₁.2]; exact h₂
          exact absurd h₂' (ha bb')
        | inr h₂ => exact h₁.1.trans h₂.1.symm
    F := p.F
    disj := by
      intro bb a' hba
      cases hba with
      | inl h => exact p.disj bb a' h
      | inr h =>
        rw [h.2]
        exact hF
    domC := Cover.mk (p.domC.D ⊕ Unit) (countable_sum p.domC.hD countable_unit)
      (Sum.elim p.domC.w (fun _ => b))
    domCov := by
      intro bb a' hba
      cases hba with
      | inl h =>
        cases p.domCov bb a' h with
        | intro d hd =>
          refine ⟨Sum.inl d, ?_⟩
          show p.domC.w d = bb
          exact hd
      | inr h =>
        refine ⟨Sum.inr Unit.unit, ?_⟩
        show b = bb
        rw [← h.1]
    ranC := Cover.mk (p.ranC.D ⊕ Unit) (countable_sum p.ranC.hD countable_unit)
      (Sum.elim p.ranC.w (fun _ => a))
    ranCov := by
      intro bb a' hba
      cases hba with
      | inl h =>
        cases p.ranCov bb a' h with
        | intro d hd =>
          refine ⟨Sum.inl d, ?_⟩
          show p.ranC.w d = a'
          exact hd
      | inr h =>
        refine ⟨Sum.inr Unit.unit, ?_⟩
        show a = a'
        rw [← h.2]
    FC := p.FC
    FCov := p.FCov }

/-- Forbidding a range-fresh point `x`: the forbidden set grows by `x`,
the injection part is unchanged. -/
def RCond.forbidExt (p : RCond B A) (x : A) (hxran : ∀ b', ¬ p.rel b' x) :
    RCond B A :=
  { p with
    F := fun a => p.F a ∨ a = x
    disj := by
      intro bb a' hba
      have h₁ : ¬ p.F a' := p.disj bb a' hba
      have h₂ : ¬ (a' = x) := by
        intro he
        exact hxran bb (he ▸ hba)
      intro hOr
      cases hOr with
      | inl h => exact h₁ h
      | inr h => exact h₂ h
    FC := Cover.mk (p.FC.D ⊕ Unit) (countable_sum p.FC.hD countable_unit)
      (Sum.elim p.FC.w (fun _ => x))
    FCov := by
      intro a hF
      cases hF with
      | inl h =>
        cases p.FCov a h with
        | intro d hd =>
          refine ⟨Sum.inl d, ?_⟩
          show p.FC.w d = a
          exact hd
      | inr h =>
        refine ⟨Sum.inr Unit.unit, ?_⟩
        show x = a
        rw [← h] }

/-! ## Two-branch density -/

/-- **Two-branch density.** For every old predicate `Y` of the family and
every condition `p` there is a stronger condition `p'` and a fresh
`x ∈ X` deciding the trace against `Y`: pairing branch (`x ∈ Y`: pair a
fresh `b ↦ x`) or forbidding branch (`x ∉ Y`: add `x` to `F`). -/
theorem denseTwoBranch {B A X : Type} (XA : X → A)
    (YMX : PredFamily X) (SF : SliceFresh A X XA) (DF : DomFresh B A)
    (p : RCond B A) (y : YMX.YM) :
    ∃ p' : RCond B A, RCondLe p p' ∧
      ∃ x : X, (YMX.ym y x ∧ ∃ b, p'.rel b (XA x)) ∨ (¬ YMX.ym y x ∧ p'.F (XA x)) := by
  -- the combined countable cover of ran(p) ∪ F(p) inside A
  cases SF.fresh (p.ranC.D ⊕ p.FC.D) (countable_sum p.ranC.hD p.FC.hD)
    (Sum.elim p.ranC.w p.FC.w) with
  | intro x hxfresh =>
    have hxF : ¬ p.F (XA x) := by
      intro hF
      cases p.FCov (XA x) hF with
      | intro d hd => exact hxfresh (Sum.inr d) hd
    have hxran : ∀ b', ¬ p.rel b' (XA x) := by
      intro b' hrel
      cases p.ranCov b' (XA x) hrel with
      | intro d hd => exact hxfresh (Sum.inl d) hd
    cases YMX.ymdec y x with
    | inl hiny =>
      cases DF.domFresh p with
      | intro b hb =>
        refine ⟨RCond.pairExt p b (XA x) hb hxran hxF,
          ⟨fun bb a hba => Or.inl hba, fun a hF => hF⟩,
          x, Or.inl ⟨hiny, b, Or.inr (And.intro rfl rfl)⟩⟩
    | inr hnoty =>
      refine ⟨RCond.forbidExt p (XA x) hxran,
        ⟨fun bb a hba => hba, fun a hF => Or.inl hF⟩,
        x, Or.inr ⟨hnoty, Or.inr rfl⟩⟩

/-! ## Trace newness -/

/-- The generic range relation at `a`. -/
def RanG {B A : Type} (G : RCond B A → Prop) (a : A) : Prop :=
  ∃ p b, G p ∧ p.rel b a

theorem FGRan_false {B A : Type} {G : RCond B A → Prop} {a : A}
    (hdir : ∀ p p', G p → G p' → ∃ p'' : RCond B A, G p'' ∧
      RCondLe p p'' ∧ RCondLe p' p'')
    (hF : ∃ p, G p ∧ p.F a) (hR : ∃ p b, G p ∧ p.rel b a) : False := by
  cases hF with
  | intro p hp =>
    cases hR with
    | intro q hq =>
      cases hq with
      | intro b hb =>
        cases hdir p q hp.1 hb.1 with
        | intro p'' hp'' =>
          have hF' : p''.F a := hp''.2.1.2 a hp.2
          have hR' : p''.rel b a := hp''.2.2.1 b a hb.2
          exact p''.disj b a hR' hF'

/-- The generic trace `T_G` at the slice point `x`: the forbidden side
(= `F_G ∩ X`; generically `F_G = A \ ran(j)`). -/
def TG {B A : Type} {X : Type} (XA : X → A) (G : RCond B A → Prop) (x : X) : Prop :=
  ∃ p, G p ∧ p.F (XA x)

/-- **Trace newness.** A directed family meeting every deciding
requirement has its generic trace differ from every old predicate of the
family at some fresh point. -/
theorem trace_not_old {B A X : Type} (XA : X → A) (YMX : PredFamily X)
    (G : RCond B A → Prop)
    (hdir : ∀ p p', G p → G p' → ∃ p'' : RCond B A, G p'' ∧
      RCondLe p p'' ∧ RCondLe p' p'')
    (hmeet : ∀ y : YMX.YM, ∃ p, G p ∧ ∃ x : X,
      (YMX.ym y x ∧ ∃ b, p.rel b (XA x)) ∨ (¬ YMX.ym y x ∧ p.F (XA x))) :
    ∀ y : YMX.YM, ∃ x : X, TG XA G x ≠ YMX.ym y x := by
  intro y
  cases hmeet y with
  | intro p hp =>
    cases hp.2 with
    | intro x hx =>
      cases hx with
      | inl hx =>
        cases hx.2 with
        | intro b hb =>
          refine ⟨x, fun heq => ?_⟩
          have hR : RanG G (XA x) := ⟨p, b, hp.1, hb⟩
          have hF : TG XA G x := heq.symm ▸ hx.1
          exact FGRan_false hdir hF hR
      | inr hx =>
        refine ⟨x, fun heq => ?_⟩
        have hF : TG XA G x := ⟨p, hp.1, hx.2⟩
        have hny : ¬ YMX.ym y x := hx.1
        rw [heq] at hF
        exact hny hF

/-! ## Pullback newness -/

/-- The preimage trace `U_G := hξ⁻¹[T_G]` for a total old surjection
`hξ : S → X` of the slice. -/
def Upred {B A S X : Type} (XA : X → A) (G : RCond B A → Prop) (hξ : S → X)
    (s : S) : Prop := TG XA G (hξ s)

/-- **Pullback newness.** If the preimage trace `U_G` were an old
predicate of the `S`-family, then — by the Replacement interface
`himg` (images of old-family members under the old map `hξ` are
old-family members) and the surjectivity of `hξ` — the trace `T_G` would
equal the old predicate `ym y`, contradicting `trace_not_old`. -/
theorem pollution_pullback {B A S X : Type} (XA : X → A) (hξ : S → X)
    (YMX : PredFamily X) (YMS : PredFamily S)
    (G : RCond B A → Prop)
    (hdir : ∀ p p', G p → G p' → ∃ p'' : RCond B A, G p'' ∧
      RCondLe p p'' ∧ RCondLe p' p'')
    (hmeet : ∀ y : YMX.YM, ∃ p, G p ∧ ∃ x : X,
      (YMX.ym y x ∧ ∃ b, p.rel b (XA x)) ∨ (¬ YMX.ym y x ∧ p.F (XA x)))
    (hsurj : ∀ x, ∃ s, hξ s = x)
    (himg : ∀ yS : YMS.YM, ∃ y : YMX.YM,
      ∀ x, YMX.ym y x ↔ ∃ s, YMS.ym yS s ∧ hξ s = x) :
    ∀ yS : YMS.YM, ¬ ∀ s, Upred XA G hξ s = YMS.ym yS s := by
  intro yS heq
  cases himg yS with
  | intro y himgy =>
    cases trace_not_old XA YMX G hdir hmeet y with
    | intro x hx =>
      cases hsurj x with
      | intro s hs =>
        have hkey : TG XA G x ↔ YMX.ym y x := by
          constructor
          · intro hT
            refine himgy x |>.mpr ⟨s, ?_, hs⟩
            rw [← heq s]
            show TG XA G (hξ s)
            rw [hs]
            exact hT
          · intro h
            cases himgy x |>.mp h with
            | intro s' hs' =>
              rw [← hs'.2]
              show Upred XA G hξ s'
              exact (heq s').symm ▸ hs'.1
        exact hx (propext hkey)

/-! ## Stage-freeze contradiction -/

/-- The stage-chain interfaces: a stage order with cofinally many repair
stages each contributing a fresh subset of `S` (outside the ground family
of that stage), and the eventual freezing of the `S`-subsets in the
stage-union final model. Internally the freezing holds because
`P(S)^N ∈ N` belongs to some stage `M_γ` and transitivity keeps its
elements there from `γ` on; that ZF argument is the interface's content,
not formalized here. -/
structure StageFreeze (I S : Type) (le : I → I → Prop) where
  new : I → (S → Prop) → Prop
  gamma : I
  freeze : ∀ j, le gamma j → ∀ U, new j U → False
  cofinal : ∀ i, ∃ j, le i j ∧ ∃ U, new j U

/-- **Stage-freeze contradiction**: cofinally many fresh subsets of `S`
cannot coexist with an eventual freezing of the `S`-subsets. This is the
class-length consequence of the pollution lemma: unboundedly many `R_ω`
repairs (each adding a fresh `U_α ⊆ S`) are impossible once `P(S)` has
frozen. -/
theorem stage_freeze_contra {I S : Type} {le : I → I → Prop}
    (SF : StageFreeze I S le) : False :=
  let ⟨j, hj, U, hU⟩ := SF.cofinal SF.gamma
  SF.freeze j hj U hU

end PPAC.ClassObstruction
