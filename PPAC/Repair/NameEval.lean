/-
PPAC/Repair/NameEval.lean — Batch 3, name evaluation and free-injection
collapse.

Part 1 formalizes the SVC-seed preservation step of
`Feferman可数部分注入修复直接恢复AC_核查.md` (¶ "旧 SVC(S) 对任意集合强迫保持
为 SVC(S^M)"): a new nonempty set `X` presented through old names `T` with
an old surjection `σ : S × α ↠ T` and a generic evaluation `ev : T → Option X`
in which every `x ∈ X` has a name, is a surjective image of `S × α` — the
evaluation map is CONSTRUCTED as data — and if `S` carries a well-order
with a least-element selector, `X` is well-orderable by least preimages.

Part 2 formalizes the general repair mechanism (same note, ¶2): free
partial injections `B ⇀ A` with an old map `ρ : B → S`, a fresh `ρ`-fiber
point and a fresh value of the old pool `W` available at every condition;
the dense sets `D_s` make the generic injection's `W`-preimages map onto
`S` — relationally: `S` becomes a surjective image of (a subset of) `W`.

BOUNDARY: `ev` (the generic name evaluation) and the fresh-pool interfaces
are hypotheses standing in for the ground-model/forcing adapter, which is
NOT formalized in this batch; the relational collapse becomes the internal
surjection `h : I ↠ S` by Replacement inside ZF (remaining bridge). No
claim of `PP ⇒ AC`, no countermodel, no priority.

Axiom discipline: no `sorry`, no custom `axiom`, no `Classical.choice`.
-/

import PPAC.Repair.Parity

namespace PPAC.Repair

open PPAC.Choice

/-! ## Well-orders with a least-element selector -/

/-- A well-order carrying its least-element selector as data. Uniqueness
of the least element is provable (`least_unique`-style), so this is
object-level definite description, not choice; it is a hypothesis, never
an axiom. -/
structure WOrd (S : Type) where
  r : S → S → Prop
  r_trich : Trich r
  r_wf : WellFounded r
  r_least : ∀ p : S → Prop, (∃ i, p i) → {m : S // p m ∧ ∀ i, p i → ¬ r i m}

/-! ## The product lexicographic order on `S × α` -/

/-- Lexicographic order on `S × α`: compare second coordinates first
(the stage), then the well-order of `S` inside a stage. -/
def prodLex {S A : Type} (rS : S → S → Prop) (rA : A → A → Prop)
    (p q : S × A) : Prop :=
  spliceRel rA (Prod.snd) (fun _a x y _ _ => rS x.1 y.1) p q

theorem fiberTrich {S A : Type} {rS : S → S → Prop} (hS : Trich rS) (a : A) :
    Trich (FiberRel (Prod.snd : S × A → A) (fun _a x y _ _ => rS x.1 y.1) a) := by
  intro p q
  cases hS p.1.1 q.1.1 with
  | inl h => exact Or.inl h
  | inr h =>
    cases h with
    | inl h =>
      exact Or.inr (Or.inl (Subtype.ext (Prod.ext h (p.2.trans q.2.symm))))
    | inr h => exact Or.inr (Or.inr h)

theorem prodLex_trich {S A : Type} {rS : S → S → Prop} {rA : A → A → Prop}
    (hS : Trich rS) (hA : Trich rA) : Trich (prodLex rS rA) :=
  splice_trich rA (Prod.snd) _ hA (fun a => fiberTrich hS a)

theorem prodLex_wf {S A : Type} {rS : S → S → Prop} {rA : A → A → Prop}
    (hwfS : WellFounded rS) (hwfA : WellFounded rA) : WellFounded (prodLex rS rA) :=
  splice_wf rA (Prod.snd) (fun _a x y _ _ => rS x.1 y.1) hwfA
    (fun a => pullback_wf (fun t : {z : S × A // z.2 = a} => t.1.1) rS hwfS)

/-- The least `p`-element of `S × α` in the product order: least stage
first, least point inside the stage. -/
def prodLexLeast {S A : Type} (rS : WOrd S) (rA : OrdIndex A)
    {p : S × A → Prop} (h : ∃ z, p z) :
    {m : S × A // p m ∧ ∀ z, p z → ¬ prodLex rS.r rA.r z m} := by
  have hA : ∃ a, ∃ s, p (s, a) := by
    cases h with
    | intro z hz => exact ⟨z.2, z.1, hz⟩
  cases rA.leastSel (fun a => ∃ s, p (s, a)) hA with
  | mk α₀ hα₀ =>
    have hs₀ : ∃ s, p (s, α₀) := hα₀.1
    cases rS.r_least (fun s => p (s, α₀)) hs₀ with
    | mk s₀ hs₀' =>
      refine ⟨(s₀, α₀), hs₀'.1, ?_⟩
      intro z hz hlex
      cases hlex with
      | inl h1 =>
        have hz2 : (fun a => ∃ s, p (s, a)) z.2 := ⟨z.1, hz⟩
        exact absurd h1 (hα₀.2 z.2 hz2)
      | inr h2 =>
        cases h2 with
        | intro he hs =>
          have he2 : z = (z.1, α₀) := Prod.ext rfl he
          rw [he2] at hz
          exact hs₀'.2 z.1 hz hs

/-! ## Name evaluation: the fixed SVC seed survives set forcing -/

/-- A new set `X` whose names `T` are covered by an old surjection
`σ : S × α ↠ T` and whose generic evaluation `ev` names every element, is
a surjective image of `S × α`. The evaluation map is constructed as data:
send each `(s, γ)` to the evaluated name, with a default `x₀ ∈ X` for
non-valued names. No choice is used anywhere. -/
theorem svc_name_eval {S A T X : Type} (σ : S × A → T) (hsurj : Function.Surjective σ)
    (ev : T → Option X) (hnamed : ∀ x, ∃ t, ev t = some x) (x₀ : X) :
    Function.Surjective (fun z : S × A => Option.getD (ev (σ z)) x₀) := by
  intro x
  cases hnamed x with
  | intro t ht =>
    cases hsurj t with
    | intro z hz =>
      refine ⟨z, ?_⟩
      show Option.getD (ev (σ z)) x₀ = x
      rw [hz, ht]
      rfl

/-- With a selected well-order of `S` and an ordinal-like index `α`, any
surjection `σ : S × α ↠ X` makes `X` well-orderable: order `X` by the least
preimage (constructed from the two least-element selectors). -/
theorem wo_of_surjection {S A X : Type} (rS : WOrd S) (rA : OrdIndex A)
    (σ : S × A → X) (hsurj : Function.Surjective σ) : WO X := by
  have hlp : ∀ x, {m : S × A // σ m = x ∧ ∀ z, σ z = x → ¬ prodLex rS.r rA.r z m} :=
    fun x => prodLexLeast rS rA (hsurj x)
  have hginj : Function.Injective (fun x => (hlp x).1) := by
    intro x x' he
    have hσ : σ ((hlp x).1) = σ ((hlp x').1) := congrArg σ he
    exact (hlp x).2.1.symm.trans (hσ.trans (hlp x').2.1)
  refine ⟨fun x x' => prodLex rS.r rA.r (hlp x).1 (hlp x').1,
    pullback_trich _ _ (prodLex_trich rS.r_trich rA.r_trich) hginj,
    pullback_wf _ _ (prodLex_wf rS.r_wf rA.r_wf)⟩

/-! ## The free partial-injection collapse -/

/-- A countable partial injection `B ⇀ A`, relationally: functional,
backward-injective, with a countable domain cover. -/
structure InjCnt (B A : Type) where
  rel : B → A → Prop
  funi : ∀ b a a', rel b a → rel b a' → a = a'
  inj : ∀ b b' a, rel b a → rel b' a → b = b'
  cnt : ∃ c : Cover B, ∀ b a, rel b a → ∃ d, c.w d = b

/-- Extension order on countable partial injections. -/
def InjCntLe {B A : Type} (p p' : InjCnt B A) : Prop :=
  ∀ b a, p.rel b a → p'.rel b a

/-- The generic union of a directed family of countable partial
injections. -/
def jrelInj {B A : Type} (G : InjCnt B A → Prop) (b : B) (a : A) : Prop :=
  ∃ p : InjCnt B A, G p ∧ p.rel b a

/-- The fresh-pool interfaces of the general mechanism (¶2 of the source
note): every `ρ`-fiber has a point outside any given condition's domain,
and the old pool `W` always has a value outside any condition's range. -/
structure FreshPool {B A S W : Type} (ρ : B → S) (wA : W → A) where
  fib_fresh : ∀ (p : InjCnt B A) (s : S), ∃ b, ρ b = s ∧ ∀ a, ¬ p.rel b a
  W_fresh : ∀ (p : InjCnt B A), ∃ w, ∀ b : B, ¬ p.rel b (wA w)

/-- **Density of `D_s`**: from any condition, a fresh fiber point `b` of
`ρ(b) = s` and a fresh pool value `wA w` can be added simultaneously. -/
theorem denseD_s {B A S W : Type} {ρ : B → S} {wA : W → A}
    (FP : FreshPool ρ wA) (p : InjCnt B A) (s : S) :
    ∃ p' : InjCnt B A, InjCntLe p p' ∧ ∃ b w, ρ b = s ∧ p'.rel b (wA w) := by
  cases FP.fib_fresh p s with
  | intro b hb =>
    cases FP.W_fresh p with
    | intro w hw =>
      refine ⟨⟨fun bb a => p.rel bb a ∨ (bb = b ∧ a = wA w), ?_, ?_, ?_⟩,
        (fun bb a hba => Or.inl hba), b, w, hb.1, Or.inr ⟨rfl, rfl⟩⟩
      · -- functionality: the fresh point `b` is outside dom(p)
        intro bb a a' h₁ h₂
        cases h₁ with
        | inl h₁ =>
          cases h₂ with
          | inl h₂ => exact p.funi bb a a' h₁ h₂
          | inr h₂ => exact absurd (h₂.1 ▸ h₁) (hb.2 a)
        | inr h₁ =>
          cases h₂ with
          | inl h₂ => exact absurd (h₁.1 ▸ h₂) (hb.2 a')
          | inr h₂ => exact h₁.2.trans h₂.2.symm
      · -- backward injectivity: the pool value is outside ran(p)
        intro bb bb' a h₁ h₂
        cases h₁ with
        | inl h₁ =>
          cases h₂ with
          | inl h₂ => exact p.inj bb bb' a h₁ h₂
          | inr h₂ => exact absurd (h₂.2 ▸ h₁) (hw bb)
        | inr h₁ =>
          cases h₂ with
          | inl h₂ => exact absurd (h₁.2 ▸ h₂) (hw bb')
          | inr h₂ => exact h₁.1.trans h₂.1.symm
      · -- countable coverage of the domain
        cases p.cnt with
        | intro c hcov =>
          refine ⟨Cover.mk (c.D ⊕ Unit) (countable_sum c.hD
            ⟨fun _ => 0, fun x y _ => Subsingleton.elim x y⟩)
            (Sum.elim c.w (fun _ => b)), ?_⟩
          intro bb a hba
          cases hba with
          | inl h =>
            cases hcov bb a h with
            | intro d hd =>
              refine ⟨Sum.inl d, ?_⟩
              show c.w d = bb
              exact hd
          | inr h =>
            refine ⟨Sum.inr Unit.unit, ?_⟩
            show b = bb
            rw [← h.1]

/-- **Collapse (relational).** A directed family `G` meeting every `D_s`
makes the generic injection's `W`-preimages cover `S` along `ρ`: for each
`s` there are `w` and `b` with `ρ(b) = s` and the generic union pairing
`b ↦ wA w`. Internally `h(w) = ρ(j⁻¹(w))` is a surjection from a subset of
the well-orderable pool `W` onto `S`, so `S` becomes well-orderable. -/
theorem collapse_free {B A S W : Type} {ρ : B → S} {wA : W → A}
    (FP : FreshPool ρ wA)
    (G : InjCnt B A → Prop)
    (hmeet : ∀ s, ∃ p, G p ∧ ∃ b w, ρ b = s ∧ p.rel b (wA w)) :
    ∀ s, ∃ w b, ρ b = s ∧ jrelInj G b (wA w) := by
  intro s
  cases hmeet s with
  | intro p hp =>
    cases hp.2 with
    | intro b hw =>
      cases hw with
      | intro w hw' =>
        cases hw' with
        | intro hρ hrel =>
          exact ⟨w, b, hρ, Exists.intro p (And.intro hp.1 hrel)⟩

/-- The generic `ρ`-preimage of a pool value is unique (functionality of
the internal map `h`). -/
theorem collapse_free_fun {B A S W : Type} {ρ : B → S} {wA : W → A}
    (G : InjCnt B A → Prop)
    (hdir : ∀ p p', G p → G p' → ∃ p'' : InjCnt B A, G p'' ∧
      InjCntLe p p'' ∧ InjCntLe p' p'')
    {w : W} {s s' : S} {b b' : B}
    (h₁ : jrelInj G b (wA w)) (h₂ : jrelInj G b' (wA w)) (h₁' : ρ b = s)
    (h₂' : ρ b' = s') : s = s' := by
  have hbb := jrelOf_injDir (fun p'' bb bb' a => p''.inj bb bb' a) hdir h₁ h₂
  rw [← h₁', ← h₂', hbb]

end PPAC.Repair
