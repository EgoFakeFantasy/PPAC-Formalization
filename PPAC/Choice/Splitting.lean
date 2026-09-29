/-
PPAC/Choice/Splitting.lean — Batch 2, the non-well-ordered splitting lemma.

Source: `PP与SVC种子的非良序分裂必要条件_核查.md` (2026-09-27) in the
read-only research directory. Formalizes the paper argument:

In `ZF + AC_WO`, if `S` is not well-orderable and `j : S×S ↪ S×I` is an
injection into `S ×` (ordinal-like index), then there is a non-well-
orderable index class `A_β ⊆ S` and a family of pairwise disjoint non-
well-orderable blocks `P_s ⊆ S` indexed by `s ∈ A_β`.

Proof skeleton (all steps below are real proof terms):
1. For fixed `s`, splicing well-orders of the fibers `F_{s,β} = {t :
   (j(s,t)).2 = β}` along `I` would well-order `S`; hence some fiber is
   non-well-orderable (object-level classical logic of the index family is
   the `OrdIndex.classical` interface field).
2. `minBadIdx s` is the LEAST non-well-orderable fiber index of `s` —
   uniqueness of the least element makes this a definition (definite
   description), avoiding any choice over `S`.
3. If every index class `A_β = {s : minBadIdx s = β}` were well-orderable,
   splicing again would well-order `S`; hence some `A_β` is not.
4. For `s ∈ A_β`, the first-coordinate projection maps `F_{s,β}`
   bijectively onto the block `P_s`; a well-order of `P_s` would pull back
   to one of `F_{s,β}`. Distinct `s, s' ∈ A_β` have disjoint blocks: a
   common element forces `j(s,t) = (x,β) = j(s',t')`, contradicting
   injectivity.
5. Countable sub-family: with an explicit Dedekind-infiniteness witness
   `g : ℕ ↪ A_β` the blocks `(P_{g n})_n` are countably many pairwise
   disjoint non-well-orderable sets. The witness remains an explicit
   input because its derivation from countable choice is not formalized
   here. In ZF, countable choice DOES imply that every infinite set has
   a countably infinite subset; the source note was correct on this point.
6. `SVC(S) + PP` reverses the SVC surjection `S × I ↠ S × S` into the
   injection `S × S ↪ S × I` and applies the lemma.

BOUNDARY: everything is at the host-type level. `OrdIndex`, `AC_WO`, `PP`,
`SVC` are explicit hypotheses; no `Classical.choice` is used anywhere in
this file (object-level classical logic enters only through the
`OrdIndex` interface fields). No claim is made about ZF + PP → AC, about
countermodels, or about the forcing/SVC steps of the source argument.

Axiom discipline: no `sorry`, no custom `axiom`, no `Classical.choice`.
-/

import PPAC.Choice.Splice

namespace PPAC.Choice

/-! ## Fibers and blocks of an injection `j : S × S → S × I` -/

/-- The second-coordinate section of `j` at a fixed first coordinate. -/
def sec {S I : Type} (j : S × S → S × I) (s t : S) : I := (j (s, t)).2

/-- The `β`-fiber of `j` at `s`: `F_{s,β} = {t ∈ S : π₂(j(s,t)) = β}`. -/
def Fiber {S I : Type} (j : S × S → S × I) (s : S) (β : I) : Type :=
  {t : S // (j (s, t)).2 = β}

/-- Block membership: `x ∈ P_s` iff `x = π₁(j(s,t))` for some `t` in the
`β`-fiber of `s`. -/
def BlockMem {S I : Type} (j : S × S → S × I) (β : I) (s x : S) : Prop :=
  ∃ t : S, (j (s, t)).2 = β ∧ (j (s, t)).1 = x

/-- The block `P_s` as a type. -/
def Block {S I : Type} (j : S × S → S × I) (β : I) (s : S) : Type :=
  {x : S // BlockMem j β s x}

/-- The canonical map `F_{s,β} → P_s`, `t ↦ π₁(j(s,t))`. -/
def blockFwd {S I : Type} (j : S × S → S × I) (β : I) (s : S)
    (t : Fiber j s β) : Block j β s :=
  Subtype.mk (j (s, t.1)).1 (Exists.intro t.1 (And.intro t.2 rfl))

/-- Injectivity of `t ↦ π₁(j(s,t))` on the fiber (uses `j` injective and
the constant second coordinate `β`). -/
theorem blockFwd_inj {S I : Type} {j : S × S → S × I} {β : I} {s : S}
    (hinj : Function.Injective j) : Function.Injective (blockFwd j β s) := by
  intro t t' he
  unfold blockFwd at he
  have he1 : (j (s, t.1)).1 = (j (s, t'.1)).1 := congrArg Subtype.val he
  have e1 : j (s, t.1) = j (s, t'.1) := by
    have h1 : j (s, t.1) = ((j (s, t.1)).1, (j (s, t.1)).2) := Prod.eta _
    have h2 : j (s, t'.1) = ((j (s, t'.1)).1, (j (s, t'.1)).2) := Prod.eta _
    rw [h1, h2, he1, t.2, t'.2]
  exact Subtype.ext (congrArg Prod.snd (hinj e1))

/-! ## Pullback of a well-order along an injection -/

/-- Trichotomy pulls back along an injective map. -/
theorem pullback_trich {X Y : Type} (g : X → Y) (rY : Y → Y → Prop)
    (htri : Trich rY) (hg : Function.Injective g) :
    Trich (fun x x' => rY (g x) (g x')) := by
  intro x x'
  cases htri (g x) (g x') with
  | inl h => exact Or.inl h
  | inr h =>
    cases h with
    | inl h => exact Or.inr (Or.inl (hg h))
    | inr h => exact Or.inr (Or.inr h)

/-- Well-foundedness pulls back along any map. -/
theorem pullback_wf {X Y : Type} (g : X → Y) (rY : Y → Y → Prop)
    (hwf : WellFounded rY) : WellFounded (fun x x' => rY (g x) (g x')) := by
  have key : ∀ y, Acc rY y → ∀ x, g x = y → Acc (fun x x' => rY (g x) (g x')) x := by
    intro y accY
    induction accY with
    | intro y' _ ih =>
      intro x hx
      refine Acc.intro x (fun x' hx' => ?_)
      have hx2 : rY (g x') y' := by rw [hx] at hx'; exact hx'
      exact ih (g x') hx2 x' rfl
  exact ⟨fun x => key (g x) (hwf.apply (g x)) x rfl⟩

/-- If the block `P_s` were well-orderable, the fiber `F_{s,β}` would be
too (pullback along the injective projection). -/
theorem fiber_wo_of_block_wo {S I : Type} {j : S × S → S × I} {β : I} {s : S}
    (hinj : Function.Injective j) (h : WO (Block j β s)) :
    WO (Fiber j s β) := by
  cases h with
  | intro r hr =>
    refine ⟨fun t t' => r (blockFwd j β s t) (blockFwd j β s t'),
      pullback_trich _ _ hr.1 (blockFwd_inj hinj),
      pullback_wf _ _ hr.2⟩

/-- Disjointness: distinct `s ≠ s'` (in the same index class `A_β`) have
disjoint blocks. -/
theorem block_disjoint {S I : Type} {j : S × S → S × I} {β : I} {s s' : S}
    (hinj : Function.Injective j) (hne : s ≠ s') :
    ¬ ∃ x : S, BlockMem j β s x ∧ BlockMem j β s' x := by
  intro hx
  cases hx with
  | intro x hx =>
    cases hx with
    | intro ht ht' =>
      cases ht with
      | intro t ht =>
        cases ht with
        | intro ht2 ht1 =>
          cases ht' with
          | intro t' ht' =>
            cases ht' with
            | intro ht2' ht1' =>
              have e1 : j (s, t) = (x, β) := by
                rw [← Prod.eta (j (s, t)), ht1, ht2]
              have e2 : j (s', t') = (x, β) := by
                rw [← Prod.eta (j (s', t')), ht1', ht2']
              exact hne (congrArg Prod.fst (hinj (e1.trans e2.symm)))

/-! ## The least non-well-orderable fiber index -/

/-- For every `s`, some fiber `F_{s,β}` is not well-orderable: otherwise
the spliced fiber well-orders would well-order `S`. -/
theorem badFiberExists {S I : Type} (j : S × S → S × I)
    (IX : OrdIndex I) (hAC : AC_WO I) (hS : ¬ WO S) (s : S) :
    ∃ β, ¬ WO (Fiber j s β) := by
  have hall : (∀ β, WO (Fiber j s β)) → WO S :=
    partition_splice_wo IX.r IX.r_trich IX.r_wf (sec j s) hAC
  exact IX.classical (fun β => WO (Fiber j s β)) (fun hAll => hS (hall hAll))

/-- The least non-well-orderable fiber index of `s` — a definition, not a
choice: the least element is unique, so this is object-level definite
description packaged as the `OrdIndex.leastSel` interface field. -/
def minBadIdx {S I : Type} (j : S × S → S × I)
    (IX : OrdIndex I) (hAC : AC_WO I) (hS : ¬ WO S) (s : S) : I :=
  (IX.leastSel (fun β => ¬ WO (Fiber j s β)) (badFiberExists j IX hAC hS s)).1

/-- The least bad fiber index is bad. -/
theorem minBadIdx_bad {S I : Type} (j : S × S → S × I)
    (IX : OrdIndex I) (hAC : AC_WO I) (hS : ¬ WO S) (s : S) :
    ¬ WO (Fiber j s (minBadIdx j IX hAC hS s)) :=
  (IX.leastSel (fun β => ¬ WO (Fiber j s β)) (badFiberExists j IX hAC hS s)).2.1

/-! ## The splitting theorem -/

/-- **Non-well-ordered splitting lemma** (Batch 2 main theorem). Under the
stated interfaces: if `S` is not well-orderable and `j : S×S ↪ S×I`, then
for some `β` the index class `A_β = {s : minBadIdx s = β}` is not well-
orderable, and the blocks `P_s` (`s ∈ A_β`) are non-well-orderable and
pairwise disjoint. -/
theorem nonwo_splitting {S I : Type} (j : S × S → S × I)
    (IX : OrdIndex I) (hAC : AC_WO I) (hinj : Function.Injective j)
    (hS : ¬ WO S) :
    ∃ β : I, ¬ WO {s : S // minBadIdx j IX hAC hS s = β} ∧
      (∀ s : {s : S // minBadIdx j IX hAC hS s = β},
          ¬ WO (Block j β s.1)) ∧
      (∀ s s' : {s : S // minBadIdx j IX hAC hS s = β}, s.1 ≠ s'.1 →
          ¬ ∃ x : S, BlockMem j β s.1 x ∧ BlockMem j β s'.1 x) := by
  have hall : (∀ β, WO {s : S // minBadIdx j IX hAC hS s = β}) → WO S :=
    partition_splice_wo IX.r IX.r_trich IX.r_wf (minBadIdx j IX hAC hS) hAC
  have hex : ∃ β, ¬ WO {s : S // minBadIdx j IX hAC hS s = β} :=
    IX.classical (fun β => WO {s : S // minBadIdx j IX hAC hS s = β})
      (fun hAll => hS (hall hAll))
  cases hex with
  | intro β hβ =>
    refine ⟨β, hβ, ?_, ?_⟩
    · intro s
      have hbad := minBadIdx_bad j IX hAC hS s.1
      rw [s.2] at hbad
      intro hblock
      exact hbad (fiber_wo_of_block_wo hinj hblock)
    · intro s s' hne
      exact block_disjoint hinj hne

/-- **Countable sub-family.** With an explicit Dedekind-infiniteness
witness `g : ℕ ↪ S` whose image lies in the index class `A_β`, the blocks
`P_{g n}` form a countable pairwise disjoint family of non-well-orderable
sets. Deriving the witness from the appropriate countable choice
principle is not implemented here; this is a coverage gap, not an error
in the source implication.) -/
theorem countable_blocks {S I : Type} (j : S × S → S × I)
    (IX : OrdIndex I) (hAC : AC_WO I) (hinj : Function.Injective j) (hS : ¬ WO S)
    (β : I) (g : ℕ → S) (hg : Function.Injective g)
    (hgr : ∀ n, minBadIdx j IX hAC hS (g n) = β) :
    (∀ n : ℕ, ¬ WO (Block j β (g n))) ∧
    ∀ n m : ℕ, n ≠ m → ¬ ∃ x : S, BlockMem j β (g n) x ∧ BlockMem j β (g m) x := by
  refine ⟨fun n => ?_, fun n m hnm => ?_⟩
  · have hbad := minBadIdx_bad j IX hAC hS (g n)
    rw [hgr n] at hbad
    intro hblock
    exact hbad (fiber_wo_of_block_wo hinj hblock)
  · exact block_disjoint hinj (fun he => hnm (hg he))

/-- **PP + SVC application.** `SVC(S)` provides a surjection
`S × I ↠ S × S` with ordinal-like `I`; `PP` reverses it into an injection
`S × S ↪ S × I`; the splitting lemma applies. The ambient `AC_WO` is the
interface restricted to index types carrying `OrdIndex`. This is still
a host-type proof pattern, not an internal ZF interpretation. -/
theorem svc_pp_splitting {S : Type} (hSVC : SVC S) (hPP : PP)
    (hAC : ∀ I : Type, OrdIndex I → AC_WO I) (hS : ¬ WO S) :
    ∃ (I : Type) (IX : OrdIndex I) (j : S × S → S × I),
      Function.Injective j ∧
      ∃ β : I, ¬ WO {s : S // minBadIdx j IX (hAC I IX) hS s = β} ∧
        (∀ s : {s : S // minBadIdx j IX (hAC I IX) hS s = β},
            ¬ WO (Block j β s.1)) ∧
        (∀ s s' : {s : S // minBadIdx j IX (hAC I IX) hS s = β}, s.1 ≠ s'.1 →
            ¬ ∃ x : S, BlockMem j β s.1 x ∧ BlockMem j β s'.1 x) := by
  cases hSVC (S × S) with
  | intro I hex =>
    cases hex with
    | intro IX hex =>
      cases hex with
      | intro f hsurj =>
        cases hPP (S × I) (S × S) f hsurj with
        | intro j hj =>
          exact ⟨I, IX, j, hj, nonwo_splitting j IX (hAC I IX) hj hS⟩
