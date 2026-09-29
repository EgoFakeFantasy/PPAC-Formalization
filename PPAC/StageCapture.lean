/-
PPAC/StageCapture.lean — Batch 1, part B.

Capture and eventual stabilization of the Final `s`-subsets at a transitive
stage, and the impossibility of cofinally many fresh Final `s`-subsets.

Universe bound: `I` and `V` are ordinary Lean types (universes `κ`, `μ`).
They are NOT an internal object-level proper class of all ordinals, and no
ZF universe, class theory, powerset axiom or forcing machinery is encoded
here. `Stage` and `Final` are predicates on `V`; `mem` is an abstract
binary membership relation.

Labeled hypothesis (one-sided powerset membership): `FinalSubsetsInFinal`
says every Final `s`-subset is a *member of the fixed Final object `p`*.
An actual ZF powerset `P(s)` captured at a stage would supply such a `p`,
but the ZF adapter is NOT formalized in this batch — this hypothesis is
abstract input, visibly stated, not derived.

Axiom discipline: no `sorry`, no custom `axiom`, no `Classical.choice`.
All proofs proceed by explicit existential elimination and case analysis.
-/

namespace PPAC

/-! ## Internal subset and stage structure -/

/-- Internal subset: `u ⊆ s` when every member of `u` is a member of `s`. -/
def ssub {V : Type μ} (mem : V → V → Prop) (s u : V) : Prop :=
  ∀ z, mem z u → mem z s

/-- Stage `i` is transitive: every member of a member of `Stage i` is again
in `Stage i`. -/
def StageTransitive {V : Type μ} {I : Type κ} (mem : V → V → Prop)
    (Stage : I → V → Prop) (i : I) : Prop :=
  ∀ x, Stage i x → ∀ y, mem y x → Stage i y

/-- Explicit stage monotonicity with respect to an explicit order `le` on
stage indices. -/
def StageMonotone {V : Type μ} {I : Type κ} (Stage : I → V → Prop)
    (le : I → I → Prop) : Prop :=
  ∀ i j x, le i j → Stage i x → Stage j x

/-- **One-sided powerset membership hypothesis (labeled).** Every Final
`s`-subset `u` is a member of the fixed Final object `p`. See module
docstring: this is abstract input; a ZF powerset would supply `p`, but the
ZF adapter is out of scope for this batch. -/
def FinalSubsetsInFinal {V : Type μ} (mem : V → V → Prop) (Final : V → Prop)
    (s p : V) : Prop :=
  ∀ u, Final u → ssub mem s u → mem u p

/-- "Cofinally many fresh Final `s`-subsets": arbitrarily late stages miss
some Final `s`-subset. The theorems below show this is impossible under
capture + monotonicity. -/
def CofinallyFresh {V : Type μ} {I : Type κ} (Stage : I → V → Prop)
    (le : I → I → Prop) (Final : V → Prop) (mem : V → V → Prop) (s : V) : Prop :=
  ∀ i, ∃ j, le i j ∧ ∃ u, Final u ∧ ssub mem s u ∧ ¬ Stage j u

/-! ## Capture at a single stage -/

/-- Every Final object is captured by *some* stage; the Final `s`-subsets are
all members of one Final object `p`. Then a **single** stage — namely any
stage capturing `p` — already contains every Final `s`-subset. This is not
assumed: it follows from stage transitivity applied to `mem u p`. -/
theorem single_stage_capture {V : Type μ} {I : Type κ}
    {mem : V → V → Prop} {Stage : I → V → Prop} {Final : V → Prop} {s : V}
    (hTrans : ∀ i, StageTransitive mem Stage i)
    (hCaptured : ∀ x, Final x → ∃ i, Stage i x)
    (p : V) (hpFin : Final p) (hp : FinalSubsetsInFinal mem Final s p) :
    ∃ i, ∀ u, Final u → ssub mem s u → Stage i u :=
  match hCaptured p hpFin with
  | ⟨i₀, hp₀⟩ =>
    ⟨i₀, fun u huF huS => hTrans i₀ p hp₀ u (hp u huF huS)⟩

/-! ## Eventual stability -/

/-- With explicit stage monotonicity, single-stage capture upgrades to
eventual stability: some stage `j₀` has the property that **all later**
stages contain every Final `s`-subset. -/
theorem eventual_stability {V : Type μ} {I : Type κ}
    {mem : V → V → Prop} {Stage : I → V → Prop} {Final : V → Prop} {s : V}
    {le : I → I → Prop}
    (hMono : StageMonotone Stage le)
    (hSingle : ∃ i, ∀ u, Final u → ssub mem s u → Stage i u) :
    ∃ j₀, ∀ j, le j₀ j → ∀ u, Final u → ssub mem s u → Stage j u :=
  match hSingle with
  | ⟨j₀, hj₀⟩ =>
    ⟨j₀, fun j hle u huF huS => hMono j₀ j u hle (hj₀ u huF huS)⟩

/-! ## No cofinally many fresh Final `s`-subsets -/

/-- Capture + monotonicity rule out cofinally many fresh Final `s`-subsets:
stabilization at `j₀` produces, from each fresh subset beyond `j₀`, a member
of a stage that provably contains it. -/
theorem not_cofinal_fresh {V : Type μ} {I : Type κ}
    {mem : V → V → Prop} {Stage : I → V → Prop} {Final : V → Prop} {s : V}
    {le : I → I → Prop}
    (hStable : ∃ j₀, ∀ j, le j₀ j → ∀ u, Final u → ssub mem s u → Stage j u)
    (hFresh : ∀ i, ∃ j, le i j ∧ ∃ u, Final u ∧ ssub mem s u ∧ ¬ Stage j u) :
    False :=
  match hStable with
  | ⟨j₀, hj₀⟩ =>
    match hFresh j₀ with
    | ⟨j, hle, u, huF, huS, huNot⟩ => huNot (hj₀ j hle u huF huS)

/-- Contrapositive packaging of `not_cofinal_fresh`. -/
theorem not_cofinal_fresh_of_stability {V : Type μ} {I : Type κ}
    {mem : V → V → Prop} {Stage : I → V → Prop} {Final : V → Prop} {s : V}
    {le : I → I → Prop}
    (hStable : ∃ j₀, ∀ j, le j₀ j → ∀ u, Final u → ssub mem s u → Stage j u) :
    ¬ CofinallyFresh Stage le Final mem s :=
  fun hFresh => not_cofinal_fresh hStable hFresh

/-! ## Nonvacuity: a finite transitive membership structure

`ExObj` has three objects `o0 = ∅`, `o1 = {o0}`, `o2 = {o0, o1}` (von Neumann
style, concrete `mem` table). Stages `st0 = {o0, o1}`, `st1 = {o0, o1, o2}`,
ordered `st0 ≤ st1`. `Final = {o1, o2}`, `s = o1`, `p = o2`.

All interfaces are satisfied and the conclusions are non-vacuous: there is a
genuine Final `s`-subset (`u = o1`), it is a genuine member of `p = o2`, and
the capturing stage contains it. -/

inductive ExObj : Type where
  | o0 | o1 | o2

def exMem : ExObj → ExObj → Prop :=
  fun z x =>
    match x with
    | .o0 => False
    | .o1 => z = .o0
    | .o2 => z = .o0 ∨ z = .o1

inductive ExIx : Type where
  | st0 | st1

def exStage : ExIx → ExObj → Prop :=
  fun i x =>
    match i with
    | .st0 =>
      match x with
      | .o0 => True
      | .o1 => True
      | .o2 => False
    | .st1 => True

def exFinal : ExObj → Prop :=
  fun x =>
    match x with
    | .o0 => False
    | .o1 => True
    | .o2 => True

def exLe : ExIx → ExIx → Prop :=
  fun i j =>
    match j with
    | .st1 => True
    | .st0 =>
      match i with
      | .st0 => True
      | .st1 => False

/-- Both concrete stages are transitive. -/
theorem example_stage_transitive : ∀ i, StageTransitive exMem exStage i := by
  intro i x hx y hy
  cases i with
  | st0 =>
    cases x with
    | o0 => exact False.elim hy
    | o1 =>
      cases hy
      exact trivial
    | o2 => exact False.elim hx
  | st1 => exact trivial

/-- Every Final object is captured by some stage. -/
theorem example_captured : ∀ x, exFinal x → ∃ i, exStage i x := by
  intro x hx
  cases x with
  | o0 => exact False.elim hx
  | o1 => exact ⟨.st0, trivial⟩
  | o2 => exact ⟨.st1, trivial⟩

/-- The one-sided powerset membership hypothesis holds with `s = o1`,
`p = o2`: the only Final `o1`-subset is `o1` itself (`o2 ⊄ o1`), and
`mem o1 o2` holds. -/
theorem example_final_subsets_in_final :
    FinalSubsetsInFinal exMem exFinal .o1 .o2 := by
  intro u hu huS
  cases u with
  | o0 => exact False.elim hu
  | o1 => exact Or.inr rfl
  | o2 => exact absurd (huS .o1 (Or.inr rfl)) (fun h => ExObj.noConfusion h)

/-- Explicit stage monotonicity holds for the concrete order. -/
theorem example_monotone : StageMonotone exStage exLe := by
  intro i j x hle hx
  cases j with
  | st1 => exact trivial
  | st0 =>
    cases i with
    | st0 => exact hx
    | st1 => exact False.elim hle

/-- Instantiating `single_stage_capture` on the concrete structure: stage
`st1` (which captures `p = o2`) contains the Final `s`-subset `o1`. -/
theorem example_single_capture :
    ∃ i, ∀ u, exFinal u → ssub exMem .o1 u → exStage i u :=
  single_stage_capture (hTrans := example_stage_transitive)
    (hCaptured := example_captured)
    (p := .o2) (hpFin := trivial)
    (hp := example_final_subsets_in_final)

/-- Instantiating the full chain: the concrete structure admits no cofinally
fresh Final `s`-subsets. -/
theorem example_no_cofinal_fresh :
    ¬ CofinallyFresh exStage exLe exFinal exMem .o1 :=
  not_cofinal_fresh_of_stability
    (hStable := eventual_stability (hMono := example_monotone)
      example_single_capture)

end PPAC
