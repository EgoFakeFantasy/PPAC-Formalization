/-
Conditional host-level components motivated by the Cohen-locality manuscript.

The checked results are well-founded descent and a contradiction from explicit
rank-decrease and coverage assumptions. In particular, rank_contra receives
premises that directly produce a two-cycle of strict rank inequalities.
This is not a formalization of the manuscript's complete final rank argument:
Cohen Boolean algebras, Borel locality, accelerated two-coloring, delayed
roots, mixing, and the construction of the rank/coverage data remain absent.
No internal ZF model or interpretation of PP is constructed here.
See THEOREM_COVERAGE.md and GAPS.md for the publication scope.
-/

import PPAC.ClassObstruction.Obstruction

namespace PPAC.Cohen

open PPAC.Repair PPAC.ClassObstruction PPAC.Choice

/-! ## The Cohen-locality assumption (LC), interface level -/

/-- Cohen locality (LC, §1 of the source note): every ordinal-set code of
`N` is contained in a single-Cohen root `W[r] ⊆ N` (`rootOf`), and any two
roots fit into a common larger root (`merge`, §2 — iterated to any finite
family). This is the precise hypothesis of the paper theorem; it is kept
as an interface and never discharged. -/
structure CohenLocality (Code Root : Type) where
  above : Root → Root → Prop
  rootOf : Code → Root
  merge : ∀ r₁ r₂ : Root, ∃ r₃, above r₃ r₁ ∧ above r₃ r₂

/-! ## Well-foundedness basics -/

/-- A well-founded relation with a predecessor step at every point and a
nonempty carrier is contradictory (the abstract engine behind exclusion
arguments of the R120/R121 type). -/
theorem wf_desc_false {Q : Type} {R : Q → Q → Prop} (hwf : WellFounded R)
    (hne : Nonempty Q) (hstep : ∀ x, ∃ y, R y x) : False := by
  have key : ∀ x, Acc R x → False := by
    intro x acc
    induction acc with
    | intro z hz ih =>
      cases hstep z with
      | intro y hy => exact ih y hy
  cases hne with
  | intro q0 => exact key q0 (hwf.apply q0)

/-- A two-cycle contradicts well-foundedness: the cycle's two points form
a two-element subrelation with a predecessor step at every point, so
`wf_desc_false` applies to the pullback. -/
theorem wf_two_cycle {Q : Type} {R : Q → Q → Prop} (hwf : WellFounded R)
    {x y : Q} (h1 : R x y) (h2 : R y x) : False := by
  have hsub : ∀ t : {w // w = x ∨ w = y}, ∃ t' : {w // w = x ∨ w = y},
      R t'.1 t.1 := by
    intro t
    cases t.2 with
    | inl he =>
      refine Exists.intro (Subtype.mk y (Or.inr rfl)) ?_
      rw [he]
      exact h2
    | inr he =>
      refine Exists.intro (Subtype.mk x (Or.inl rfl)) ?_
      rw [he]
      exact h1
  have hinj : Function.Injective
      (fun t : {w // w = x ∨ w = y} => t.1) := fun t t' h => Subtype.ext h
  have hwf' := pullback_wf (fun t : {w // w = x ∨ w = y} => t.1) R hwf
  exact wf_desc_false hwf' (Nonempty.intro (Subtype.mk x (Or.inl rfl))) hsub

/-! ## The rank interface of the auxiliary relation -/

/-- The delayed-domain auxiliary relation `q ≺ p` of §3 with its ordinal
rank: the interface states the WF-rank property (the rank strictly
decreases along `aux`) into an ordinal-like index — internally supplied by
the well-foundedness established in §4 via LC, R111/R120/R123. The rank
map and the decrease property are the only features the final argument
uses; `OrdIndex` supplies the ordinal-like structure (least elements,
classical set-many logic) without impersonating the internal ordinals
beyond that interface. -/
structure RankAux (Q I : Type) (rA : OrdIndex I) where
  aux : Q → Q → Prop
  rho : Q → I
  dec : ∀ p q, aux p q → rA.r (rho p) (rho q)

/-- The `H_j` family interface: conditions compatible with the PP-injection
`j` — nonempty, and cofinally covered in rank above the final condition
`pStar`, each covered member a predecessor of `pStar` in the auxiliary
relation (§5: the construction from a common `j` and the merged root). -/
structure HFamily {Q I : Type} (rA : OrdIndex I) (rho : Q → I) (pStar : Q)
    (aux : Q → Q → Prop) where
  H : Q → Prop
  hne : ∃ p, H p
  coverAbove : ∀ i, ∃ p, H p ∧ rA.r i (rho p) ∧ aux p pStar

/-! ## The rank contradiction -/

/-- **The final rank argument (§5), abstractly.** With the rank interface
and the `H_j` family covered cofinally above `pStar` while every covered
member is an `aux`-predecessor of `pStar`, the ranks form a two-cycle
against the well-founded index order — contradiction. This is the
host-level form of `ρ(p*) ≥ δ` versus `ρ(p*) < δ`; the ordinal-sup
selection of §5 (AC_WO) is packaged into `HFamily.coverAbove`, and the
internal rank is packaged into `RankAux.dec` (the WF-rank decrease). -/
theorem rank_contra {Q I : Type} (rA : OrdIndex I) {aux : Q → Q → Prop}
    {ρ : Q → I} (hdec : ∀ p q, aux p q → rA.r (ρ p) (ρ q))
    (pStar : Q) (H : Q → Prop) (hHStar : H pStar)
    (hcover : ∀ i, ∃ p, H p ∧ rA.r i (ρ p) ∧ aux p pStar) :
    False := by
  cases hcover (ρ pStar) with
  | intro p hp =>
    have hdec' : rA.r (ρ p) (ρ pStar) := hdec p pStar hp.2.2
    exact wf_two_cycle rA.r_wf hdec' hp.2.1

end PPAC.Cohen
