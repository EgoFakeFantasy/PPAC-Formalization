# PPAC-Formalization

Lean 4 proof components and interface prototypes from research on the Partition Principle (PP) and the Axiom of Choice (AC).

**This is a partial formalization. It does not prove ZF + PP implies AC, construct a model of ZF + PP + not AC, or formalize the complete Cohen, random, or Fuchs-Prikry model theorems.**

The repository contains checked proof terms for pullbacks, transitive-stage capture, well-founded splicing, relational partial-condition extensions, coding-density arguments, and conditional contradictions. Higher-level names identify the motivating research direction, not a completed model-theoretic application.

## Build and audit

Lean is pinned to `leanprover/lean4:v4.33.1`; there are no external Lean packages.

```sh
lake build
lake env lean Audit.lean
python3 scripts/verify.py
```

The verification script rebuilds the library, checks every declaration listed in `Audit.lean`, rejects unauthorized axiom footprints and placeholder constructs, and writes source hashes and logs under `verification/`. The allowed axiom footprint is limited to `propext` and `Quot.sound`. Counts refer to audited declarations, including definitions, not to that many independent mathematical theorems.

## Scope

| Modules | What is checked | What is still missing |
|---|---|---|
| `Pullback`, `StageCapture` | Surjective pullback identity; capture from transitivity and an explicit powerset-like object; eventual stability | Adapters for actual internal sets and proper-class stage chains |
| `Choice` | Host-type well-founded splicing and conditional splitting patterns | A faithful internal interpretation of well-orderability, PP, SVC and choice |
| `Repair` | Relational condition extensions, coding density and coverage implications with explicit input data | Genuine forcing semantics, old/new universe distinction, concrete coding/freshness instances, full projection lifting |
| `ClassObstruction` | Two-branch trace separation, pullback and an explicit freeze/freshness contradiction | SVC slicing and the assembled model-level obstruction |
| `Cohen` | Well-founded descent and a rank two-cycle contradiction | Boolean algebras, Borel maps, acceleration, mixing, locality-to-rank construction |
| `Random` | Finite-list extension/support lemmas and well-order transport | Measure algebras, random forcing, the R139 counterexample |
| `FuchsPrikry` | Abstract data structures and surjective well-order transport | Support ideals modulo finite inclusion, group/filter constructions and the actual equivalence criteria |

**Semantic caution.** `PPAC.Choice.WO X` quantifies over all host relations on a Lean type. It does not restrict relations to members of a choiceless inner model. An axiom-free conditional proof with a hypothesis `not WO X` is therefore not a nonvacuity certificate for a ZF model. Likewise, explicit choice-valued parameters can carry choice content even when `Classical.choice` does not appear in `#print axioms`. The repair modules currently use ambient `Nat -> Bool`; an actual old-real type and model interpretation are missing.

See [coverage](THEOREM_COVERAGE.md), [gaps](GAPS.md), and the [publication review](docs/PUBLICATION_REVIEW.md) for exact limitations and corrections made before publication.

## Provenance and references

Initial implementation: glm5.3f. Publication review, corrections and reproducible verification: Codex. AI implementation/review is not independent human mathematical certification. No mathematical priority is claimed.

Background sources (not imported formal dependencies):
- Thomas Jech, *The Axiom of Choice* (1973), §2.4, Example 2.4.1 and Lemma 2.7: [text](https://gwern.net/doc/math/1973-jech-theaxiomofchoice.pdf).
- C. Ryan-Smith, *Local reflections of choice*, Acta Math. Hungar. 176 (2025), 244–257: [DOI](https://doi.org/10.1007/s10474-025-01533-3).
- A. Karagila, *Iterating Symmetric Extensions*, JSL 84 (2019): [arXiv](https://arxiv.org/abs/1606.06718).

Local task-bus records, private source manuscripts and earlier implementation reports are not included in the public repository.
