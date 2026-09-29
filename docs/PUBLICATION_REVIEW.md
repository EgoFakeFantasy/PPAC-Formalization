# Publication review — 2026-09-29

The executor delivered eight task reports, but several reported completions were interface-level only. The public scope has been rewritten to reflect actual source signatures.

Corrections before publication:

- Removed the false claim that countable choice need not make an infinite set Dedekind-infinite. Jech, *The Axiom of Choice*, Example 2.4.1 and Lemma 2.7 give the standard implication. The Lean countable-block theorem still has an explicit witness because that implication is not implemented here.
- Restricted `svc_pp_splitting`'s choice argument from all arbitrary index types to types supplied with `OrdIndex`.
- Corrected `DC` to a pointed form so that the empty carrier is handled vacuously, rather than incorrectly requiring a sequence in an empty type.
- Removed the claim that lacking a `CategoryAcc` instance is a formal negative test for R139. No such counterexample is formalized.
- Recorded that `WO` uses all host relations, that rank/freeze contradictions have strong assumed premises, and that `criterion_forward` never consumes ideal hypotheses. These are partial proof components, not completed internal ZF theorems.
- Retained original implementation reports locally but excluded them, agent task records and private manuscripts from publication. Their historical hashes do not describe the corrected source. Current hashes are in `verification/summary.json`.

The review checks source signatures, proof scope, reproducible compilation and printed axiom footprints. It does not certify manuscript novelty or supply the missing model/forcing interpretation.
