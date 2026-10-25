# Remaining migration obligations

Use the original 1–11 stages in docs/AGENT_WORKFLOW.zh-CN.md. Final target remains native `Derives nativeZF [] (Con_ZF → Con_U)`, over every internal proof code, with U = ZF + PP + ACwo + notAC.

1–3 are accepted: complete source syntax/rules and their bidirectional transfer to the original kernel, all ZF schemes and both AC presentations. Do not rebuild or report these as missing.

4: original Lean 4.34.1 Main built (8998 jobs) and five endpoints passed trust=0. Full Comparator remains unverified; local CheckStep4 is a different test.

5–6: internal pairs/graphs/omega/recursion, names, evaluation, map/action laws and check/pair/union constructions are accepted. Concrete source-system presentation and the complete nativeZF L interpretation adapter remain. The newer native YesMetaZFC checkout 7979336 already proves internal L satisfies ZF/ZFC/GCH for arbitrary ZF models, with full schemas. Its version/language/original-kernel integration remains incomplete; the previous inventory limited to ZFSet LCarrier was wrong.

7: constructed atomic recursion/equations/laws, atomic action symmetry, full fixed-formula forcing, all 19-rule fixed-proof soundness and generic formula action symmetry are accepted. The generic formula certificate retains domain-transport hypotheses; ForcingHSAction now discharges them for the actual HS predicate under explicit algebraic contexts.

The earlier ForcingStabilizer/ForcingHS/ForcingHSCheck batch is fully accepted: literal stabilizer subsets, HS internal closed witnesses, exact source recursion equation, uniqueness among definable solutions, empty HS and check HS for all internal sets. It reuses native Collection/Separation/Union/Insert, Child induction and checkName action laws. No external well-foundedness or arbitrary assumed Symmetric predicate.

Remaining in 7: actual PPAC condition/group-action presentation and application of the constructed normal filter; pair/union HS closure; instantiate the proved HS action and formula symmetry certificates with the concrete PPAC algebraic contexts; force every target ZF axiom scheme. Empty/check results retain original top-filter, valid-condition and fixed-action premises, to be supplied by the concrete system.

8–9: migrate the actual source Algebra/Construction and Models chain: monoid/placement/conservative hull, SVC, ACwo, same-model quotient injections and notAC witnesses. All-rank and exact-source hypotheses must be retained.

10: original reverse_injection_dense → forces_PP → forces_target assembly, ZF/U specialization of existing internal proof machinery, reduction of every internal/nonstandard contradiction proof, final object Con implication.

11: final theorem/quantifier/trust/source audit has not started.

Decision density, atomic_truth, exists_truth_generic and byte/packet compatibility are outside the selected direct proof-reduction route. Unintegrated packet candidates and duplicate satisfaction code were retired. Existing audited dependencies are retained; do not use their counts as a progress estimate.

The earlier accepted 47-declaration batch (ForcingNameConjugacy, ForcingStabilizerTransport, ForcingHSAction) is fully accepted: four native certificates, literal stabilizer conjugacy, HS.smul by original Child induction, and actual HS-domain formula symmetry. Concrete group/action/normal-filter instantiation remains unproved; no HS preservation premise was assumed.

The concrete label carrier, unique fixing subsets, identity/inverse/composition witnesses, exact label images and pointwise conjugacy are accepted. ForcingConjugationGraph now constructs the conjugation permutation graph on this carrier, proves the exact image of fixing subgroups, and proves subgroup closure is preserved. Directed build/trust=0 preaudit passed; full verification passed. ForcingSupportSize/ForcingSupportFilter now supply the actual support family, empty/subset/image bounds and top/upward/conjugation clauses. ForcingSupportIntersection/ForcingNormalFilter now prove the finite-union bound, intersection closure and all four normal-filter clauses. Remaining here: actual ProductNames condition action and properness/bot_not_mem when used by ChoiceFailure. The conjugation graph and stabilizer set-image are no longer unproved obligations.

ForcingDiagramAction and ForcingDiagramCarrier now construct all internal injection diagrams and their actual set-level permutation action, with identity/multiplication/inverse laws. ForcingDiagramOrder constructs sub from explicit fixed-left totality/functionality/cancellation and proves preservation/reflection of the literal translation relation. Arbitrary multiplication tables are not claimed to be monoids or to induce partial orders: the source monoid laws and conicality still need stage 8 instantiation. The source Cohen coordinate and condition order permutations are now constructed, but label-group laws, Product/WithTop and full ProductNames.actionHom remain incomplete.

ForcingCohenCoordinates/Conditions/OrderAction construct the actual two product-coordinate permutations, all internally bounded partial-function graphs, the image operation and the condition carrier's reverse-inclusion automorphism. An assembly certificate supplies the actual products/carrier/graphs from a label permutation. General internal B,w specialize to the already available 2,omega; their existence is not a new obligation. Label-action identity/composition coherence and joint Product/WithTop action remain.
