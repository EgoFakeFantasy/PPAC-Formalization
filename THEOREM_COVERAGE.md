# Migration coverage (2026-10-26)

The authoritative original stages are in docs/AGENT_WORKFLOW.zh-CN.md. Historical batch numbers are not stage numbers.

| Area | Verified target interface | Scope |
|---|---|---|
| Language | Translation.realizes_formula / realizes_sentence | Eight source constructors, last/head binder correspondence, every corresponding structure |
| Original proof kernels | TheoryTransport, ReverseCompile, finite support | Source 19 rules and native six constructors / 27 logical modes; externally finite proof certificates |
| Full theories | ZFReplay, ReverseZFReplay.derives_iff / target_derives_iff | Seven fixed axioms plus all Separation/Replacement/Collection instances; both ZF and target presentations |
| Choice presentations | ChoiceNativeBridge and graph/selector adapters | Actual source graph choice and native selector choice equivalence |
| Domain interpretation | Relativization, InterpretedZF.project_axiom / collection | Full native ZF proof/schema transport in the source-ZF relativized background, with domain nonemptiness retained |
| Existing mathematics | ModelTransfer, KuratowskiZF, InternalWellOrderChoice, GodelDefOutput/Recursion, ConstructibleHistory/Parameters | Precisely stated internal model and original-kernel certificates; no completed full L interpretation claimed |
| Target axiom injection | target_derives_PP / ACwo / notAC | Only axioms of targetTheory; not a proof of its consistency |
| Original name induction | ForcingNameInduction.kernel_certificate / source_certificate | Exact source Child relation; arbitrary-parameter formula instances in original nativeZF, without external WellFounded; later name/forcing results are recorded below |
| Original IsName | ForcingNames.unfolding_kernel_certificate / edges_kernel_certificate / empty_kernel_certificate / uniqueness_kernel_certificate | Internal set-coded conditions, exact original recursive equation, empty name, arbitrary-formula solution uniqueness; atomic recursion and laws are covered by the rows below; evaluate and mapConditions scopes are recorded below |
| Original evaluate | ForcingEvaluation.existence_kernel_certificate / uniqueness_kernel_certificate / unfolding_kernel_certificate / empty_kernel_certificate | Every internal set G and raw name, exact active-child membership equation, no external well-foundedness; external generic-filter identification is outside the selected direct proof-reduction route |
| Original mapConditions | ForcingMapConditions existence / uniqueness / unfolding / edge / empty kernel certificates | Every parameterized definable total condition map; all raw internal names, explicit object function antecedent. Raw recursion locally accepted; subsequent law coverage is recorded below. |
| Original map laws | ForcingMapLaws identity / composition / preservation / congruence kernel certificates | Original IsName antecedent for identity; composition on all raw names; P-to-Q condition premise; extensional map replacement. Full local native-kernel acceptance passed. |
| Formula-class evaluation and original covariance | ForcingClassEvaluation existence / uniqueness / unfolding / membership certificates; ForcingEvaluationCovariance.covariance_kernel_certificate | Every parameter formula and definable total map; exact inverse-image formula, no inverse-image-set hypothesis, all raw names. Old set-G evaluator is an object-equivalent instance. Full local native-kernel acceptance passed. External generic-filter identification is outside the selected direct proof-reduction route. |
| Actual condition-code and name action | ForcingConditionGraphs identity / inverse / composition certificates; ForcingConditionAction function / name / identity / composition / inverse / covariance certificates | Exact source identity-outside condition formula, instantiated name map and formula-class covariance. Arbitrary internal permutation graphs; final PPAC group/homomorphism family not yet instantiated. Full local native-kernel acceptance passed. |
| Original pair and union names | ForcingPairName seven native certificate schemas; ForcingUnionName five native certificate schemas | Exact literal pair and all-common-strengthenings union; formula-class evaluation, pair mapping/fixed-condition action; union evaluation retains subset/upward closure/directedness. Full local native-kernel acceptance passed. Both are completed by the following row. |
| Original checkName and union action | ForcingCheckName four certificates; ForcingCheckNameLaws four certificates; ForcingUnionAction two certificates | All internal sets, exact source membership equation, IsName, formula-class evaluation, definable condition mapping, fixed-condition action; actual order-preserving permutation commutes with unionName. No external WellFounded; the newly constructed HS/check closure is recorded below; atomic recursion and laws are covered below. Full acceptance passed. |
| Main OpenAI forcing chain | No completed native counterpart yet | Original forcing, algebra, construction and models remain to be migrated along their actual dependency chain |
| Internal Proof/Con and final theorem | Not complete | Original background, all internal codes, full axiom test and final Derives required |

The newer native YesMetaZFC 7979336 has l_model_zf_l/l_model_zfc_l/l_model_gch_l for arbitrary internal ZF models with full schemas; directed ZFC build and three-endpoint trust=0 audit passed. This corrects the previous inventory restricted to ZFSet LCarrier. Version/language/native-kernel integration is pending; see REUSE_CONTRACTS. Do not describe the existing ZF schema equivalence or reverse proof compilation as missing.

Current local proof acceptance is recorded in STATUS and verification/summary.json; historical counts are not completion estimates. Original OpenAI Lean 4.34.1 Comparator has not run; the exact toolchain is now installed in an isolated workspace and the original Main build passed all 8998 jobs and five endpoints passed trust=0 / standard-three dependency audit. Full Comparator remains unavailable without Linux/landrun.

The four InterpretedZF declarations inherit exactly the existing seven ZF sentence certificates plus propext, Quot.sound and Classical.choice. Existing native-recursion adapters separately inherit 15 pinned Bool certificates, explicitly reevaluated by Check.lean; this is native evaluation, not kernel reduction. The original choice-sentence certificate is confined to its separately audited bridge. No new object axiom or proof kernel was introduced.


| Source dependency | Current native migration | Remaining boundary |
|---|---|---|
| AtomicForcing child induction and relations | ForcingPairInduction, ForcingAtomicStep/Graphs/Recursion/Relations: internal recursive relations and exact equations accepted | Actual condition presentation remains |
| AtomicForcing atomic_laws and dense closure | ForcingAtomicBasic/TripleInduction/Laws accepted; constructed relations, no assumed atomic-law fields | Concrete HS system closure and target axioms remain |
| AtomicForcing atomic_symmetry | ForcingAtomicSymmetry accepted, including literal actCode permutation instance | Concrete PPAC group remains |
| ForcingQuotient BasicFormula/toBasic/Force, ForcingTruth regularity | ForcingFormula accepted: every fixed formula, all-rank parameter H, dense local witnesses | HS predicate and its domain transport are constructed below; concrete system remains |
| ForcingTruth forcing_sound/rename/raise/instantiate | ForcingSound accepted: all 19 rules, native certificate for each fixed source proof and finite premise list | Arbitrary internal/nonstandard proof-code reduction remains |
| ForcingTruth force_symmetry (14–44) | ForcingFormulaSymmetry: six-case original induction, general map and existing actCode certificates; directed build and trust=0 preaudit passed, full acceptance passed | Generic H closure/surjectivity remain explicit there; ForcingHSAction discharges them for HS under the algebraic contexts. Consumer: SymmetricNames.forces_symmetry and Separation-name action |

Decision-set density, atomic_truth and exists_truth_generic are outside the selected direct proof-reduction route. Historical batch-specific missing-status paragraphs have been removed because later accepted batches discharged them. Source definitions, quantifiers and the final nativeZF Con contract remain unchanged.


| Original HS dependency | Current object result | Remaining boundary |
|---|---|---|
| Name.Symmetric | ForcingStabilizer: actual fixed-name action and unique stabilizer subset by Separation | Normal filter constructed below; concrete condition/action-family remains |
| Name.HS / hs_iff / child | ForcingHS: internal closed-set witnesses, exact guarded source equation, uniqueness among definable solutions by original Child induction | HS.smul is proved below; pair/union closures remain |
| Name.empty_HS / check_HS | Empty HS and check HS for every internal set; five native certificates across all three modules | Retains original top-filter, t in P and fixed-action premises; concrete system must supply them |

This batch has 59 audited declarations; directed build and trust=0 preaudit passed, full acceptance passed. The all-rank HS predicate is no longer an arbitrary assumed H or a nonexistent definition. Its general action closure is now proved below; the concrete PPAC system remains uninstantiated.

| Source dependency | Current object result | Remaining boundary |
|---|---|---|
| Name.HS.smul stabilizer step | ForcingNameConjugacy and ForcingStabilizerTransport: actual fixed-name equivalence and stabilizer image | Explicit permutation/action-family covariance and normal-filter conjugation; concrete PPAC instance remains |
| Name.HS.smul hereditary step | ForcingHSAction.hs_action and kernel_certificate: original Child induction, all internal names | No assumed HS closure; algebraic Context remains |
| SymmetricNames.forces_symmetry | ForcingHSAction.domain_transport/formula_kernel_certificate: actual HS domain, both directions proved | Concrete forward/inverse Context and order preservation must be supplied |

Earlier accepted batch: 47 new declarations, one generalized existing mapping congruence, four native certificates; full verifier passed (29595 declarations, 9 commands including 5 trust=0, zero warnings). Existing native sentence-certificate dependencies are retained; no trust expansion. These counts measure audit coverage, not completion of stages 7–10.

| Concrete source dependency | Current object result | Remaining boundary |
|---|---|---|
| ProductNames.system: Equiv.Perm I | ForcingLabelPermutations constructs the exact internal permutation set via donor function space and Separation | Conjugation graph and subgroup-image closure are proved below; concrete condition action remains |
| SupportFilter.Fix / mem_Fix | Unique internal fixing subset; actual identity/inverse/composition witnesses stay in it; three native certificates | No small-support cardinal or normal-filter claim |
| SupportFilter.conjugate_fix | ForcingLabelConjugacy: exact internal label image and pointwise fixing equivalence in both directions; two native certificates | The graph and exact stabilizer set image are now proved below; finite-union/intersection and complete normality are proved below |

This label batch has 41 declarations; directed build and trust=0 preaudit passed. Full verification passed. Its five certificates retain only the existing nativeZF trust baseline.

| Source dependency | Current object result | Remaining boundary |
|---|---|---|
| SupportFilter.conjugate_fix map | ForcingConjugationGraph.exists_graph: unique internal permutation graph, with actual inverse/surjectivity proof | Concrete condition-action covariance remains |
| SupportFilter.conjugate_fix equality | fixing_image and image_kernel_certificate: exact fixing-subgroup set image | No small-support cardinal conclusion |
| SupportFilter.conjugate_mem subgroup map | identity/inverse/composition covariance; subgroup_image and subgroup_kernel_certificate | Support-family conjugation membership and finite-union/intersection are supplied below |

This conjugation batch has 30 declarations and three native certificates. Directed build and trust=0 preaudit passed; full verification passed. No new trust dependency or assumed graph/stabilizer-image conclusion.

| Source dependency | New native migration | Remaining boundary |
|---|---|---|
| SupportFilter.subgroupFilter / top_mem / upward_closed / conjugate_mem | ForcingSupportSize and ForcingSupportFilter: actual source injection and native cardinal bound; unique support-defined subgroup family; top, upward among subgroups, conjugation; six native certificates | inf_mem and all four normal-filter clauses are completed by the following row; ProductNames.actionHom and properness remain |

| Source dependency | Current object result | Remaining boundary |
|---|---|---|
| SupportFilter.inf_mem / isNormalFilter | Literal newer native omega/cardinal-bound proofs + ForcingSupportIntersection + ForcingNormalFilter.construction_kernel_certificate: constructs G,F with exact support definition and all four clauses under internal IsOmega/IsInfiniteCardinal | Condition action, properness/bot_not_mem and target axioms remain. No assumed omega-cardinality or normality |

The current cardinal consumer additionally uses nine existing pinned native Bool certificates (ordinal maximum and omega multiplication), reevaluated in Check.lean and locked per declaration. These supplement the prior 15 recursion checks and seven sentence certificates; native evaluation is not kernel reduction. No object AC or new proof kernel was added.

ForcingDiagramCarrier/Order continue the pinned Diagram.permuteOrderIso dependency. Six native certificates construct the full internal diagram carrier and action, prove set-level identity/multiplication, construct sub from the original fixed-left function/cancellation conditions and construct an automorphism of the source translation relation. Full monoid/conicality instantiation, WithTop and ProductNames.actionHom remain incomplete; the current stage remains 7.

Seven Cohen native certificates now cover actual coordinate products/permutations, bounded partial-function carrier, preservation of functionality/internal size bound, reverse-inclusion equivalence, entire-carrier order permutation and their actual assembly. The final ProductNames action-family and omega/2 specialization are not claimed; no native base construction is newly missing.

ForcingCohenActionLaws and ForcingProductAction add six native certificates for Cohen identity/composition, exact product carrier/action construction and identity/composition, and assembly of the source Cohen/diagram product from a label permutation. Product order is the conjunction of Cohen reverse inclusion and the literal Diagram translation relation; no monoid/conical partial-order premises are silently discharged. WithTop and uniform ProductNames action-family remain. Batch acceptance is recorded in STATUS.
