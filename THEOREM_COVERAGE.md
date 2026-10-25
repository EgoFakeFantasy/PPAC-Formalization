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
| Actual condition-code and name action | ForcingConditionGraphs identity / inverse / composition certificates; ForcingConditionAction function / name / identity / composition / inverse / covariance certificates | Exact source identity-outside condition formula, instantiated name map and formula-class covariance. Arbitrary internal permutation graphs; fixed-carrier family and support-filter Context now constructed below; full concrete system remains. Full local native-kernel acceptance passed. |
| Original pair and union names | ForcingPairName seven native certificate schemas; ForcingUnionName five native certificate schemas | Exact literal pair and all-common-strengthenings union; formula-class evaluation, pair mapping/fixed-condition action; union evaluation retains subset/upward closure/directedness. Full local native-kernel acceptance passed. Both are completed by the following row. |
| Original checkName and union action | ForcingCheckName four certificates; ForcingCheckNameLaws four certificates; ForcingUnionAction two certificates | All internal sets, exact source membership equation, IsName, formula-class evaluation, definable condition mapping, fixed-condition action; actual order-preserving permutation commutes with unionName. No external WellFounded; the newly constructed HS/check closure is recorded below; atomic recursion and laws are covered below. Full acceptance passed. |
| Main OpenAI forcing chain | No completed native counterpart yet | Original forcing, algebra, construction and models remain to be migrated along their actual dependency chain |
| Internal Proof/Con and final theorem | Not complete | Original background, all internal codes, full axiom test and final Derives required |

The newer native YesMetaZFC 7979336 has l_model_zf_l/l_model_zfc_l/l_model_gch_l for arbitrary internal ZF models with full schemas; directed ZFC build and three-endpoint trust=0 audit passed. This corrects the previous inventory restricted to ZFSet LCarrier. Version/language/native-kernel integration is pending; see REUSE_CONTRACTS. Do not describe the existing ZF schema equivalence or reverse proof compilation as missing.

Current local proof acceptance is recorded in STATUS and verification/summary.json; historical counts are not completion estimates. Original OpenAI Lean 4.34.1 Comparator has not run; the exact toolchain is now installed in an isolated workspace and the original Main build passed all 8998 jobs and five endpoints passed trust=0 / standard-three dependency audit. Full Comparator remains unavailable without Linux/landrun.

The four InterpretedZF declarations inherit exactly the existing seven ZF sentence certificates plus propext, Quot.sound and Classical.choice. Existing native-recursion adapters separately inherit 15 pinned Bool certificates, explicitly reevaluated by Check.lean; this is native evaluation, not kernel reduction. The original choice-sentence certificate is confined to its separately audited bridge. No new object axiom or proof kernel was introduced.


| Pinned source dependency | Current object interface | Remaining boundary |
|---|---|---|
| AtomicForcing relations/atomic_laws/atomic_symmetry | ForcingPairInduction, AtomicStep/Graphs/Recursion/Relations/Basic/Laws/Symmetry: internal recursion, exact equations, laws and action symmetry | Concrete system and forced axioms |
| ForcingQuotient Force; ForcingTruth regularity/forcing_sound | ForcingFormula/Sound: every fixed formula and all 19-rule fixed proofs | Every internal proof code belongs to stage 10 |
| Name.Symmetric/HS/hs_iff/child | Literal stabilizers, internal closed witnesses, exact recursive equation and definable uniqueness | HS pair/union now supplied by ProductHSPair/ProductHSUnion; full forced axioms remain |
| Name.empty_HS/check_HS | ForcingHSCheck: all internal sets; top-filter, valid top and fixed-action premises retained | Supply these from the complete system |
| Name.HS.smul; SymmetricNames.forces_symmetry | ForcingNameConjugacy/StabilizerTransport/HSAction: actual stabilizer conjugacy, Child induction, two-way HS domain transport | ProductSymmetry now supplies both contexts and order; the final Main monoid/poset system remains |
| Equiv.Perm I; SupportFilter.Fix/conjugate_fix | LabelPermutations/LabelConjugacy/ConjugationGraph: actual permutation carrier, fixing subsets, conjugation graph, exact subgroup images | These constructions are complete |
| SupportFilter.subgroupFilter/isNormalFilter | SupportSize/Filter/Intersection/NormalFilter: actual support family and all four normality clauses, using donor omega/cardinal proofs | Source infinite bound and properness at their actual consumers |
| Diagram.permuteOrderIso | DiagramAction/Carrier/Order: all injection diagrams, sub and literal translation-relation invariance | Actual monoid/conicality and resulting partial-order laws |
| Cohen coordinatePerm/permuteOrderIso | CohenCoordinates/Conditions/OrderAction/ActionLaws: coordinate products, bounded partial functions, reverse-inclusion automorphisms, identity/composition | Source omega/two specialization supplied by ProductParameters |
| ProductForcing.permuteOrderIso; ProductNames.WithTop | ProductAction/WithTopCarrier/WithTopAction: actual product, empty/singleton presentation, fixed top, exact coe order and action laws | Full concrete partial-order instance |
| ProductNames.actionHom → system | ProductFamily: one formula on fixed shared carriers, total unique action, identity/composition/order/top, native Family construction | Source parameters now supplied; monoid/conical order remains |
| ProductNames.system → Name.HS.smul | ProductCovariance: inverse/conjugacy, actual support-filter Context, existential SystemData and HS closure native certificates | Formula symmetry supplied below; full forcing-system axioms remain |

| SymmetricNames.forces_symmetry → Separation-name | ProductSymmetry.kernel_certificate: actual action family, reverse conjugation, both HS-domain directions and order invariance | Each complete fixed formula; arbitrary internal codes and final Main poset remain |
| CohenForcing.Condition countable Boolean graphs | ProductParameters.construction_kernel_certificate: native omega/two existence followed by shared carriers and uniform Family | Monoid/conical order and complete source-system assembly remain |

| Source diagram/product/WithTop partial order | ForcingProductPoset.kernel_certificate, using ForcingDiagramPoset source laws | Object implication from the source left-cancel monoid/conical contract and actual Presentation to the existing forcing PreorderOn, antisymmetry and internal top. Concrete stage-8 monoid is not yet constructed. |

| Source actual-name stabilizer and HS pair/union | ProductStabilizer, ProductHSPair, ProductHSUnion.kernel_certificate | Actual action, native subgroup closure, literal source names, source normality/presentation antecedents. All internal names; no HS closure assumption. Does not yet prove forces_pairing/forces_union. |

These rows are integrated into the formal audit; current full acceptance is reported only in STATUS. Existing seven sentence certificates, 15 recursion Bool certificates and nine cardinal Bool certificates remain explicitly audited/reevaluated. No new object axiom, HS-closure assumption or proof kernel is added.

Decision density, atomic_truth, exists_truth_generic and byte compatibility are outside the selected direct proof-reduction route. Historical reports remain recoverable in Git; their obsolete missing-status narratives are not current obligations.
