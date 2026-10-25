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
| Original name induction | ForcingNameInduction.kernel_certificate / source_certificate | Exact source Child relation; arbitrary-parameter formula instances in original nativeZF, without external WellFounded; full names/forcing not yet ported |
| Original IsName | ForcingNames.unfolding_kernel_certificate / edges_kernel_certificate / empty_kernel_certificate / uniqueness_kernel_certificate | Internal set-coded conditions, exact original recursive equation, empty name, arbitrary-formula solution uniqueness; atomic forcing remains unported; evaluate and mapConditions scopes are recorded below |
| Original evaluate | ForcingEvaluation.existence_kernel_certificate / uniqueness_kernel_certificate / unfolding_kernel_certificate / empty_kernel_certificate | Every internal set G and raw name, exact active-child membership equation, no external well-foundedness; external generic-filter identification remains pending |
| Original mapConditions | ForcingMapConditions existence / uniqueness / unfolding / edge / empty kernel certificates | Every parameterized definable total condition map; all raw internal names, explicit object function antecedent. Raw recursion locally accepted; subsequent law coverage is recorded below. |
| Original map laws | ForcingMapLaws identity / composition / preservation / congruence kernel certificates | Original IsName antecedent for identity; composition on all raw names; P-to-Q condition premise; extensional map replacement. Full local native-kernel acceptance passed. |
| Formula-class evaluation and original covariance | ForcingClassEvaluation existence / uniqueness / unfolding / membership certificates; ForcingEvaluationCovariance.covariance_kernel_certificate | Every parameter formula and definable total map; exact inverse-image formula, no inverse-image-set hypothesis, all raw names. Old set-G evaluator is an object-equivalent instance. Full local native-kernel acceptance passed. External generic-filter identification remains pending. |
| Actual condition-code and name action | ForcingConditionGraphs identity / inverse / composition certificates; ForcingConditionAction function / name / identity / composition / inverse / covariance certificates | Exact source identity-outside condition formula, instantiated name map and formula-class covariance. Arbitrary internal permutation graphs; final PPAC group/homomorphism family not yet instantiated. Full local native-kernel acceptance passed. |
| Main OpenAI forcing chain | No completed native counterpart yet | Original forcing, algebra, construction and models remain to be migrated along their actual dependency chain |
| Internal Proof/Con and final theorem | Not complete | Original background, all internal codes, full axiom test and final Derives required |

The completed donor LCarrier ZF/ZFC theorems include full schemas; see REUSE_CONTRACTS for their exact types and the outstanding integration distinction. Do not describe the existing ZF schema equivalence or reverse proof compilation as missing.

Local proof acceptance: 2846 build jobs, 29114 audited declarations, 9 commands succeeded, 5 trust=0 checks, zero warnings. These counts are audit coverage, not a progress percentage. Original OpenAI Lean 4.34.1 Comparator has not run; the exact toolchain is now installed in an isolated workspace and an original Main build has started. Full Comparator remains unavailable without Linux/landrun.

The four InterpretedZF declarations inherit exactly the existing seven ZF sentence certificates plus propext, Quot.sound and Classical.choice. Existing native-recursion adapters separately inherit 15 pinned Bool certificates, explicitly reevaluated by Check.lean; this is native evaluation, not kernel reduction. The original choice-sentence certificate is confined to its separately audited bridge. No new object axiom or proof kernel was introduced.
