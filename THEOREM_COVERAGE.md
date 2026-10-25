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
| Main OpenAI forcing chain | No completed native counterpart yet | Original forcing, algebra, construction and models remain to be migrated along their actual dependency chain |
| Internal Proof/Con and final theorem | Not complete | Original background, all internal codes, full axiom test and final Derives required |

The completed donor LCarrier ZF/ZFC theorems include full schemas; see REUSE_CONTRACTS for their exact types and the outstanding integration distinction. Do not describe the existing ZF schema equivalence or reverse proof compilation as missing.

Local proof acceptance: 2836 build jobs, 28800 audited declarations, 9 commands succeeded, 5 trust=0 checks, zero warnings. These counts are audit coverage, not a progress percentage. Original OpenAI Lean 4.34.1 Comparator has not run; its toolchain acquisition failed on DNS resolution this turn.

The four InterpretedZF declarations inherit exactly the existing seven ZF sentence certificates plus propext, Quot.sound and Classical.choice. Existing native-recursion adapters separately inherit 15 pinned Bool certificates, explicitly reevaluated by Check.lean; this is native evaluation, not kernel reduction. The original choice-sentence certificate is confined to its separately audited bridge. No new object axiom or proof kernel was introduced.
