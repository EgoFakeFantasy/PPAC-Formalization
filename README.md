# PPAC → YesMetaZFC
[简体中文](README.zh-CN.md)

An in-progress migration of OpenAI family 244 to the original YesMetaZFC pure-set language and Hilbert derivation kernel.
Steps 1 and 2 are implemented: language preservation, strict AST renaming/substitution, all 19 source rules into original Derives, arbitrary-variable closed-sentence transfer, and finite axiom support. No relative-consistency theorem, symmetric model, or PP/AC separation is delivered by this branch.

The final endpoint is an object derivation in native ZF of the internal sentence Con(ZF) → Con(ZF+PP+ACwo+¬AC). The internal proof-checker ASTs and internalization remain pending; external consistency transfer is intermediate only. See docs/OBJECT_TARGET.zh-CN.md.
Step 3a adds full native-to-source syntax, original-kernel normalization and arbitrary-theory presentation replay. All seven fixed ZF axioms now have native-kernel derivations in both presentations. Every source Separation instance (arbitrary parameter count and matrix) is proved in native ZF; the corresponding native instance also replays from the source ZF image. Reverse coverage now includes every native Project matrix. Arbitrary Collection presentations are also proved/replayed in native ZF. Collection plus Separation now derives every original source Replacement instance. Full source ZF and target-theory derivations replay into the actual native theories. The native-to-source derivation compiler now covers all 6 original kernel constructors and 27 logical axiom modes, arbitrary finite local hypotheses, and closed sentences at source variable-context size 1. It returns actual Source.Derives certificates. This is external certificate transport; the internal compiler and Con formula remain pending. Full bounded membership-minimal and induction schemas are now proved in both source and native ZF, each using only Foundation and one Separation instance. Pure object Kuratowski pair existence/uniqueness and component characterization now strictly match the original source PP/AC encoding and use only Pairing and Extensionality. The original full edge/functionOn formulas are preserved; singleton function graphs are constructed and evaluated, and arbitrary function graphs have edge-domain, total output existence and single-valuedness derivations. Arbitrary function graphs now have actual unique extensions at a fresh input outside the old domain, preserving full functionOn and an exact all-edge law. Arbitrary graph restrictions are constructed with full functionOn, exact edges, uniqueness, identity and nested-restriction composition. Compatible graph-family union, internal omega iteration, transitive closure, ranks and cumulative hierarchy, the converse mathematical Collection direction, and Choice correspondence remain pending. See [graph restriction acceptance](docs/STEP3_GRAPH_RESTRICTION_ACCEPTANCE.zh-CN.md), [graph insertion acceptance](docs/STEP3_GRAPH_INSERT_ACCEPTANCE.zh-CN.md), [object graphs acceptance](docs/STEP3_OBJECT_GRAPHS_ACCEPTANCE.zh-CN.md), [object pairs acceptance](docs/STEP3_OBJECT_PAIRS_ACCEPTANCE.zh-CN.md), [bounded Foundation acceptance](docs/STEP3_BOUNDED_FOUNDATION_ACCEPTANCE.zh-CN.md), [reverse derivation acceptance](docs/STEP3_REVERSE_DERIVATION_ACCEPTANCE.zh-CN.md) and [Replacement and forward-theory acceptance](docs/STEP3_REPLACEMENT_FORWARD_ACCEPTANCE.zh-CN.md).

Native ZF uses full Collection; the source uses full Replacement. Their proof-theoretic correspondence is pending.
The source uses graph Choice; YesMetaZFC's built-in axiom uses disjoint-family selection. Their correspondence is pending too.

Run: python scripts/verify.py
Lean 4.33.1; the only external dependency is YesMetaZFC pinned at 039c8e132cc19671d73a3933c66b4799d2599dd6.
The command builds all active modules, checks the native declarations with trust=0, and audits the listed declarations.
Logs are local under verification/ and are not publication material.

Main entry: import PPAC
Retained host-level auxiliary lemmas: import PPAC.Auxiliary

- [Feasibility and exact scope](docs/FEASIBILITY.zh-CN.md)
- [Repository reuse assessment](docs/REPOSITORY_MAP.zh-CN.md)
- [Agent workflow with acceptance gates](docs/AGENT_WORKFLOW.zh-CN.md)
- [Cleanup decisions](docs/CLEANUP.zh-CN.md)
- [Remaining gaps](GAPS.md)
- [Source lock](docs/SOURCE_LOCK.json)

Attribution: existing auxiliary implementations and their authorship remain in Git history.
OpenAI source syntax and formula definitions are adapted under Apache-2.0; see NOTICE.
This branch has not compiled or run Comparator on the original OpenAI development.
