# PPAC → YesMetaZFC
[简体中文](README.zh-CN.md)

An in-progress migration of OpenAI family 244 to the original YesMetaZFC pure-set language and Hilbert derivation kernel.
Steps 1 and 2 are implemented: language preservation, strict AST renaming/substitution, all 19 source rules into original Derives, arbitrary-variable closed-sentence transfer, and finite axiom support. No relative-consistency theorem, symmetric model, or PP/AC separation is delivered by this branch.

The final endpoint is an object derivation in native ZF of the internal sentence Con(ZF) → Con(ZF+PP+ACwo+¬AC). The internal proof-checker ASTs and internalization remain pending; external consistency transfer is intermediate only. See docs/OBJECT_TARGET.zh-CN.md.
Step 3a adds full native-to-source syntax, original-kernel normalization and arbitrary-theory presentation replay. All seven fixed ZF axioms now have native-kernel derivations in both presentations. Every source Separation instance (arbitrary parameter count and matrix) is proved in native ZF; the corresponding native instance also replays from the source ZF image. Reverse coverage of arbitrary native Project matrices, Collection/Replacement, Choice correspondence, and the native-to-source derivation compiler remain pending. See [schema-stage acceptance](docs/STEP3_SCHEMAS_ACCEPTANCE.zh-CN.md).

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
