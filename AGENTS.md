# PPAC migration instructions
Use the original YesMetaZFC pure-set signature and FirstOrder.Derives; no new proof kernel.
Read docs/FEASIBILITY.zh-CN.md and docs/AGENT_WORKFLOW.zh-CN.md before continuing.
Main goal is native syntactic consistency transfer. RelativeConsistencyGoal is pending, not a theorem.
Step 1 truth preservation is an intermediate language result and must not be presented as the main theorem.
Keep SourceStatements graph definitions, arbitrary schema parameters, binder order and all-set quantifiers exact.
Source Replacement/native Collection and the two AC presentations require actual derivation equivalences.
Do not import host auxiliary PP as the object sentence. Do not add Choice or inaccessible premises to the ordinary route.
Only one Lean/Lake build at a time; LEAN_NUM_THREADS=1. Run python scripts/verify.py after changes.
Do not restore retired reflection implementations. Do not publish local probes, archives or logs automatically.
