# PPAC migration instructions
Use the original YesMetaZFC pure-set signature and FirstOrder.Derives; no new proof kernel.
Read docs/FEASIBILITY.zh-CN.md and docs/AGENT_WORKFLOW.zh-CN.md before continuing.
User correction: read docs/REUSE_CONTRACTS.zh-CN.md first. Reuse the pinned YesMetaZFC interfaces and completed companion-project closing methods before adding any foundation, syntax checker, satisfaction recursion, support-elimination or completeness implementation. An object-level requirement does not justify duplicating existing definitions and proofs.
Active scope is governed by docs/SCOPE_REASSESSMENT.zh-CN.md. Historical next-step tables do not justify restarting the frozen NatPacket/reader compatibility route. First audit the missing ZF-internal relative-consistency mathematics; do not add lower-level infrastructure without a concrete dependency on a necessary object theorem.
Final goal is an object derivation in native ZF: Derives B [] (Con_ZF → Con_target). Read docs/OBJECT_TARGET.zh-CN.md. External consistency transfer is intermediate only; neither it nor ExternalConsistencyGoal is the final deliverable.
Step 1 truth preservation is an intermediate language result and must not be presented as the main theorem.
Keep SourceStatements graph definitions, arbitrary schema parameters, binder order and all-set quantifiers exact.
Source Replacement/native Collection and the two AC presentations require actual derivation equivalences.
Do not import host auxiliary PP as the object sentence. Do not add Choice or inaccessible premises to the ordinary route.
Only one Lean/Lake build at a time; LEAN_NUM_THREADS=1. Run python scripts/verify.py after changes.
Do not restore retired reflection implementations. Do not publish local probes, archives or logs automatically.
