# Steps 1–2 coverage
- SourceSyntax: all eight source Formula constructors, last-variable binding, renaming/instantiation/closure, relational realization.
- SourceStatements: source PP, graph AC, ACwo, Kuratowski graph definitions, arbitrary Separation/Replacement schema sentence constructors.
- Translation.lift_assignment: source last variable becomes target head; prior assignments are preserved.
- Translation.realizes_formula: full structural semantic preservation, for every source formula and every native pure-set structure, with no ZF or external well-foundedness premise.
- Translation.realizes_sentence: specialization to closed sentences.
- Contract: original Collection-based ZF through Project.fo_theory, native target sentences and theory, and original FirstOrder.Derives.
- target_derives_PP / ACwo / notAC: only target axiom injection checks.
- consistent_ZF_of_target: easy downward consistency implication.
- no_AC_of_target_consistent: conditional contradiction check; no consistency premise is supplied by this project.

The source Derives forward transport now exists. Source/native ZF equivalence, reverse transport, forcing implementation and the internal Con main proof do not exist yet.
Retained auxiliaries are documented in docs/CLEANUP.json; none counts as an internal ZF proof.
Audit.lean enumerates selected declarations; counts are not counts of independent results.


公理审计边界：固定 YesMetaZFC 的 sentence! 宏用 native_decide 生成7个基础句子的 FreeClosed 证书，原生ZF合同继承其7个 native_decide.ax_1 依赖。见 docs/TRUST_BASELINE.json。当前检查精确守住此基线，不标成“仅三项标准公理”；未修改底座，也未添加新的自定义公理。后续若要求纯内核证书，需另行把这些证书改为 kernel-checked decide 并核对原理论不变。

语义桥的 Classical.choice 已定位到 Lean 核心定理 Fin.lastCases_castSucc，只用于 Prop 中的绑定等式证明；未向对象ZF加入AC，也未抽取内部集合选择函数。旧宿主辅助维持原先无 Classical.choice 的依赖范围。


## Step 2
- SyntaxTransport: strict AST equality for source rename and instantiate, native renaming and arbitrary bound/free substitution, binder lifting, fresh abstraction, and exact compatibility with step-1 sentences.
- SourceDerivation: all 19 pinned input rules, with only Set notation unfolded to predicates. scripts/check_source_rules.py checks the exact excerpt.
- Compile.derives: a source derivation plus derivable hypotheses produces original FirstOrder.Derives over a finite local context. No model or completeness input.
- TheoryTransport.closed_at: a source closed-sentence proof in any finite variable environment produces the same sentence image with empty native free context.
- FiniteSupport.certificate / derives: every actual original Hilbert proof has a finite list of theory axioms supporting the same judgment.
- TheoryTransport.consistent_source_of_native: only the external consistency direction justified by forward transport.
- CheckStep2: actual original-kernel replay of quantifier identity, existential elimination, a closed existential proved at source n=1, equality substitution and classical inference; nested capture-sensitive AST checks.
- Internal Con specification is fixed; it is not yet a concrete ZF/U checker implementation or an object main theorem.
