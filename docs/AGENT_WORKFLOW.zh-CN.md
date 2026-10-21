# 对象层迁移工程流程
最终交付：Derives B [] (Formula.imp Con_ZF Con_target)。
B固定原YesMetaZFC的ZF纯语言像，不额外加入AC、不可达或Con(B)。
内部Con的展开、编码与全内部ω范围见[对象目标规格](OBJECT_TARGET.zh-CN.md)。
这里只按明确工作单元推进，不要求并行启动agent；Lean/Lake构建始终串行。

| 步骤 | 输入与负责职责 | 必须交付的模块/结果 | 验收门 | 状态 |
|---|---|---|---|---|
| 0 | 来源审查：固定OpenAI244/YesMetaZFC/PPAC | SOURCE_LOCK、REPOSITORY_MAP、CLEANUP | 来源/前提分开；备份可恢复 | 完成 |
| 1 | 原语言与原核接口 | SourceSyntax、SourceStatements、Translation、Contract | 全8构造器语义保真；正确对象句子 | 完成，中间层 |
| 2 | 19条源规则与原Hilbert核 | SyntaxTransport、SourceDerivation、DerivationTransport、TheoryTransport、FiniteSupport | 非单射rename、嵌套instantiate、fresh量词、等词、任意n闭句、有限公理支撑；原核回放与trust=0 | 完成，正向传输 |
| 3a | 原生11构造器／源8构造器、原核theory_cut | Normalization、ReverseSyntax、Presentation、SourceTheory | 全公式严格往返/规范化；量词下任意替换；原核对象等价；任意理论与开放推导回放；源九类ZF溯源 | 完成，中间层 |
| 3b | 源Replacement版ZF与原Collection版ZF | ZFEquivalence | 七固定公理及任意参数的两种全模式，两个方向的实际Derives | 已完成外延/空集/配对/并集/幂集；其余待做 |
| 3c | 原六规则Hilbert证书与源19规则 | ReverseDerivation | 原核→源演绎；明确额外非空变量环境及闭句回落，不能把原核内呈现回放当作本项 | 待做 |
| 3d | 源图选择与原生不交族选择集 | ChoiceEquivalence | 原ZF内双向对象推导，内部集合图、全量词、无外加AC | 待做 |
| 4 | 固定原核六规则及ZF/U公理识别 | Internal/ProofZF、ProofTarget、ConFormula | 完整纯ℒ公式AST；任意内部ω中的Proof/Con正确性；不得套用ZFC专用检查器 | 待做 |
| 5 | 句法转换器及步骤2–3 | Internal/CompilerRepresentation | 代码函数的内部表示及原核推导；覆盖非标准码，不能只列外部标准实例 | 待做 |
| 6 | 原OpenAI 4.34.1环境 | 原源码定向构建、两个Comparator记录 | 分开普通Con与带不可达传递模型；真实命令与允许公理 | 待做 |
| 7 | 原生集合构造与递归 | Internal/Names、Pairs、Tuples、Recursion | 内部图与唯一性；不假定外部良基或标准ω | 待做 |
| 8 | 论文的内部解释路线 | Interpretation/Constructible、Background | 在对象ZF中逐公理证明L相对化；背景/语言/universe对应明确 | 待做 |
| 9 | 实际对称强迫系统 | Forcing/Atomic、Truth、Symmetry、ZF | 实际poset/正规滤子/HS、混合、全部ZF模式的对象证明 | 待做 |
| 10 | 单子与图式构造 | Geometry/Monoid、Placement、ConservativeHull | 核心局部存在性实际证明，不以结构字段假定结论 | 待做 |
| 11 | 模型应用 | Models/SVC、ACwo、Quotient、NotAC | 任意秩集合、同一HS模型内商双射及非选择见证 | 待做 |
| 12 | 全局装配与内部化结果 | Consistency/ObjectMain | 实际 Derives B [] (Con_ZF → Con_target)，原量词与前提不变 | 待做 |
| 13 | 最终验收 | 量词/编码/可信基/完整依赖审计 | 全build、无缺口、完整对象主句；源与目标一致性边界分开 | 待做 |

每单元交接必须记录：固定提交、允许文件、目标完整Lean类型、实际命令/退出码、
剩余义务、禁止强假设和下一最小工作。外部Consistent传输不替代对象Con推导。

第二步只实现正向传输。反向对应、ZF/U内部检查公式和完整内部化没有被偷偷列为完成。
当前原生ZF合同仍继承底座7个native_decide句子闭合证书，见TRUST_BASELINE.json；
新增第二步传输关键声明的公理审计只允许标准propext/Classical.choice/Quot.sound。

第三步边界：Presentation.theory T 是任意原理论T经回译再正向翻译的规范化呈现，
并不等于OpenAI源Replacement版ZF。Presentation.derives_iff 的两端都使用原FirstOrder.Derives；
它不是返回Source.Derives的反向编译器。源Source.Consistent量化全部变量环境，
后续反向接口必须核对源末变量规则与原free_strengthening的非空环境要求，不能默认n=0逐条对齐。
第三步验收与下一最小工作见STEP3_ACCEPTANCE.zh-CN.md。
