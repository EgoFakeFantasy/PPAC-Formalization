# PPAC 向 YesMetaZFC 迁移审查
核查日期：2026-10-21。结论：可以分阶段实施，但不是改 import 的直接移植；完整迁移尚未完成。
当前：完整ZF呈现互导、外部推导双向回放及原两种AC的对象等价均已验收；内部Proof/Con和最终主句仍待实现。
最新AC验收见STEP3_CHOICE_EQUIVALENCE_ACCEPTANCE.zh-CN.md；下列分批更新保留历史范围。

## 来源、结论和可信边界
- [OpenAI family 244](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/docs/244.md)。
- 论文主结论为 Con(ZF) → Con(ZF+PP+ACwo+¬AC)，不是 PP→AC。
- 相对一致性源码：lean/OAI/SetTheory/PartitionConsistency/Main.lean，75 个模块，32558 行。
- 独立传递模型源码：lean/OAI/SetTheory/PartitionPrinciple/，943 个模块。其选定终点假定外部可数传递地面及内部强不可达；不能混入普通相对一致性的前提。
- ComparatorChallenges 中的 sorry 是题面占位，不是实际证明。实际解答位于 OAI 子树。此轮只做源码审查，未编译 OpenAI 全套，未运行 Comparator，不声称其内核验收通过。
- 实际 main_consistency 忽略输入一致性，调用 Lean 元理论中具体强迫解释的 consistent_target；GroundModels 明说未证明 ZF 内的可构造解释。其外部定理类型与论文相符，但不是论文所述逐行相对化证书的实现。
- 来源要求 Lean 4.34.1+mathlib；目标固定 YesMetaZFC 039c8e132cc19671d73a3933c66b4799d2599dd6，Lean 4.33.1+Std。不能跨版本复制 olean。
- 固定提交、源文件 SHA256 见 SOURCE_LOCK.json。旧的“仍开放”研究笔记只作历史材料。

## 本工程的对象合同
对象语言是 YesMetaZFC 的单排序纯成员语言 ℒ，只有等词和 ∈。
使用其原 FirstOrder.Derives / HilbertDerivation，禁止增加新的公理核。
背景是原 SetTheory.ZF 经 Project.fo_theory 的纯语言像；该库使用全 Collection 模式，源用全 Replacement 模式。
PP、AC、ACwo 使用源的集合图形式，函数是结构内部的 Kuratowski 对集合，量词遍历全部内部集合。
源 AC 是一般非空集合族的选择函数式；YesMetaZFC 自带 AC 是不交族的选择集式，两者在原ZF核内的双向蕴含和双条件现已证明。
Source Formula n 的量词绑定最后变量；目标内在语法绑定列表头。须显式变换并证明保真。
原生目标理论是 ZF+PP+ACwo+¬AC。语义保真不自动给出推导传输。
第一步只交付原生句子与理论合同、全语法翻译及真值保持、最小对象推导接入检查。
最终终点已按用户要求固定为对象ZF中的内部Con蕴含的Derives证书；背景与编码见OBJECT_TARGET.zh-CN.md。外部一致性传输仅是中间层。
不以 ZFC 的普通推导证明 ¬AC；模型解释的结论和解释所处的元理论必须区分。

## 主要缺口
1. 源开放自然演绎规则（无限假设集、末自由变量）到目标有限上下文 Hilbert 核的双向传输；须用有限支撑。
2. 两种AC呈现的对象互导、源Replacement与目标Collection完整逐模式互导及ZF/目标理论回放均已完成；内部证明码表示仍待实现。
3. 元层纯集合、布尔值、商、全部 HS 名字的 universe 对应；不能强行固定名字秩界。
4. 可构造解释如走论文路径，应逐公理证明 ZF ⊢ α^L；语义 L 模型或文档提及 GCH 不够。
5. 将强迫系统、逻辑规则、ZF 全模式、SVC、ACwo、非选择见证及全秩 PP 装配为原核可检查接口。
6. 不可把反向单射升级成原满射的截面，不可把内部良基等同于外部 WellFounded。
7. 最终分开验收普通 Con 路线、带强不可达的传递模型路线和论文更强的序列保持结论。


公理审计边界：固定 YesMetaZFC 的 sentence! 宏用 native_decide 生成7个基础句子的 FreeClosed 证书，原生ZF合同继承其7个 native_decide.ax_1 依赖。见 docs/TRUST_BASELINE.json。当前检查精确守住此基线，不标成“仅三项标准公理”；未修改底座，也未添加新的自定义公理。后续若要求纯内核证书，需另行把这些证书改为 kernel-checked decide 并核对原理论不变。

语义桥的 Classical.choice 已定位到 Lean 核心定理 Fin.lastCases_castSucc，只用于 Prop 中的绑定等式证明；未向对象ZF加入AC，也未抽取内部集合选择函数。旧宿主辅助维持原先无 Classical.choice 的依赖范围。

第二步进度：源19规则正向传输、AST重命名/替换、任意变量环境的闭句传输和有限原核公理支撑已完成；源/目标ZF呈现等价、反向传输与对象内部化尚未完成。

第三步阶段进度：全原生语法回译、任意公式的原核规范化等价、任意理论与开放推导的呈现回放已完成。
这不等于原核到源Source.Derives的反向编译。源九类ZF公理谓词已固定并逐字溯源。
外延、空集、配对、并集、幂集已有两个方向的实际原核推导；
无穷、基础、任意参数全模式与两种AC仍待完成。没有提高最终内部Con主句的完成状态。

持续目标更新：七条固定公理均已双向对象推导。全部源分离模式已在原ZF中推导，
同矩阵对应的原生实例可在源ZF句子像回放。参数数目与矩阵复杂度没有有限限制。
任意原生Project矩阵的反向覆盖、Collection/Replacement完整等价、两种AC及内部Con主句尚待完成。

全分离更新：任意原生Project矩阵的反向覆盖已证明，分离模式已在两个呈现中全参数双向对象推导。
原Collection的任意源矩阵呈现与任意原生二元矩阵回译也已证明；
这不等于Replacement/Collection实质推导已完成，内部Con主句状态仍未完成。

Replacement实质更新：原Collection加分离已对任意参数/矩阵证明原始源Replacement实例。
两实例原核证书不依赖底座7个固定句子证书，原ZF回放仍按既有基线审计。
源ZF九类公理及源目标理论的完整正向推导回放现已完成；
反向Collection方向、内部码编译正确性和内部Con对象主句仍未完成。

完整ZF呈现互导更新：CollectionFromReplacement已为任意关系矩阵和任意有限参数提供源Replacement版ZF中的完整原Collection推导，
并经原核传输覆盖任意原生Project矩阵。ReverseZFReplay逐原ZF九类公理回放，给ZF和目标理论任意开放推导的双向原核传输，
及闭句到原19条源规则的实际反向编译。见STEP3_FULL_ZF_EQUIVALENCE_ACCEPTANCE.zh-CN.md。
这里仍是对象公理逐模式证明和外部证书回放；任意内部码的Proof检查器、内部编译正确性与最终Con蕴含主句未完成。

AC正向及可信基更新：原图AC到原不交族选择集AC已完成实际对象推导；反向尚未实现。
源有限理论核心仅使用一个图值域Replacement实例，原核核心依赖仍为标准三项。
ChoiceNativeBridge引用未修改原Axioms.choice，因此额外激活该库声明已有的FreeClosed语法证书
YesMetaZFC.SetTheory.Axioms.choice._native.native_decide.ax_1；仅桥接模块和原choice声明允许这项依赖，
单独来源/原文件SHA锁定见CHOICE_TRUST_BASELINE.json，不混入原ZF的七项基线，不声称引用原choice后可信基没有变化。
未新增自定义axiom声明或对象AC背景公理；完整AC互导、内部Proof/Con和最终主句仍待完成。

AC反向及完整等价更新：Extensionality、Pairing和三个明确原Replacement实例实际构造标签行、精确非空不交族与精确选择对图。
原选择集允许含杂项；完整entriesOn/totalOn、唯一输出及输出成员性均有对象推导。
ChoiceNativeBridge.native_equivalence给原nativeZF内AC与原Axioms.choice的实际双条件，源核心保持标准三项依赖；
原choice额外闭性证书限域没有扩大。完整AC互导已完成，内部Proof/Con及最终主句仍未完成。
