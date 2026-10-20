# PPAC 向 YesMetaZFC 迁移审查
核查日期：2026-10-21。结论：可以分阶段实施，但不是改 import 的直接移植；完整迁移尚未完成。

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
源 AC 是一般非空集合族的选择函数式；YesMetaZFC 自带 AC 是不交族的选择集式，两者的 ZF 内推导等价尚待证明。
Source Formula n 的量词绑定最后变量；目标内在语法绑定列表头。须显式变换并证明保真。
原生目标理论是 ZF+PP+ACwo+¬AC。语义保真不自动给出推导传输。
第一步只交付原生句子与理论合同、全语法翻译及真值保持、最小对象推导接入检查。
后续终点：原核的一致性传输；若要对象理论内部的 Con 公式，另固定算术化与背景理论并证明 Derives，不把 Lean Prop 冒充对象句子。
不以 ZFC 的普通推导证明 ¬AC；模型解释的结论和解释所处的元理论必须区分。

## 主要缺口
1. 源开放自然演绎规则（无限假设集、末自由变量）到目标有限上下文 Hilbert 核的双向传输；须用有限支撑。
2. 源 Replacement 与目标 Collection 及两种 AC 呈现的逐模式推导对应。
3. 元层纯集合、布尔值、商、全部 HS 名字的 universe 对应；不能强行固定名字秩界。
4. 可构造解释如走论文路径，应逐公理证明 ZF ⊢ α^L；语义 L 模型或文档提及 GCH 不够。
5. 将强迫系统、逻辑规则、ZF 全模式、SVC、ACwo、非选择见证及全秩 PP 装配为原核可检查接口。
6. 不可把反向单射升级成原满射的截面，不可把内部良基等同于外部 WellFounded。
7. 最终分开验收普通 Con 路线、带强不可达的传递模型路线和论文更强的序列保持结论。


公理审计边界：固定 YesMetaZFC 的 sentence! 宏用 native_decide 生成7个基础句子的 FreeClosed 证书，原生ZF合同继承其7个 native_decide.ax_1 依赖。见 docs/TRUST_BASELINE.json。当前检查精确守住此基线，不标成“仅三项标准公理”；未修改底座，也未添加新的自定义公理。后续若要求纯内核证书，需另行把这些证书改为 kernel-checked decide 并核对原理论不变。

语义桥的 Classical.choice 已定位到 Lean 核心定理 Fin.lastCases_castSucc，只用于 Prop 中的绑定等式证明；未向对象ZF加入AC，也未抽取内部集合选择函数。旧宿主辅助维持原先无 Classical.choice 的依赖范围。
