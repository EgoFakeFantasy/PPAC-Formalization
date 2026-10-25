> 当前阶段见 AGENT_WORKFLOW。以下源数学路线保持固定；“源已有证明”“本仓接口”“尚未定位／尚未接入”分开读取。日期较早的验收段只代表历史批次。

# 普通相对一致性的数学归约依赖（2026-10-25）

用户纠正后的复用优先级见 [现有接口复用合同](REUSE_CONTRACTS.zh-CN.md)。下表中的“缺”指PPAC尚未接好的对象接口，不意味着底座或其他项目没有对应构造；不得按旧措辞重新开发已有满足关系、L、识别器或收尾工具。

固定终点：原纯等词／成员语言、完整 nativeZF、原 FirstOrder.Derives 中的 `Con_ZF → Con_U`，`U = ZF + PP + ACwo + ¬AC`。此表列证明义务，不是开发次数估计。

选用直接语法路线：**U 的矛盾证明 → ZFC 的矛盾证明 → ZF 的矛盾证明**。中间 ZFC 是待证明解释所涉及的理论，不是给最终背景添加 AC 假设。

| 必要命题／构造 | 已核对的实际来源 | 本仓当前证据／缺口 |
|---|---|---|
| 参数无关纯公式 L(x)，解释域非空，量词相对化 | 论文 metatheory.tex:68–93 | 参数无关候选L(x)公式与逐量词语义已接通；解释域非空仍缺实际求值见证，后续相对化使用已验收接口 |
| 固定Gödel Def后继的实际内部输出 | 原L工程RudimentaryDefOutputFormula／固定StackProgramEvalFormula；GodelDefOutput.existence_kernel_certificate、uniqueness_kernel_certificate | 原ZF内对全部14输入参数的输出存在唯一闭句已推导；原99项纯语法正文及槽位锁定。层历史及规范参数已接通；完整内部求值／Def正确性及L公理仍待传输 |
| 固定原Def的内部层递归 | YesMetaZFC原三分支算子全定义单值、原内部超限递归；GodelDefRecursion.hierarchy_kernel_certificate | 全部13参数、全部内部序数上的唯一递归值闭句已推导，历史为内部集合编码；原bareStageAt对应及规范参数已接通；L公理尚待接通 |
| 原bareStageAt全部内部序数接口 | 固定L工程BareStageHistory原14项语法；ConstructibleHistory.agreement_kernel_certificate／unique_kernel_certificate；原内部序数归纳与全分离 | 参数empty槽为空时，原历史与内部Def递归等价且层值存在唯一已推导；保留历史含杂项的原范围。规范参数已接通；求值／Def正确性仍待接通 |
| 规范参数及参数消去 | 原StageHistoryParameters／RudimentaryTermZFCode；既有SyntaxNumerals、ObjectOmega；ConstructibleParameters.unique_kernel_certificate | 规范13参数已在对象量词内消去；无参数层关系在全部内部序数上存在唯一已推导。L(x)纯公式及语义对应已定义；域非空、求值／Def正确性尚未证明 |
| 相对化保留推理，显式处理自由变量在解释域内 | Relativization.lean 的 formula／derives／source_closed_at／kernel_certificate | 本批提供全部19条源规则、任意外部有限证书及真正原核证书；非空前提保持为对象蕴含 |
| 每个 ZFC 公理的 L 相对化在 ZF 可证，含完整模式 | 原 L 工程 ZFModel.lCarrier_models_ZF、StageHistoryGraphSystem.lCarrier_models_ZFC；本仓 InterpretedZF | 原 LCarrier 的完整模式与 Choice 结论已完成。本仓全模式相对化回放已接线，保留解释背景与域非空；尚未定位到可直接调用的全 nativeZF 模型 L 终局，需要接其精确接口，不是重证底座公理模式 |
| L解释中选择公理的分离收尾 | 现成L工程Choice／InternalWellOrder；DefinableMinimaChoice.kernel_certificate、relative_kernel_certificate | 原ZF中Min_lt→AC及原库内部良序覆盖CoverWO→Min_edge→AC与域相对化已推导；实际L中的层序图／CoverWO及L域相对化ZF仍待接通 |
| 原名字 Child 关系的内部归纳 | ForcingNames.Child/child_wf；已有 SetInduction.native_induction 与 KuratowskiZF.source_edge | 已接入 ForcingNameInduction.kernel_certificate：每个任意参数公式的原核闭句，沿原三次成员下降。所有内部集合都在量化范围内；没有外部 WellFounded 假设。原 IsName/evaluate/mapConditions 与 AtomicForcing.eq_refl 是消费者，名字与原子递归及原子定律已迁入；见当前流程表 |
| 具体集合对称系统及全部内部 HS 名字类 | ProductNames.system:89–92；SymmetricNames.Name:48–49 | 缺纯对象公式、构造及全秩证明；不能把 HS 类当作地面集合，不能加全局秩截断 |
| 原子强迫的内部名字递归、单调性、等词合同及正则性 | SymmetricNames.atomic:89–100；ForcingTruth.data_regular:351–356 | 原子递归、单调性、等词合同、eq_of_dense / mem_of_dense 原核证书已完成；不可再报为未证明。当前补原子作用对称性；HS 限制及完整逻辑消费者待接 |
| 逐公式强迫翻译及逻辑规则保真 | ForcingTruth.force_of_dense:60–82、forcing_sound:240 起 | 本批 ForcingFormula / ForcingSound 已实现逐固定公式翻译与全部 19 源规则到原核的固定证明实例证书。实际 HS 域及目标公理待接；所有内部证明码的统一归约仍归阶段 10。不得定义全宇宙统一真值谓词 |
| 全 ZF 公理在 HS 解释中成立 | SymmetricChoice.forces_ZF:203–217 | 原源强迫模型证明已经存在，尚未迁移到目标解释。迁移该证明并消费既有完整 Replacement/Collection 互导；不重造全公理模式 |
| 无选择、序数指标选择与全秩 PP 在同一系统成立 | ChoiceFailure.forces_not_AC:241–260；OrdinalChoice.forces_ACwo:472–474；Main.forces_PP:133–152 | 缺对象证明。PP 依赖 OrdinalPresentation.ordinal_presentation 和 SliceAssembly.presentation_reverse_injection；不能把局部逆单射改成原满射截面 |
| 任意内部码上的完整 Ax_ZF/Ax_U、Proof_ZF/Proof_U | 固定 OBJECT_TARGET；现有 ProofTreeEntrySyntax／ProofTheoryNodeSyntax 的显式公式参数 | 检查器仍未完整实例化；六规则、27模式及全模式不可只验证固定有限表 |
| 两段语法证明归约在 ZF 内表示并证明正确 | 论文 metatheory.tex:383–394 提供数学路线 | 缺全部内部码上的传输，外部有限证书回放不等于这一项；不要求二进制程序或确定性算法 |
| 封闭最终 Con 蕴含 | 上述内部矛盾证明归约 | 缺最终 Derives；不改变既有未完成标志 |

论文目录：`../openai-math-ppac-source/preprints/The-Partition-Principle-does-not-imply-Choice-September-24-2026/build/sections/`。
源码目录：`../openai-math-ppac-source/lean/OAI/SetTheory/PartitionConsistency/`。上表涉及的11个 Lean 文件已逐个核对 SOURCE_LOCK 中的 SHA-256，固定 OpenAI 提交 `1581d4cbdd69a0faf34b2089614fe2a814316a6a`。

已剔除的额外路线：

- 不把 `V=L` 或 GCH 加为中间理论的额外公理。源码 ConcreteSystem:29–72 使用 `μ = succ(continuum)`，证明 `μ^ℵ₀ = μ` 和正则性；所需条件已有一般 ZFC 路线，故无需移植论文的 GCH 参数特化。L 仍用于把 ZFC 矛盾归约到 ZF，不能因此省略可构造解释。
- 不移植外部可数模型、泛滤选择、Mostowski 坍塌及商模型真值引理。论文 metatheory.tex:383–394 的直接有限证明归约已给出替代路线；这不免除内部语法转换证明。
- 不恢复 NatPacket、LEB128、字节／树／森林解析兼容。直接结构公理测试是独立对象公式；改变证明呈现仍须取得所需对象 Con 等价。
- 不以 PP 推出 ACwo 为理由删除源码 PP 证明中使用的 ACwo 构造；那会形成循环。两者在同一系统中的数学依赖仍按上表处理。

当前按原 1–11 阶段执行；第 6 阶段消费已有 L／Def／Gödel及配套满足关系，仅补尚未返回原ZF推导的实际接口；不重新定义整套L。对集合结构的满足关系可以在 ZF 内编码；这与被禁止的全宇宙统一真值谓词不同。不得把二者混淆后重新引入无关 packet 设施。

历史冻结工作曾保存在 `.local/frozen-packet-20261025/`；它不属于当前正式目标。当前清理范围见 CLEANUP，已验收证明尚未按批量依赖裁剪删除。

复用核查：联网只读 IBLP/Model/SetSatisfaction.lean（blob e22c8df3043f215a3a40b34e3b3c53d835b490ce）和 SetSatisfactionFormula.lean（blob 7f4dcc8cf340c6f371681c8c6ca1801a1631bf92）。前者有有界集合上的实际 Sat 集，后者含排除非法／越域条目的支持条件及有限纯公式构造；其定理依赖 ZFSet／ModelStage 的宿主语义，不能作为本项目原ZF推导证书直接导入。本轮未添加 Lake 依赖或复制这些文件。

收尾清理：删除两个弃用的 PackedTokens 包装生成／集成脚本；冻结的14个Lean文件及移位哈希清单完整保留。正式验证结束后无残留 Lean/Lake 编译进程。

2026-10-26 消费者复审：AtomicForcing 的决策稠密集仅进入 exists_truth_generic；atomic_truth 在锁定 PartitionConsistency 目录没有该定义之外的使用。普通 Main 走 SymmetricNames.atomic_regular → ForcingTruth.forcing_sound / consistent_of_forces，不需要泛滤求值真值分支。此前把该分支列成必需下一步错误；已撤回新候选，保持本文件原有直接归约选择。
