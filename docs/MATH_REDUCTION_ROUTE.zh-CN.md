# 普通相对一致性的数学归约依赖（2026-10-25）

用户纠正后的复用优先级见 [现有接口复用合同](REUSE_CONTRACTS.zh-CN.md)。下表中的“缺”指PPAC尚未接好的对象接口，不意味着底座或其他项目没有对应构造；不得按旧措辞重新开发已有满足关系、L、识别器或收尾工具。

固定终点：原纯等词／成员语言、完整 nativeZF、原 FirstOrder.Derives 中的 `Con_ZF → Con_U`，`U = ZF + PP + ACwo + ¬AC`。此表列证明义务，不是开发次数估计。

选用直接语法路线：**U 的矛盾证明 → ZFC 的矛盾证明 → ZF 的矛盾证明**。中间 ZFC 是待证明解释所涉及的理论，不是给最终背景添加 AC 假设。

| 必要命题／构造 | 已核对的实际来源 | 本仓当前证据／缺口 |
|---|---|---|
| 参数无关纯公式 L(x)，解释域非空，量词相对化 | 论文 metatheory.tex:68–93 | 既有L／Def模块和配套已定位；待完成纯对象句子、原ZF背景及推导接口的接入，不重建构造 |
| 相对化保留推理，显式处理自由变量在解释域内 | Relativization.lean 的 formula／derives／source_closed_at／kernel_certificate | 本批提供全部19条源规则、任意外部有限证书及真正原核证书；非空前提保持为对象蕴含 |
| 每个 ZFC 公理的 L 相对化在 ZF 可证，含完整模式 | 论文 metatheory.tex:68–93 | 缺逐模式原核证书和统一的语法证书生成／内部准确性；宿主 models_ZFC 不可替代 |
| L解释中选择公理的分离收尾 | 现成L工程Choice／InternalWellOrder；DefinableMinimaChoice.kernel_certificate、relative_kernel_certificate | 原ZF中Min_lt→AC及原库内部良序覆盖CoverWO→Min_edge→AC与域相对化已推导；实际L中的层序图／CoverWO及L域相对化ZF仍待接通 |
| 具体集合对称系统及全部内部 HS 名字类 | ProductNames.system:89–92；SymmetricNames.Name:48–49 | 缺纯对象公式、构造及全秩证明；不能把 HS 类当作地面集合，不能加全局秩截断 |
| 原子强迫的内部名字递归、单调性、等词合同及正则性 | SymmetricNames.atomic:89–100；ForcingTruth.data_regular:351–356 | 缺对象定义与实际原核证明；不能把 Regular 当作未消除的目标假设 |
| 逐公式强迫翻译及逻辑规则保真 | ForcingTruth.force_of_dense:60–82、forcing_sound:240 起 | 源为宿主证明；缺对象逐实例证书与递归语法转换。不得定义全宇宙的统一真值谓词 |
| 全 ZF 公理在 HS 解释中成立 | SymmetricChoice.forces_ZF:203–217 | 缺对象逐模式 Separation／Collection 证明；Replacement 与 Collection 先用已验收呈现互导对应 |
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

当前先接入已完成的 L／Def／Gödel及配套满足关系，再补尚未返回原ZF推导的实际接口；不重新定义整套L。对集合结构的满足关系可以在 ZF 内编码；这与被禁止的全宇宙统一真值谓词不同。不得把二者混淆后重新引入无关 packet 设施。

冻结工作保存在 `.local/frozen-packet-20261025/`，14文件均有移前／移后相同的 SHA-256，清单为该目录的 manifest.json；没有删除已验收证明。

本批实际验收：`python scripts/verify.py` 通过，2635 构建任务，28543 审计声明，9条命令全部成功（含5条 trust=0），零警告。新增 Relativization 的13个声明全部进入审计，仅使用 propext／Quot.sound／Classical.choice；未增加对象AC。完整检查输出保存在 verification/，最终Con与专用内部检查器等五项原未完成标志仍为 false。

复用核查：联网只读 IBLP/Model/SetSatisfaction.lean（blob e22c8df3043f215a3a40b34e3b3c53d835b490ce）和 SetSatisfactionFormula.lean（blob 7f4dcc8cf340c6f371681c8c6ca1801a1631bf92）。前者有有界集合上的实际 Sat 集，后者含排除非法／越域条目的支持条件及有限纯公式构造；其定理依赖 ZFSet／ModelStage 的宿主语义，不能作为本项目原ZF推导证书直接导入。本轮未添加 Lake 依赖或复制这些文件。

收尾清理：删除两个弃用的 PackedTokens 包装生成／集成脚本；冻结的14个Lean文件及移位哈希清单完整保留。正式验证结束后无残留 Lean/Lake 编译进程。
