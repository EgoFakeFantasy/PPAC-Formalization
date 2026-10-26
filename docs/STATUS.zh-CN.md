# 当前状态：原 1–11 阶段

本批输入基点 `bc8f71c`。重新对照最初 `f28b0334` 的流程表、固定源和现有验收后：**连续完整验收到原 1–3，当前主开发在 8；尚未进入收尾，最终对象 Con 未证明。** 历史 S3／STEP4 批次名及 CheckStep4 不代表原阶段编号。

| 原阶段 | 已完成／已经存在 | 真正剩余 |
|---|---|---|
| 1 | 全八构造器、首末 binder 对应、语言桥与原核连线 | 原范围已验收，不重做 |
| 2 | 重命名、替换、有限支撑、19 条源规则及双向外部证书传输 | 原范围已验收；全部内部码归约归 10 |
| 3 | 完整 ZF 模式互导及两种 AC 对应 | 已验收，不把完整模式再列为缺口 |
| 4 | 原 Main 的 8998 项构建和五端点审计有既有验收；75 份主链源码本轮重新核对全部匹配 | 完整 Comparator 未运行，缺 Linux/landrun；本轮未重跑原 4.34.1 环境 |
| 5 | 内部集合／图／ω／序列／递归、名字及作用／HS 基础已有 | 具体系统消费者归 8–10，不重建基础 |
| 6 | 新版 7979336 的任意 ZF 模型内部 L→ZF/ZFC 及完整模式已完成；上一批回读 Model/Choice 正文并确认固定 7979336 及供体干净状态；本批未重跑供体构建 | 固定旧版、当前对象语言相对化与原核接口未接通；不是缺少 L 数学 |
| 7 | forces_ZF 固定公理和全部模式已有逐实例原核证书 | 源单子／Presentation／正规滤子前提待具体系统实例化；全部内部码归 10 |
| 8 | 初始 Base 与完整 margin、Path／过渡／字母商、动作／target／exit／Alphabet、锥与字母界、Raw、reduced Word、quotient、letterAct 已验收。Raw.eval、求值定律、实际 Word 左消去单子已验收；实际 oldHom 单射同态、因子／整除反映和 Word conical 已验收；本批接通 generator 实际图、乘法／作用关系和旧元素 gate | evalHom／liftHom、hom_ext、呈现及大小界，Probe/Merger 实际扩张、保守嵌入／margin 延拓、Placement、ConservativeHull 与最终饱和单子 |
| 9 | Models 固定源码已有 | SVC、ACwo、同一系统商单射和非选择见证的目标端迁移未完成 |
| 10 | 原 Main 链与内部 Con 合同固定；底座通用 Proof/Sat 已有 | 全秩 PP/Main 装配、ZF/U 特化、全部内部矛盾证明码归约与最终闭句 |
| 11 | 现有验收工具可复用 | 最终主定理验收未开始 |

目标保持纯成员／等词语言、完整 nativeZF 和原 FirstOrder.Derives：`Derives nativeZF [] (Con_ZF → Con_U)`，U = ZF + PP + ACwo + ¬AC。Con 的量词覆盖所有内部证明码，包括外部看来非标准的码；这里的蕴含是对象公式，不是 Lean 函数类型。当前底座 ZFC 特化的证明／满足关系配套需要 ZF/U 适配，不重建通用核或 Sat。

## 本批实际源迁移

固定源为 OpenAI `1581d4cbdd69a0faf34b2089614fe2a814316a6a` 的 Algebra/ProbeWords.lean:599–616、683–725，以及 Path.probe_transition:776 的 old/cons 计算。ConstructionProbeGenerator 将 generator 精确表示为 cons(s,old(unit))，由原生函数图构造得到 S→Word 的实际内部图；沿源 conical 和 b≠unit 前提证明 reduced 闭包。

五项原关系已经证明：generator 乘法等于 letterAct、generator*old(b)=old(exit)、旧元素作用与 generator 相容、非 headDiv 时的 cons 乘法分解，以及 generator 整除 old(y) 当且仅当 exit 整除 y。最后一个反向见证是原 old(b)*old(t) 按已有乘法方程化简后的 old(b*t)，不是改写为其他整除性质。

ConstructionProbeGeneratorSyntax.construction_kernel_certificate 是纯成员句子的原 FirstOrder.Derives 证明。它组合现成构造，给出实际 Word、单位、乘法图、old 单射图和 generator 图，并包含 LeftCancelMonoid、conical、old 嵌入定律和上述五项关系。保留全部内部 Word，未限制外部标准长度。

实际复用 fixed YesMetaZFC 的 exists_setFunctionFromTo_of_denote、既有 exists_cons/cons_unique、reduced_cons、eval_old_iff/eval_cons_iff、oldAct_one、letterAct_oldAct_b 和上批 oldAct_eq_old_iff；原核回传仍是已接入的 BMS 式 ModelTransfer。没有增加新的递归、函数图或代数后端。

已核对实际消费者：ProbeGates.lean:386、388、452；ProbePresentations.lean:531、533；ProbeMargins.lean:375、408–409；ProbeWords 的 hom_ext、probe_mul_b/probe_transition/probe_not_le。当前只迁移它们使用的生成元关系，没有把整个呈现或 Path 扩张标成完成。

## 清理与真实后续

Audit 接管本批 21 项声明后，删除一次性预审文件，清单 verification/cleanup-probe-generator-20261026.json 保留绝对路径与 SHA；预审和正式日志保留。没有新增持久脚本。覆盖表中删除反复堆叠的下游进度叙述，各行保留自身准确范围；原阶段 8 流程缩为实际资产及剩余源链。历史内容可从 Git 恢复。

NatPacket／字节兼容、泛滤真值及独立 L 重建继续停用。上一批核对的 431 个冻结名称候选及 13 个非同名模块直接消费者未改动；其依赖裁剪仍未完成，本批没有宣称已删除这些证明。启动检查无活动 Lean/Lake；本轮构建串行。

下一必要源链是 evalHom／liftHom／hom_ext、呈现与 Word 大小界，再接实际 Probe/Merger 扩张、保守嵌入／margin、Placement／ConservativeHull。原 evalHom 的目标 N 为任意单子；直接复用原生内部递归和现成乘法图合同，不增加目标左消去或外部良基前提。第 6、9、10 阶段的真实剩余义务不变。

## 实际验收

严格定向构建、trust=0 预审及完整 scripts/verify.py 均退出 0。全仓 2977 项构建任务；9 条正式命令全部退出 0，其中 5 次 --trust=0；31152 项声明审计：841 项无公理依赖、30311 项使用已记录依赖；0 警告；2537 个当前文件指纹全部匹配。75 份固定 OpenAI 主链源码哈希全部匹配。没有重跑原 Comparator 或其他供体构建。

本批新增 21 项声明和 1 项原核存在证书。证书使用 22 项既有依赖：标准三项、七项基础句子证书、六项递归历史限制 Bool 证书、六项序列限制 Bool 证书；没有新增可信依赖。正式流程仍复算既有 15 项递归、9 项基数和 6 项序列限制证书；不称整个工程只有标准三项依赖。

证据：verification/commands.json、summary.json、build.log、audit.log，以及 construction-probe-generator-syntax-build.log、construction-probe-generator-preaudit.log、construction-probe-generator-full-verification.log。本批 generator 图／关系／旧元素 gate 标志为 true；完整呈现、完整扩张及 relative_consistency_proved 仍为 false。最终原核主句未证明。构建结束无活动 Lean/Lake 进程；仅本地提交，不上传或发布。
