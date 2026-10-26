# 当前状态：原 1–11 阶段

本批输入基点 `380a12a`。重新对照最初 `f28b0334` 的流程表、固定源和现有验收后：**连续完整验收到原 1–3，当前主开发在 8；尚未进入收尾，最终对象 Con 未证明。** 历史 S3／STEP4 批次名及 CheckStep4 不代表原阶段编号。

| 原阶段 | 已完成／已经存在 | 真正剩余 |
|---|---|---|
| 1 | 全八构造器、首末 binder 对应、语言桥与原核连线 | 原范围已验收，不重做 |
| 2 | 重命名、替换、有限支撑、19 条源规则及双向外部证书传输 | 原范围已验收；全部内部码归约归 10 |
| 3 | 完整 ZF 模式互导及两种 AC 对应 | 已验收，不把完整模式再列为缺口 |
| 4 | 原 Main 的 8998 项构建和五端点审计有既有验收；75 份主链源码本轮重新核对全部匹配 | 完整 Comparator 未运行，缺 Linux/landrun；本轮未重跑原 4.34.1 环境 |
| 5 | 内部集合／图／ω／序列／递归、名字及作用／HS 基础已有 | 具体系统消费者归 8–10，不重建基础 |
| 6 | 新版 7979336 的任意 ZF 模型内部 L→ZF/ZFC 及完整模式已完成；本批再次回读 Model/Choice 正文，确认固定 7979336 及供体干净状态；未重跑供体构建 | 固定旧版、当前对象语言相对化与原核接口未接通；不是缺少 L 数学 |
| 7 | forces_ZF 固定公理和全部模式已有逐实例原核证书 | 源单子／Presentation／正规滤子前提待具体系统实例化；全部内部码归 10 |
| 8 | 初始 Base 与完整 margin、Path／过渡／字母商、动作／target／exit／Alphabet、锥与字母界、Raw、reduced Word、quotient、letterAct 已验收。Raw.eval、求值定律、实际 Word 左消去单子已验收；本批接通实际 oldHom 单射同态、因子／整除反映和 Word conical | generator、呈现及大小界，Probe/Merger 实际扩张、保守嵌入／margin 延拓、Placement、ConservativeHull 与最终饱和单子 |
| 9 | Models 固定源码已有 | SVC、ACwo、同一系统商单射和非选择见证的目标端迁移未完成 |
| 10 | 原 Main 链与内部 Con 合同固定；底座通用 Proof/Sat 已有 | 全秩 PP/Main 装配、ZF/U 特化、全部内部矛盾证明码归约与最终闭句 |
| 11 | 现有验收工具可复用 | 最终主定理验收未开始 |

目标保持纯成员／等词语言、完整 nativeZF 和原 FirstOrder.Derives：`Derives nativeZF [] (Con_ZF → Con_U)`，U = ZF + PP + ACwo + ¬AC。Con 的量词覆盖所有内部证明码，包括外部看来非标准的码；这里的蕴含是对象公式，不是 Lean 函数类型。当前底座 ZFC 特化的证明／满足关系配套需要 ZF/U 适配，不重建通用核或 Sat。

## 本批实际源迁移

固定源为 OpenAI `1581d4cbdd69a0faf34b2089614fe2a814316a6a` 的 Algebra/ProbeWords.lean:526–602。ConstructionProbeOldEmbedding 迁移 oldHom、old_mul_eq_old_iff、old_dvd_old_iff、old_dvd_iff_headDiv，沿原 old/cons 分支保留精确因子见证；通过 Alphabet 的 exit 分离与原 conical 前提迁移 exit_ne_one、oldAct_exit_ne_one、letterAct_ne_one 和 Word conical。

ConstructionProbeOldEmbeddingSyntax.construction_kernel_certificate 是纯成员句子的原 FirstOrder.Derives 证明：从原左消去单子及 Alphabet，构造实际 Word、单位、乘法图及 old 单射图，证明单位／乘法保持、因子刻画、两项整除等价，以及原单子 conical 时 Word conical。没有把这些结论作为未证字段，也没有为 conical 添加 b≠unit。generator 及其非单位前提仍在下一源步骤。

复用固定 YesMetaZFC 的 exists_setFunctionFromTo_of_denote；复用本仓已证 old 唯一性／单射／排斥、Word.headDiv_iff、eval_old_iff/cons、实际乘法构造；回传继续使用已接入的 BMS 式 ModelTransfer.derives。没有重建集合图、递归、完整模式、L、Proof/Sat 或完备性。

原消费者已定位到 ConservativeExtensions.lean:86 的 oldHom_conservative，以及 ProbeGates.lean:623 的 liftHom 与 ProbePresentations。当前仅完成其中 old 因子部分；完整保守扩张还需锥交／共同倍数向 Word 的提升及后续呈现，不能标为完成。

## 纠错与清理

本轮回读最初 f28b0334 的 1–11 阶段表；改动前 2533 个既有验收指纹、75 份主链来源哈希均匹配。之前将局部验收当成整体进度、将接口未接入报成数学不存在、未核对主链消费者就扩写兼容支线，都是规划与验收口径错误；对象层要求从早期已明确。当前不再以声明／构建数量或后加批次名推算完成比例。

已删除当前文档中 oldHom／整除反映／conical 仍待证明的过时待办；没有删除已有正确数学。Audit 接管本批 24 项声明后删除一次性预审文件，SHA 清单见 verification/cleanup-probe-old-embedding-20261026.json。保留预审与正式验收日志，不增加持久脚本。三个现有 scripts 均为正式验收入口。

重新检查 import 图：431 个 Packet/Varint/Reader/Bytes 名称候选仍有 13 个非同名模块直接引用。冻结兼容链依赖裁剪未完成，未按名称批量删除或声称清理完成。NatPacket、泛滤真值及独立 L 重建继续停用。工作区启动检查没有 Lean/Lake 残留；本轮只运行串行构建。

下一源链为 generator／generator_mul／generator_mul_b → evalHom／liftHom／呈现与大小界 → 实际 Probe/Merger 扩张、保守嵌入／margin、Placement／ConservativeHull。第 6 的已有 L 适配、第 9 的模型应用、第 10 的全部内部码与最终 Con 仍是真实未完成项。

## 实际验收

严格定向构建、trust=0 预审及完整 scripts/verify.py 均退出 0。全仓 2975 项构建任务；9 条正式命令全部退出 0，其中 5 次 --trust=0；31131 项声明审计：837 项无公理依赖、30294 项使用已记录依赖；0 警告；2535 个当前文件指纹全部匹配。75 份固定 OpenAI 主链源码哈希全部匹配。没有重新运行原 4.34.1 Comparator 或供体构建，不将历史结果说成本轮新增验收。

本批新增 24 项声明和 1 项原核存在证书。证书使用 22 项既有依赖：标准三项、七项基础句子证书、六项递归历史限制 Bool 证书、六项序列限制 Bool 证书；比较先前活动足迹没有新增可信依赖。正式流程仍复算既有 15 项递归、9 项基数和 6 项序列限制证书；不称整个工程只有标准三项依赖。

证据：verification/commands.json、summary.json、build.log、audit.log，以及 construction-probe-old-embedding-syntax-build.log、construction-probe-old-embedding-preaudit.log、construction-probe-old-embedding-full-verification.log。本批 old 嵌入／因子／整除／conical 标志为 true；包含完整呈现的合并标志、完整扩张和 relative_consistency_proved 仍为 false。原核主句尚未证明。仅本地提交，不上传或发布。
