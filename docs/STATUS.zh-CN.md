# 当前状态：原 1–11 阶段

本批输入基点 `709801f`。重新对照最初 `f28b0334` 的流程表、固定源和现有验收后：**连续完整验收到原 1–3，当前主开发在 8；尚未进入收尾，最终对象 Con 未证明。** 历史 S3／STEP4 批次名及 CheckStep4 不代表原阶段编号。

| 原阶段 | 已完成／已经存在 | 真正剩余 |
|---|---|---|
| 1 | 全八构造器、首末 binder 对应、语言桥与原核连线 | 原范围已验收，不重做 |
| 2 | 重命名、替换、有限支撑、19 条源规则及双向外部证书传输 | 原范围已验收；全部内部码归约归 10 |
| 3 | 完整 ZF 模式互导及两种 AC 对应 | 已验收，不把完整模式再列为缺口 |
| 4 | 原 Main 的 8998 项构建和五端点审计有既有验收；75 份主链源码本轮重新核对全部匹配 | 完整 Comparator 未运行，缺 Linux/landrun；本轮未重跑原 4.34.1 环境 |
| 5 | 内部集合／图／ω／序列／递归、名字及作用／HS 基础已有 | 具体系统消费者归 8–10，不重建基础 |
| 6 | 新版 7979336 的任意 ZF 模型内部 L→ZF/ZFC 及完整模式已完成；上一批回读 Model/Choice 正文并确认固定 7979336 及供体干净状态；本批未重跑供体构建 | 固定旧版、当前对象语言相对化与原核接口未接通；不是缺少 L 数学 |
| 7 | forces_ZF 固定公理和全部模式已有逐实例原核证书 | 源单子／Presentation／正规滤子前提待具体系统实例化；全部内部码归 10 |
| 8 | 初始 Base 与完整 margin、Path／过渡／字母商、动作／target／exit／Alphabet、锥与字母界、Raw、reduced Word、quotient、letterAct 已验收。Raw.eval、求值定律、实际 Word 左消去单子已验收；实际 oldHom 单射同态、因子／整除反映和 Word conical 已验收；generator 实际图、乘法／作用关系和旧元素 gate 已验收；evalHom 与任意目标单子的实际 liftHom 已验收；本批接通 hom_ext 实际函数图相等和 lift 唯一性 | 路径索引呈现及大小界，Probe/Merger 实际扩张、保守嵌入／margin 延拓、Placement、ConservativeHull 与最终饱和单子 |
| 9 | Models 固定源码已有 | SVC、ACwo、同一系统商单射和非选择见证的目标端迁移未完成 |
| 10 | 原 Main 链与内部 Con 合同固定；底座通用 Proof/Sat 已有 | 全秩 PP/Main 装配、ZF/U 特化、全部内部矛盾证明码归约与最终闭句 |
| 11 | 现有验收工具可复用 | 最终主定理验收未开始 |

目标保持纯成员／等词语言、完整 nativeZF 和原 FirstOrder.Derives：`Derives nativeZF [] (Con_ZF → Con_U)`，U = ZF + PP + ACwo + ¬AC。Con 的量词覆盖所有内部证明码，包括外部看来非标准的码；这里的蕴含是对象公式，不是 Lean 函数类型。当前底座 ZFC 特化的证明／满足关系配套需要 ZF/U 适配，不重建通用核或 Sat。

## 阶段误判的纠正

已重新回读最初 f28b0334 的 1–11 流程。历史批次名、CheckStep4、构建数量及辅助声明数量均不能作为原阶段完成的证据。阶段 8 的局部对象证书已成立，不等于整个构造核心或最终一致性证明成立；不得据此称为收尾或给完成百分比。

此前将供体已有数学、旧版接口适配和最终系统实例化混为同一个缺口，造成重复规划；又将局部验收成功外推到整体进度，造成结果误判。以后每项剩余义务必须对应固定 OpenAI 源声明及实际消费者，并先查 REUSE_CONTRACTS 的现成入口。原阶段完成只按最初验收门确认，不能靠新增辅助模块数量推进编号。

## 本批实际源迁移

固定源为 OpenAI `1581d4cbdd69a0faf34b2089614fe2a814316a6a` 的 Algebra/ProbeWords.lean:688–700 Word.hom_ext。ConstructionProbeHomExt 按原 old/cons 两分支证明：old 分支使用给定取值一致；cons 分支使用既有 generator_mul_of_not_headDiv 分解，再用后缀归纳、生成元一致及乘法保持得到输出一致。

归纳性质是纯成员公式，通过现有 raw_induction 和底座内部 ω 归纳处理所有内部字长，没有使用外部标准长度。IsSetRelation.eq_of_pairMember_iff 将逐值相等变成实际内部函数图相等。lift_unique 直接消费已完成的 LiftLaws，对相同 old/generator 取值的两个 lift 给出唯一性。

ConstructionProbeHomExtSyntax.homExt_kernel_certificate 返回原 FirstOrder.Derives nativeZF [] 证书。保留实际 Word、乘法图、generator 图和乘法保持前提，不增加目标左消去。源 conical/b≠unit 用于先前 generator 图存在构造；本句从已构造的 generator 图推出唯一性。

实际消费者是 ProbeGates.Path.presentedHom_ext:635–639。它进一步把全部字母生成元的一致性归约为路径索引 probe 的一致性；该适配尚未完成。本批不把路径呈现、大小界或扩张标成完成。复用原核回传仍是已接入的 BMS 式 ModelTransfer，没有新建归纳、递归或函数图后端。

## 清理与真实后续

Audit 接管本批 19 项声明后，删除一次性预审文件，清单 verification/cleanup-probe-hom-ext-20261026.json 保留绝对路径与 SHA；预审和正式日志保留。没有新增持久脚本。覆盖表和原阶段 8 流程已将 Word.hom_ext 移入已完成范围，保留实际剩余源链。历史内容可从 Git 恢复。

NatPacket／字节兼容、泛滤真值及独立 L 重建继续停用。上一批核对的 431 个冻结名称候选及 13 个非同名模块直接消费者未改动；其依赖裁剪仍未完成，本批没有宣称已删除这些证明。启动检查无活动 Lean/Lake；本轮构建串行。

下一必要源链是 Path.presentedHom_ext／索引呈现与 Word 大小界，再接实际 Probe/Merger 扩张、保守嵌入／margin、Placement／ConservativeHull。原 evalHom 的目标 N 为任意单子；直接复用原生内部递归和现成乘法图合同，不增加目标左消去或外部良基前提。第 6、9、10 阶段的真实剩余义务不变。

## 实际验收

本批严格定向构建、--trust=0 预审及完整 scripts/verify.py 全部退出 0。全仓 2983 项构建任务；9 条正式命令全部成功，其中 5 次 --trust=0；31242 项声明审计，其中 851 项无公理依赖、30391 项沿用记录依赖；零警告。2543 个文件指纹与 75 份固定源文件哈希全部匹配。19 项新声明中 1 项无公理依赖，原核证书沿用 22 项既有依赖，没有新增可信依赖。没有重跑原 Comparator 或供体构建。

22 项证书依赖包括标准三项、七项基础句子证书、六项递归历史限制 Bool 证书、六项序列限制 Bool 证书。正式流程继续复算既有 15 项递归、9 项基数和 6 项序列限制证书；不称整个工程只有标准三项依赖。

证据：verification/commands.json、summary.json、build.log、audit.log，以及 construction-probe-hom-ext-build.log、construction-probe-hom-ext-syntax-build.log、construction-probe-hom-ext-preaudit.log、construction-probe-hom-ext-full-verification.log。本批 hom_ext 标志为 true，完整呈现、扩张及 relative_consistency_proved 仍为 false。最终原核 Con 主句未证明。验收结束无活动 Lean/Lake。仅本地提交，不上传或发布。
