# 当前状态：原 1–11 阶段

本批输入基点 `702f0d25edb0d4a33e5c281584712a32ed8db85e`。重新对照最初 `f28b0334` 的流程表、固定源和现有验收后：**连续完整验收到原 1–3，当前主开发在 8；尚未进入收尾，最终对象 Con 未证明。** 历史 S3／STEP4 批次名及 CheckStep4 不代表原阶段编号。

| 原阶段 | 已完成／已经存在 | 真正剩余 |
|---|---|---|
| 1 | 全八构造器、首末 binder 对应、语言桥与原核连线 | 原范围已验收，不重做 |
| 2 | 重命名、替换、有限支撑、19 条源规则及双向外部证书传输 | 原范围已验收；全部内部码归约归 10 |
| 3 | 完整 ZF 模式互导及两种 AC 对应 | 已验收，不把完整模式再列为缺口 |
| 4 | 原 Main 的 8998 项构建和五端点审计有既有验收；75 份主链源码本轮重新核对全部匹配 | 完整 Comparator 未运行，缺 Linux/landrun；本轮未重跑原 4.34.1 环境 |
| 5 | 内部集合／图／ω／序列／递归、名字及作用／HS 基础已有 | 具体系统消费者归 8–10，不重建基础 |
| 6 | 新版 7979336 的任意 ZF 模型内部 L→ZF/ZFC 及完整模式已完成；上一批已回读 Model/Choice 正文并确认供体版本与干净状态；本批未重跑供体 | 固定旧版、当前对象语言相对化与原核接口未接通；不是缺少 L 数学 |
| 7 | forces_ZF 固定公理和全部模式已有逐实例原核证书 | 源单子／Presentation／正规滤子前提待具体系统实例化；全部内部码归 10 |
| 8 | 初始 Base 与完整 margin、Path／过渡／字母商、动作／target／exit／Alphabet、锥与字母界、Raw、reduced Word、quotient、letterAct 已验收。Raw.eval 精确求值已验收；本批接通 eval_oldAct/eval_injective、Word.eval_letterAct、结合／单位律和实际 Word 左消去单子 | 原 oldHom／整除反映、conical／generator、呈现及大小界，Probe/Merger 实际扩张、保守嵌入／margin 延拓、Placement、ConservativeHull 与最终饱和单子 |
| 9 | Models 固定源码已有 | SVC、ACwo、同一系统商单射和非选择见证的目标端迁移未完成 |
| 10 | 原 Main 链与内部 Con 合同固定；底座通用 Proof/Sat 已有 | 全秩 PP/Main 装配、ZF/U 特化、全部内部矛盾证明码归约与最终闭句 |
| 11 | 现有验收工具可复用 | 最终主定理验收未开始 |

目标保持纯成员／等词语言、完整 nativeZF 和原 FirstOrder.Derives：`Derives nativeZF [] (Con_ZF → Con_U)`，U = ZF + PP + ACwo + ¬AC。Con 的量词覆盖所有内部证明码，包括外部看来非标准的码；这里的蕴含是对象公式，不是 Lean 函数类型。当前底座 ZFC 特化的证明／满足关系配套需要 ZF/U 适配，不重建通用核或 Sat。

## 本批实际源迁移

固定源仍为 OpenAI `1581d4cbdd69a0faf34b2089614fe2a814316a6a` 的 Algebra/ProbeWords.lean:457–523。ConstructionProbeEvaluationLaws 沿原构造器案例证明 eval_oldAct，沿原 headDiv 分支证明 Word.eval_letterAct。源 Raw 归纳的性质由 lengthSchema 编成纯公式，直接调用底座 Separation、IsOmega.induction 与现成有限序列末项分解；据此证明 eval_injective。该接口立即被下面的结合律和右单位律消费，不是另建通用归纳后端。

ConstructionProbeWordMonoid 沿原 old/cons 归纳证明 mul_assoc 与 mul_one；前者消费 eval_oldAct/eval_letterAct，后者消费 reduced_cons 和原 letterAct 非 headDiv 支。原生 exists_setFunctionFromTo_of_denote 在实际 W×W 上构造精确求值乘法表。左单位来自 oldAct_one，左消去来自 eval_injective。

ConstructionProbeWordMonoidSyntax.construction_kernel_certificate 在纯成员语言和原 FirstOrder.Derives 中证明：由原左消去单子与 Alphabet、b∈D，构造实际 Word 集合、old 单位、W×W 输入集和乘法图，并满足 LeftCancelMonoid。没有把 Word、乘法表或单子律作为未证字段。整个构造保留所有内部有限长度，包括外部看来非标准的长度；未加对象 AC、外部良基或新的推导核。

本批直接复用固定底座的 ω 归纳、分离、序列解析、可定义函数图，以及已经接入的 BMS 式 ModelTransfer 原核完备性接口。L 数学、通用 Proof/Sat 与完整模式没有重建，也没有因本批单子完成而被误报为最终 Con 已接通。

## 纠错、清理与后续边界

此前“收尾”判断错误：把局部构建／辅助验收当作整体进度，把接口尚未接入误报为数学尚未完成，且曾以同文件相邻定理代替实际消费者判断。对象层要求并非后来新增。最初 1–11 阶段和最终 Con 合同始终不变；不再用声明数、构建数或拆分批次数给完成比例。

本轮更新当前流程／缺口／覆盖／复用表，撤出“求值定律与 Word 单子尚待证明”的旧待办，缩短首页和重复的直接消费者叙述。正式 Audit 接管 29 项声明后，删除一次性预审输入；清理记录见 verification/cleanup-probe-word-monoid-20261026.json。保留正式验收及预审日志，没有新增长期生成脚本。旧的失败定向日志被后续成功的 syntax 定向构建和正式全仓构建覆盖，清理后不作为当前证据。

NatPacket／字节兼容、泛滤真值与独立 L 重建继续停用。冻结旧证明的整体依赖裁剪尚未完成，未删除仍被引用的模块，也不把它们计为主目标新进度。本批编译验收结束，无活动 Lean/Lake 进程；工作区保留当前已验收源码。

下一必要源链是 oldHom／old_mul_eq_old_iff／old_dvd_old_iff／old_dvd_iff_headDiv → conical／generator → evalHom／liftHom 与呈现。实际消费者已回读：ConservativeExtensions.lean:86、ProbeGates.lean:623 及 ProbePresentations 的保守／生成元映射链。随后接大小界、Probe/Merger 扩张、margin、Placement／ConservativeHull。不是把源文件相邻的任意引理都增加为新义务。

第 6、9、10 阶段真实缺口仍在；不得重复报告已有 L、完整模式、递归、Proof/Sat 或完备性缺失。

## 实际验收

严格定向构建、trust=0 预审及完整 scripts/verify.py 均退出 0。全仓 2973 项构建任务；9 条正式命令全部退出 0，其中 5 次 --trust=0；31107 项声明审计：831 项无公理依赖、30276 项使用已记录依赖；0 警告；2533 个当前文件指纹全部匹配。75 份固定 OpenAI 主链源码哈希全部匹配。

本批新增 29 项声明和1项原核存在证书。证书使用 22 项既有依赖：标准三项、七项基础句子证书、六项递归历史限制 Bool 证书、六项序列限制 Bool 证书；比较先前活动足迹没有新增可信依赖。正式流程仍复算既有 15 项递归、9 项基数和6项序列限制证书；不把这些说成已消除 native 信任或只有标准三项。

证据：verification/commands.json、summary.json、build.log、audit.log、construction-probe-word-monoid-syntax-build.log、construction-probe-word-monoid-preaudit.log 和 construction-probe-word-monoid-full-verification.log。求值定律、实际 Word 左消去单子状态为 true；conical／嵌入／呈现、完整扩张及 relative_consistency_proved 仍为 false。仅本地提交，不上传或发布。
