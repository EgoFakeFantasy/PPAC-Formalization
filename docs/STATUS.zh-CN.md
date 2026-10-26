# 当前状态：原 1–11 阶段

本批输入基点 `3b4270f`。重新对照最初 `f28b0334` 的流程表、固定源和现有验收后：**连续完整验收到原 1–3，当前主开发在 8；尚未进入收尾，最终对象 Con 未证明。** 历史 S3／STEP4 批次名及 CheckStep4 不代表原阶段编号。

| 原阶段 | 已完成／已经存在 | 真正剩余 |
|---|---|---|
| 1 | 全八构造器、首末 binder 对应、语言桥与原核连线 | 原范围已验收，不重做 |
| 2 | 重命名、替换、有限支撑、19 条源规则及双向外部证书传输 | 原范围已验收；全部内部码归约归 10 |
| 3 | 完整 ZF 模式互导及两种 AC 对应 | 已验收，不把完整模式再列为缺口 |
| 4 | 原 Main 的 8998 项构建和五端点审计有既有验收；75 份主链源码本轮重新核对全部匹配 | 完整 Comparator 未运行，缺 Linux/landrun；本轮未重跑原 4.34.1 环境 |
| 5 | 内部集合／图／ω／序列／递归、名字及作用／HS 基础已有 | 具体系统消费者归 8–10，不重建基础 |
| 6 | 新版 7979336 的任意 ZF 模型内部 L→ZF/ZFC 及完整模式已完成；上批回读 Model/Choice 正文并确认固定 7979336 及供体干净状态；本批未重跑供体构建 | 固定旧版、当前对象语言相对化与原核接口未接通；不是缺少 L 数学 |
| 7 | forces_ZF 固定公理和全部模式已有逐实例原核证书 | 源单子／Presentation／正规滤子前提待具体系统实例化；全部内部码归 10 |
| 8 | 初始 Base 与完整 margin、Path／过渡／字母商、动作／target／exit／Alphabet、锥与字母界、Raw、reduced Word、quotient、letterAct 已验收。Raw.eval、求值定律、实际 Word 左消去单子已验收；实际 oldHom 单射同态、因子／整除反映和 Word conical 已验收；generator 实际图、乘法／作用关系和旧元素 gate 已验收；evalHom 与任意目标单子的实际 liftHom 已验收；hom_ext 实际函数图相等和 lift 唯一性已验收；实际索引 probe 图与 Path.presentedHom_ext 已验收；相邻过渡传输、实际 interpretedLetter 及代表公式／动作等变已验收；exit 相容、实际 probe 关系及索引呈现同态存在唯一性已验收；Raw/扩张大小界已验收；本批接通实际映射路径／因子／终端表及字母商映射、代表公式、单射反映 | 动作／exit／锥相容与 Word 保守模拟，Probe/Merger 实际扩张、保守嵌入／margin 延拓、Placement、ConservativeHull 与最终饱和单子 |
| 9 | Models 固定源码已有 | SVC、ACwo、同一系统商单射和非选择见证的目标端迁移未完成 |
| 10 | 原 Main 链与内部 Con 合同固定；底座通用 Proof/Sat 已有 | 全秩 PP/Main 装配、ZF/U 特化、全部内部矛盾证明码归约与最终闭句 |
| 11 | 现有验收工具可复用 | 最终主定理验收未开始 |

目标保持纯成员／等词语言、完整 nativeZF 和原 FirstOrder.Derives：`Derives nativeZF [] (Con_ZF → Con_U)`，U = ZF + PP + ACwo + ¬AC。Con 的量词覆盖所有内部证明码，包括外部看来非标准的码；这里的蕴含是对象公式，不是 Lean 函数类型。当前底座 ZFC 特化的证明／满足关系配套需要 ZF/U 适配，不重建通用核或 Sat。

## 阶段误判的纠正

已重新回读最初 f28b0334 的 1–11 流程。历史批次名、CheckStep4、构建数量及辅助声明数量均不能作为原阶段完成的证据。阶段 8 的局部对象证书已成立，不等于整个构造核心或最终一致性证明成立；不得据此称为收尾或给完成百分比。

此前将供体已有数学、旧版接口适配和最终系统实例化混为同一个缺口，造成重复规划；又将局部验收成功外推到整体进度，造成结果误判。以后每项剩余义务必须对应固定 OpenAI 源声明及实际消费者，并先查 REUSE_CONTRACTS 的现成入口。原阶段完成只按最初验收门确认，不能靠新增辅助模块数量推进编号。

## 本批实际源迁移

固定 OpenAI 1581d4c 的 ProbePresentations.Path.map/map_node/map_factor/map_terminal，以及 lettersMap/lettersMap_letter/lettersMap_injective。直接消费者是同文件 alphabetSimulation:105，随后为 Word.transportHom:243 和 transport_conservative:572。

ConstructionProbeMappedPath 使用原生 exists_compositionFunction 构造 node 的实际像图；原路径的递增和终端见证经乘法保持传输，得到实际新路径，再调用已完成的 exists_factor_table/exists_terminal_table，证明因子／终端的精确像关系。没有把映射路径或表的存在作为前提。

ConstructionProbeLettersMap 从实际投影的代表出发构造内部商映射函数图；良定义性用既有 letter_eq_iff 共同阶段判据。反映单射时，把较大底座上的共同阶段拉回源路径，用已有 transition_total/transition_unique 及底座映射的单射性反映相等；不假设过渡映射单射。两个 Syntax 模块在原 FirstOrder.Derives nativeZF [] 中分别给出路径／表存在和实际字母图／代表公式／单射反映证书，覆盖所有内部索引。

没有新增递归、直极限或函数图后端。FactorMap 的实际见证由前一个证书提供；字母图消费已经构造的源／目标商投影及其相等判据。这还不是完整 AlphabetSimulation 或 Word.transport_conservative。

## 清理与真实后续

删除未使用的化简项；正式 Audit 接管 44 项声明后删除唯一临时预审输入，绝对路径及 SHA 清单在 verification/cleanup-probe-mapped-letters-20261026.json。正式日志保留，没有新增持久生成脚本。启动时工作区干净，构建串行。

下一个真实消费者：lettersMap_act、lettersMap_exit、lettersMap_inCone_iff → alphabetSimulation，随后按原 Raw/Word.transport → transportHom → transport_conservative 迁移。已完成的 map／因子表／终端表／字母图不再列为待重证。实际 Probe/Merger 扩张、保守嵌入／margin、Placement／ConservativeHull 及原 6、9–11 阶段的剩余不变。

NatPacket／字节兼容、泛滤真值和独立 L 重建继续停用。已验收冻结模块的精确依赖裁剪尚未完成，不能称其已全部清除。最终目标仍是全部内部证明码下的对象 Con 蕴含。

## 实际验收

四个模块的最终定向构建均通过；--trust=0 预审退出 0。44 项声明中 16 项无公理依赖，两个原核证书各沿用标准三项及七项已有基础句子证书；没有新增可信依赖。完整 scripts/verify.py 已退出 0：2997 项构建任务；9 条命令全部退出 0，其中 5 条 --trust=0；31406 项声明（879 无公理依赖，30527 有已记录依赖）；0 警告。2557 个验收指纹和 75 份固定源主链哈希全部匹配。验收结束无活动 Lean/Lake。

证据：verification/commands.json、summary.json、build.log、audit.log，以及 construction-probe-mapped-path-build.log、construction-probe-letters-map-build.log、construction-probe-letters-map-syntax-build.log、construction-probe-mapped-letters-preaudit.log、construction-probe-mapped-letters-full-verification.log。原 L 供体和原 4.34.1 Main 本批未重跑。仅本地提交，不上传或发布。
