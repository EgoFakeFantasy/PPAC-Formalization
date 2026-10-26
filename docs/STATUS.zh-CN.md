# 当前状态：原 1–11 阶段

本批输入基点 `6c638d9`；一般差值和加法相消已在该基点验收，结合律已在 `7828bfe` 验收。已从最初 `f28b0334` 回读原流程，并核对现行验收，而非沿用历史批次编号。**连续完整验收到第 1–3 阶段；主开发仍在第 8 阶段，最终对象 Con 未证明，不是收尾。**

| 原阶段 | 已完成／已经存在 | 真正剩余 |
|---|---|---|
| 1 | 全八构造器、首末 binder 对应、语言桥与原核连线 | 原范围已验收，不重做 |
| 2 | 重命名、替换、有限支撑、19 条源规则及双向外部证书传输 | 原范围已验收；全部内部码归约归 10 |
| 3 | 完整 ZF 模式互导及两种 AC 对应 | 已验收，不再列为缺口 |
| 4 | 原 Main 的 8998 项构建和五端点审计有既有验收 | 完整 Comparator 未运行，缺 Linux/landrun；本轮未重跑原 4.34.1 环境 |
| 5 | 内部集合／图／ω／序列／递归、名字及作用／HS 基础已有 | 具体系统消费者归 8–10，不重建基础 |
| 6 | 新版 7979336 的任意 ZF 模型内部 L→ZF/ZFC 和完整模式已有；此前已核对版本及干净工作树，本批未重跑或修改供体 | 固定旧版、当前对象语言相对化与原核接口未接通；不是缺少 L 数学 |
| 7 | forces_ZF 固定公理和全部模式已有逐实例原核证书 | 仍保留源单子／Presentation／正规滤子前提，待具体系统实例化；全部内部码归 10 |
| 8 | 初始 Base 及严格 margin；内部 Path/Alphabet/Word、old/generator/probe 图、呈现、大小界、保守模拟、条件并、profile 保持、pushout；floor、条件式 cost 界、加法/max、正整数除法、/4 与四倍和恢复已有。一般加法结合律已有；一般差值精确加回／所有切割解唯一性、加法序反映／相消已有；本批接实际逐字母区间及统一锥外 cost 界（保留旧 uniform margin） | heightIntervals 内部函数图、旧 HeightCost 接口适配、Word height/cost/margin 和 Probe 装配；Merger、Placement、ConservativeHull、最终饱和单子 |
| 9 | Models 固定源码已有 | 同一系统中的全秩 SVC、ACwo、商单射和非选择见证尚未迁移完成 |
| 10 | 原 Main 链与内部 Con 合同固定；底座通用 Proof/Sat 已有 | 全秩 PP/Main 装配、ZF/U 特化、全部内部矛盾证明码归约与最终闭句 |
| 11 | 现有验收工具可复用 | 最终主定理验收未开始 |

目标保持纯成员／等词语言、完整 nativeZF 和原 FirstOrder.Derives：`Derives nativeZF [] (Con_ZF → Con_U)`，U = ZF + PP + ACwo + ¬AC。Con 覆盖所有内部证明码，包括外部看来非标准的码；蕴含是对象公式。现成 ZFC 特化 Proof/Sat 需要 ZF/U 适配，不另建通用核或 Sat。

## 本轮实查与误判纠正

- 此前基点的 2459 份验收哈希已与当时工作树逐一匹配；本批更新到 2467 份并再次全部匹配，九条既有验收命令均退出 0；这些结果真实，但最终 Con 标志仍为 false。编译成功不能推出全迁移完成。
- 原阶段 1–3 的语言、推导和全理论对应已经完成；L 数学、完整模式、内部递归、函数图、Proof/Sat 不能再误报为待研发。
- 第 6 阶段缺供体接口适配，第 7 阶段保留实际系统前提；把它们与已完成的供体数学混为一谈，是先前重复规划的原因。
- 将可选 Packet/reader 字节兼容当作主定理义务、用局部验收外推整体进度，造成范围扩张和“收尾”误判。对象层目标早已明确，不是用户后来改了要求。
- 已有 BMS 式 ModelTransfer 回传在当前库实际使用。本轮再次通过它取得纯对象闭句的原核证书；没有重造完备性。新版 L、原生集合图及内部算术的复用边界见 REUSE_CONTRACTS。

## 本批实际源迁移

原源：Algebra/ProbeMargins.lean 的 `Path.target_lt_exit:106`、`Path.exists_letter_interval:117`，消费者是 `heightIntervals:144` 和 `Word.rawHeight:210`。旧前提对应 MergerCones.lean 的 `UniformMargin:12`、`HeightCost.uniform_margin:44`。本批不假设新 Word 的 margin。

- ConstructionProbeIntervals 按原公式构造 p=target−floor、K=max(p,C)、delta=(exit−floor−K)/4、offset=floor+2delta。复用前批差值、相消、max、/4、四倍和恢复及结合律，证明 delta 非空、floor+delta<offset、offset+delta+K<exit。Recipe 保留实际运算的成员公式并证明固定 C 时三个输出唯一，供内部函数图装配使用。
- ConstructionProbeLetterIntervals 在同一组实际 floor／target／exit／height／cost 图上证明 target 严格小于 exit，构造逐字母区间，并证明同一个 K 控制所有旧锥外 cost。按源证明分成“d 整除 target”和“不整除 target”两支，前一支消费既有 target_outside_cost 并用加法相消，后一支消费旧 uniform margin。
- 两个原核闭句分别为 `ConstructionProbeIntervalsSyntax.construction_kernel_certificate` 和 `letter_kernel_certificate`，返回原 `FirstOrder.Derives nativeZF [] …`。保留的 UniformMargins 是旧 HeightCost 的一致成本界输入；区间和新 K 的统一界是结论，不是前提。

**准确边界：逐字母存在性已证明，但 source heightIntervals 的全体内部函数图尚未装配。** 固定旧 C 的 Recipe 唯一性已证；下一步以原遗漏成本集合的精确上确界规范化 C，消费既有 bounded_union／Separation 和可定义函数图入口，不能将宿主 choose 当作内部对象选择。旧 Base 的完整严格 margin 已有，只需适配其已有表示，不重证其数学。后继 Word height/cost/margin 仍未完成。

本批删除一个没有消费者的新辅助引理及无用局部绑定，没有新增持久生成脚本。39 项声明的严格定向构建与 --trust=0 预审均退出 0；两个原核端点均继承已有 25 项依赖，没有新增可信依赖。正式 scripts/verify.py 已退出 0：2907 项构建，29648 项声明（948 项无公理依赖、28700 项有已记录依赖），九条命令全部退出 0，五次 --trust=0，零警告。2467 份当前受验文件指纹及 75 份固定源哈希全部匹配。完整日志：verification/construction-probe-intervals-full-verification.log。

## 当前必要顺序与停止项

按固定源继续：规范旧 uniform bound 的已有成本上确界 → 装配 heightIntervals 的内部 offset／scale／outsideBound 函数图 → 同一 Word 的实际 height/cost、严格 margin 和旧 cost 上确界保持 → 完整 Probe → Merger → Placement／ConservativeHull → 最终单子。再与第 6 阶段接口、第 9 阶段模型应用和第 10 阶段全部内部证明码归约汇合。

差值、加法序反映／相消、结合律、max、/4 和四倍和恢复均不再是缺口。本批逐字母区间已有原核证书，不能再写作“区间算术未证明”；真正剩余是上述规范选择／函数图和后继构造，不能把点态存在性误记为 heightIntervals 或整个 margin 已完成。

停止：NatPacket／reader 兼容、泛滤 atomic_truth 支线、独立 L 重建、当前消费者不需要的完整实数域。工作树清理按精确依赖闭包执行；已证明不等于主线需要，未找到接口也不等于数学不存在。

## 本轮清理复审与执行边界

此前“291 个 Packet 模块仍被其他证明引用，所以保留”的结论不够完整。反向追踪发现，这 291 个模块只牵连 67 个同属冻结兼容支线的内部消费者；总共 358 个模块，没有其他保留证明模块 import 它们。对应 14 个专用检查函数、263 个重复测试、3219 项专用声明审计及 19 项兼容状态输出也列入同一退役提案。通用保留源码编译、完整声明审计、原核 trust=0 及最终 Con 验收门均保留。

**该批量删除被自动审批拒绝，尚未执行。** 拒绝理由是删除范围大、涉及验证脚本／审计调整，当前授权未明确覆盖这份具体清单。现已完成逐文件哈希、358 份源码及原检查文件的 ZIP 归档校验，并生成完整拟议 patch；拟议 verifier 已通过 Python AST 解析，剩余源码指向候选模块的 import 为 0。这是静态方案检查，不是删除后编译验收。

精确方案：verification/retired-packet-closure-review.json；归档：同名 .zip；拟议差异：同名 .patch。恢复基点为 7828bfe。待用户批准这份具体清单后执行并重新全量验收；不通过另一条命令绕过审批。

本轮只删除已由正式 Audit 覆盖的本轮重复预审输入，成功构建／预审／全量验收日志全部保留，清单见 verification/cleanup-cut-associativity-20261027.json。没有残留 Lean/Lake 编译进程；没有终止其他项目或应用进程。Agent 广场本轮连接拒绝，未写入其数据文件；需要使用时可双击 C:/Users/17857/AgentPlaza/启动广场.bat。


本批收尾进程复核：全量验收句柄已明确退出 0，复核时没有 Lean/Lake 进程。此前其他 BTBMS 工程的编译未被干预。358 项退役提案的 patch 在新主线改动后只读检查仍可应用，但依然未执行。
