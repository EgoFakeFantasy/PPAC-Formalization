# 当前状态：原 1–11 阶段

本批输入基点 `4914789`。按最初 `f28b0334` 的原流程：**连续完整验收到 1–3，当前主开发在 8；尚未进入收尾，最终对象 Con 未证明。** 本批迁移固定 OpenAI ProbeMargins 的锥内／锥外 cost 界，当前仍属原第 8 阶段。

| 原阶段 | 已完成／已经存在 | 真正剩余 |
|---|---|---|
| 1 | 全八构造器、首末 binder 对应、语言桥与原核连线 | 原范围已验收，不重做 |
| 2 | 重命名、替换、有限支撑、19 条源规则及双向外部证书传输 | 原范围已验收；全部内部码归约归 10 |
| 3 | 完整 ZF 模式互导及两种 AC 对应 | 已验收，不把完整模式再列为缺口 |
| 4 | 原 Main 的 8998 项构建和五端点审计有既有验收；75 份主链源码本轮重新核对全部匹配 | 完整 Comparator 未运行，缺 Linux/landrun；本轮未重跑原 4.34.1 环境 |
| 5 | 内部集合／图／ω／序列／递归、名字及作用／HS 基础已有 | 具体系统消费者归 8–10，不重建基础 |
| 6 | 新版 7979336 的任意 ZF 模型内部 L→ZF/ZFC 及完整模式已完成；最近复审回读 Model/Choice 正文，确认版本 7979336 及当时供体干净状态；本批未重跑供体构建 | 固定旧版、当前对象语言相对化与原核接口未接通；不是缺少 L 数学 |
| 7 | forces_ZF 固定公理和全部模式已有逐实例原核证书 | 源单子／Presentation／正规滤子前提待具体系统实例化；全部内部码归 10 |
| 8 | Base/margin；实际 Path、Alphabet、Word 单子、old/generator/probe 图、呈现与大小界；共享 Gate、完整 Word 保守传输已有原核证书。Path old/probe 方程与完整保守性已验收；实际 Word 扩张及三项代数性质已构造；初始 probe 全 Word profile 已验收；old gates 和同一实际后继扩张对所有旧 profile 的保持已验收；实际模拟的任意内部目标单子 pushout 已验收；所有字母的内部 floor 图及上下界已验收；本批在原旧点界合同下推导锥内／锥外 cost 界并构造实际和切割，正式验收见下文 | Probe 的 margin 与完整装配接口及 Merger 扩张、margin 延拓、Placement、ConservativeHull、最终饱和单子 |
| 9 | Models 固定源码已有 | SVC、ACwo、同一系统商单射和非选择见证的目标端迁移未完成 |
| 10 | 原 Main 链与内部 Con 合同固定；底座通用 Proof/Sat 已有 | 全秩 PP/Main 装配、ZF/U 特化、全部内部矛盾证明码归约与最终闭句 |
| 11 | 现有验收工具可复用 | 最终主定理验收未开始 |

目标保持纯成员／等词语言、完整 nativeZF 和原 FirstOrder.Derives：`Derives nativeZF [] (Con_ZF → Con_U)`，U = ZF + PP + ACwo + ¬AC。Con 的量词覆盖所有内部证明码，包括外部看来非标准的码；这里的蕴含是对象公式，不是 Lean 函数类型。当前底座 ZFC 特化的证明／满足关系配套需要 ZF/U 适配，不重建通用核或 Sat。

## 阶段误判的纠正

已重新回读最初 f28b0334 的 1–11 流程。历史批次名、CheckStep4、构建数量及辅助声明数量均不能作为原阶段完成的证据。阶段 8 的局部对象证书已成立，不等于整个构造核心或最终一致性证明成立；不得据此称为收尾或给完成百分比。

此前将供体已有数学、旧版接口适配和最终系统实例化混为同一个缺口，造成重复规划；又将局部验收成功外推到整体进度，造成结果误判。以后每项剩余义务必须对应固定 OpenAI 源声明及实际消费者，并先查 REUSE_CONTRACTS 的现成入口。原阶段完成只按最初验收门确认，不能靠新增辅助模块数量推进编号。

## 本批实际源迁移

固定源 Algebra/ProbeMargins.lean 的 Path.letter_inside_cost:72、target_outside_cost:88；直接用于 exists_letter_interval:117 与 heightIntervals:144，最终供 extensionHeightCost:573 → MonoidBase.ProbeData.extension.margin:185 使用。

ConstructionProbeCostBoundsSyntax.construction_kernel_certificate 是原 FirstOrder.Derives nativeZF [] 中的纯成员／等词闭句：构造同一实际 floor 图，并为每个适用的内部锥内／锥外实例构造实际和切割，证明所需的包含界。锥内沿源证明取旧条件并，利用锥的并闭包及旧点界；锥外用 floor 的精确高度像并表示，把各旧高度的点界传至整个 floor，单位分支补齐 cost 本身的界。

加法直接消费已验收的分数 Sum、次序及其平移严格单调性，用原生 Separation 构造下闭包；两个操作数分支保留零切割情形。有界和的 Cut、圆整性及唯一性已证明，AddBound 与实际和切割包含关系的双向等价已证明。没有新增选择、递归、编码或证明核。

保留旧 HeightOrder、cost 函数图和 PointBound 输入；PointBound 是原旧 HeightCost.point_margin 的非严格加法后果，当前尚未从完整的具体旧 HeightCost 实例消去。初始 Base 的完整 margin、主切割加法和严格 cut_gap 已在 ConstructionBaseHeightGap / ConstructionPrincipalAddition 中完成；这里只缺到本批一般切割加法关系的适配，不把既有 Base margin 重新列为待证。源单子／作用／target／ConeLaws／条件并也保持为已证接口合同。因而本批不能记成实际旧 HeightCost 已实例化，不能记成 strict uniform margin、letter intervals 或完整后继 margin 已完成。状态分别记录为 false。

## 真实剩余及本轮复审

原 Word 条件并、实际三性质扩张、初始完整 profile、probe old gates、后继 profile 保持、pushout、letterFloor 图及上下界均不再列为待重证数学；本批从旧 PointBound 推导的两个 cost 界也不重证。下一条必要源依赖是 Algebra/ProbeMargins.lean 的 Path.extensionHeightCost:573 与 extension_old_cost_supremum:584，供 MonoidBase.ProbeData.extension.margin:185 和 inclusion.supremum:196 使用；letterFloor 与条件式 inside/outside cost 界已接通，下一步补实际旧 HeightCost 的 PointBound／严格统一间隙实例及 exists_letter_interval；随后接实际 Raw/Word height、cost 和旧 cost 上确界保持。复用已有切割／上确界、函数图、Raw 递归和 Gate，不另造完整实数或递归底座。随后是完整 Probe 装配、Merger 实际扩张与专用 gates/profile 保持、Placement、ConservativeHull 和最终饱和单子。第 6 阶段适配、第 9–11 阶段及全部内部码 Con 未完成。

此前复审重新回读了最初 f28b0334 的 1–11 表及新版 YesMetaZFC 7979336 的 Model/Choice 正文并核对当前版本及干净工作树，确认任意模型 L→ZF/ZFC、全分离／收集已经存在，供体工作树干净；没有重跑供体构建或修改版本。BMS 式 ModelTransfer 已在当前库实际消费，函数图／递归／Proof/Sat 已有。不恢复 NatPacket、泛滤真值或独立 L 重建。

此前误判来自把局部验收当整体推进、把已有供体数学与未接接口混为一谈，以及将可选字节兼容支线当作主定理义务；不是对象层目标后来改变。135 个孤立 Packet 模块已有可恢复退役记录；仍被保留证明依赖的 291 个不凭文件名前缀删除。本轮不增加持久脚本或新一套阶段编号。

## 实际验收

定向构建退出 0（634 项任务），原核证书及全部 40 项新声明的 --trust=0 预审退出 0。原核证书依赖既有 25 项；逐项与上一份完整验收足迹比较，没有新增可信依赖。正式 scripts/verify.py 已退出 0：2890 项构建、29461 项声明（937 项无公理依赖、28524 项有已记录依赖），9 条命令全部退出 0，其中 5 次 --trust=0，零警告。75 份主链源文件哈希全部匹配，2450 份受验文件哈希与当前内容一致，包含已校正的 target_outside_cost 声明行号 88。完整日志为 verification/construction-probe-cost-bounds-full-verification.log；commands.json / summary.json 对应本批正式入口。

编译全部退出后仅删除由正式 Audit 覆盖的重复预审输入，成功构建／预审／全量验收日志保留；清理记录见 verification/cleanup-probe-cost-bounds-20261027.json。没有遗留 Lean/Lake 进程，无需终止进程。

本批不上传、不新增持久脚本；完整后继 margin、最终对象 Con 均未完成，当前仍在原第 8 阶段。
