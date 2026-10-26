# 当前状态：原 1–11 阶段

本批输入基点 `59b73ad`。实际 Word 高度图及唯一性已为既有成果。本批按固定 OldMinimum/gateCap 和 rawCost 公式构造同一 Word 的实际 cap／成本图、完整成本图唯一性及原正性／非严格上界；复用现有 Raw evalHom、Word lift 与内部归纳。**连续完整验收到第 1–3 阶段；主开发仍在第 8 阶段，最终对象 Con 未证明，不是收尾。**

| 原阶段 | 已完成／已经存在 | 真正剩余 |
|---|---|---|
| 1 | 全八构造器、首末 binder 对应、语言桥与原核连线 | 原范围已验收，不重做 |
| 2 | 重命名、替换、有限支撑、19 条源规则及双向外部证书传输 | 原范围已验收；全部内部码归约归 10 |
| 3 | 完整 ZF 模式互导及两种 AC 对应 | 已验收，不再列为缺口 |
| 4 | 原 Main 的 8998 项构建和五端点审计有既有验收 | 完整 Comparator 未运行，缺 Linux/landrun；本轮未重跑原 4.34.1 环境 |
| 5 | 内部集合／图／ω／序列／递归、名字及作用／HS 基础已有 | 具体系统消费者归 8–10，不重建基础 |
| 6 | 新版 7979336 的任意 ZF 模型内部 L→ZF/ZFC 和完整模式已有；此前已核对版本及干净工作树，本批未重跑或修改供体 | 固定旧版、当前对象语言相对化与原核接口未接通；不是缺少 L 数学 |
| 7 | forces_ZF 固定公理和全部模式已有逐实例原核证书 | 仍保留源单子／Presentation／正规滤子前提，待具体系统实例化；全部内部码归 10 |
| 8 | 初始 Base 及严格 margin；内部 Path/Alphabet/Word、old/generator/probe 图、呈现、大小界、保守模拟、条件并、profile 保持、pushout；floor、条件式 cost 界、加法/max、正整数除法、/4 与四倍和恢复已有。一般加法结合律已有；一般差值精确加回／所有切割解唯一性、加法序反映／相消已有；逐字母区间及统一锥外 cost 界已有；规范旧成本上确界和实际 heightIntervals 三图已有；初始 Base 的旧 UniformMargins／HeightOrder 输入已消去；一般切割乘法实际函数图及单调／零／正性定律、min 的唯一实际值／界／正性均已有；同一实际 Word 载体上的唯一高度图及原 old/cons 方程已有；本批完成实际 gateCap／唯一成本图及 cost_bounds | Word 高度界、cost_le_scale／旧因子成本等原估计、严格后继 margin／旧成本上确界保持和 Probe 装配；Merger、Placement、ConservativeHull、最终饱和单子 |
| 9 | Models 固定源码已有 | 同一系统中的全秩 SVC、ACwo、商单射和非选择见证尚未迁移完成 |
| 10 | 原 Main 链与内部 Con 合同固定；底座通用 Proof/Sat 已有 | 全秩 PP/Main 装配、ZF/U 特化、全部内部矛盾证明码归约与最终闭句 |
| 11 | 现有验收工具可复用 | 最终主定理验收未开始 |

目标保持纯成员／等词语言、完整 nativeZF 和原 FirstOrder.Derives：`Derives nativeZF [] (Con_ZF → Con_U)`，U = ZF + PP + ACwo + ¬AC。Con 覆盖所有内部证明码，包括外部看来非标准的码；蕴含是对象公式。现成 ZFC 特化 Proof/Sat 需要 ZF/U 适配，不另建通用核或 Sat。

## 本批实际源迁移

固定原源 ProbeMargins.lean：OldMinimum:172 / unique:175，gateCap:183 / pos:186 / le_one:193 / eq:200，rawCost:216 / cost:221 / cost_old:226 / cost_cons:227 / cost_bounds:257。

- ConstructionProbeGateCap 直接使用原生函数构造器及现有 OldGate 的精确旧倍数轮廓。旧单子的左消去／conical 给出元素整除反对称和 OldMinimum 唯一性；没有重证门的存在性。cap 的值严格为“最小旧右倍数 g 的实际 C(g)”，不存在最小元时才取源 unit，绝非任意更大旧倍数的成本。
- cap 实际函数图具有完整唯一性、默认分支、精确最小成本分支及正性／非严格上界。没有假设所有词均有 OldMinimum，没有引入对象选择函数。
- ConstructionProbeCostOperation 按原式构造 `min(scale(s) × suffixCost, cap(当前新词))`。内部状态是实际 `(word,cost)` 配对；总运算的默认值仅处理不会在有效 cons 方程中出现的输入。
- ConstructionProbeCostFold 直接复用现成 evalHom 和 Word lift；原生 Raw 公式归纳证明状态中的词恰为当前输入词，因此 cap 索引不会误落到字母或后缀。复用上批根步骤范围细化和原生函数构造取得实际 W→R 成本图。
- 同一图满足原 old/cons 成本方程；所有内部有限长度上的公式归纳给出整个成本图唯一性。正性来自既有乘积／min 正性，上界直接来自 min≤cap≤unit；只使用源 scale 正性，没有强化成额外的 scale 上界假设。
- GateCapSyntax 的原核对象证书构造 cap 本身；CostFoldSyntax 的原核对象证书同时构造实际 cap 和实际成本图，并返回成本方程、非空正性、非严格上界及图唯一性。不是“先假设 cap 或成本图再证明其性质”。

`unit` 是已有 Base 数据所供给的 1 切割；本证书对任何给定正 unit 上界都成立。现有构造已证明这个实际 unit 为主切割 1，不需重证。允许成本等于 unit，不能误用 Base 专有的严格 `<1` 代替源通用 `≤1`。

**实际 Word 高度图、cap、成本图和 cost_bounds 已有；完整 HeightCost 尚未完成。** 下一源义务仍包括 height_bounds、cost_le_scale／cost_old_factor 等实际消费的估计、严格后继 margin 与旧成本上确界保持，随后完整 Probe／Merger 等装配。最终内部 Con 未证明。

本批 89 项声明的定向严格构建和 --trust=0 预审均退出 0，零警告。两个新原核终点分别继承已有 10／31 项依赖，没有扩大本工程可信基。原 evalHom、Word lift、Raw 归纳及 HeightFold 范围细化均未修改。正式 scripts/verify.py 已退出 0：2926 项构建，29900 项声明（972 项无公理依赖、28928 项有已记录依赖）；九条命令全部退出 0，其中五次 --trust=0，零警告。2486 份当前文件指纹和 75 份固定源哈希全部匹配。日志：verification/probe-cost-fold-full-verification.log。没有新增持久生成脚本。

## 当前必要顺序与停止项

按固定源继续：接原 Word 高度界、cost_le_scale／成本旧因子等估计，再接严格 margin 与旧 cost 上确界保持 → 完整 Probe → Merger → Placement／ConservativeHull → 最终单子；再与第 6 阶段已有 L 的接口、第 9 阶段模型应用和第 10 阶段全部内部证明码归约汇合。

Base、其 margin／order 适配、heightIntervals 三图、所需已有切割算术、Word 高度图及本批 cap／成本图均不再列作待构造。先补原高度界与 cost_le_scale 共同消费的切割乘法单位法则；只有原消费者实际需要的运算律与估计进入下一步，不扩建完整实数域，也不重造递归／Proof／Sat 或已有 L 数学。


停止：NatPacket／reader 兼容、泛滤 atomic_truth 支线、独立 L 重建、当前消费者不需要的完整实数域。工作树清理按精确依赖闭包执行；已证明不等于主线需要，未找到接口也不等于数学不存在。

## 本轮清理复审与执行边界

此前“291 个 Packet 模块仍被其他证明引用，所以保留”的结论不够完整。反向追踪发现，这 291 个模块只牵连 67 个同属冻结兼容支线的内部消费者；总共 358 个模块，没有其他保留证明模块 import 它们。对应 14 个专用检查函数、263 个重复测试、3219 项专用声明审计及 19 项兼容状态输出也列入同一退役提案。通用保留源码编译、完整声明审计、原核 trust=0 及最终 Con 验收门均保留。

**该批量删除被自动审批拒绝，尚未执行。** 拒绝理由是删除范围大、涉及验证脚本／审计调整，当前授权未明确覆盖这份具体清单。现已完成逐文件哈希、358 份源码及原检查文件的 ZIP 归档校验，并生成完整拟议 patch；拟议 verifier 已通过 Python AST 解析，剩余源码指向候选模块的 import 为 0。这是静态方案检查，不是删除后编译验收。

精确方案：verification/retired-packet-closure-review.json；归档：同名 .zip；拟议差异：同名 .patch。恢复基点为 7828bfe。待用户批准这份具体清单后执行并重新全量验收；不通过另一条命令绕过审批。

本轮只删除已由正式 Audit 覆盖的本轮重复预审输入，成功构建／预审／全量验收日志全部保留，本批清单见 verification/cleanup-probe-cost-fold-20261027.json。没有残留 Lean/Lake 编译进程；没有终止其他项目或应用进程。Agent 广场本轮连接拒绝，未写入其数据文件；需要使用时可双击 C:/Users/17857/AgentPlaza/启动广场.bat。


本批收尾进程复核：全量验收句柄已明确退出 0，复核时没有 Lean/Lake 进程。此前其他 BTBMS 工程的编译未被干预。358 项退役提案的 patch 在新主线改动后只读检查仍可应用，但依然未执行。
