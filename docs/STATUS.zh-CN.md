# 当前状态：原 1–11 阶段

本批输入基点 `944a8b2`。原 heightIntervals、Base margin 接口和一般乘法／min 均为已有成果。本批按固定 rawHeight 公式构造实际 Word 高度图，直接复用现有 Raw evalHom、Word lift 和内部归纳，并证明完整图唯一性。**连续完整验收到第 1–3 阶段；主开发仍在第 8 阶段，最终对象 Con 未证明，不是收尾。**

| 原阶段 | 已完成／已经存在 | 真正剩余 |
|---|---|---|
| 1 | 全八构造器、首末 binder 对应、语言桥与原核连线 | 原范围已验收，不重做 |
| 2 | 重命名、替换、有限支撑、19 条源规则及双向外部证书传输 | 原范围已验收；全部内部码归约归 10 |
| 3 | 完整 ZF 模式互导及两种 AC 对应 | 已验收，不再列为缺口 |
| 4 | 原 Main 的 8998 项构建和五端点审计有既有验收 | 完整 Comparator 未运行，缺 Linux/landrun；本轮未重跑原 4.34.1 环境 |
| 5 | 内部集合／图／ω／序列／递归、名字及作用／HS 基础已有 | 具体系统消费者归 8–10，不重建基础 |
| 6 | 新版 7979336 的任意 ZF 模型内部 L→ZF/ZFC 和完整模式已有；此前已核对版本及干净工作树，本批未重跑或修改供体 | 固定旧版、当前对象语言相对化与原核接口未接通；不是缺少 L 数学 |
| 7 | forces_ZF 固定公理和全部模式已有逐实例原核证书 | 仍保留源单子／Presentation／正规滤子前提，待具体系统实例化；全部内部码归 10 |
| 8 | 初始 Base 及严格 margin；内部 Path/Alphabet/Word、old/generator/probe 图、呈现、大小界、保守模拟、条件并、profile 保持、pushout；floor、条件式 cost 界、加法/max、正整数除法、/4 与四倍和恢复已有。一般加法结合律已有；一般差值精确加回／所有切割解唯一性、加法序反映／相消已有；逐字母区间及统一锥外 cost 界已有；规范旧成本上确界和实际 heightIntervals 三图已有；初始 Base 的旧 UniformMargins／HeightOrder 输入已消去；一般切割乘法实际函数图及单调／零／正性定律、min 的唯一实际值／界／正性均已有；本批取得同一实际 Word 载体上的唯一高度图及原 old/cons 方程 | Word 高度界、实际成本图、严格后继 margin／旧成本上确界保持和 Probe 装配；Merger、Placement、ConservativeHull、最终饱和单子 |
| 9 | Models 固定源码已有 | 同一系统中的全秩 SVC、ACwo、商单射和非选择见证尚未迁移完成 |
| 10 | 原 Main 链与内部 Con 合同固定；底座通用 Proof/Sat 已有 | 全秩 PP/Main 装配、ZF/U 特化、全部内部矛盾证明码归约与最终闭句 |
| 11 | 现有验收工具可复用 | 最终主定理验收未开始 |

目标保持纯成员／等词语言、完整 nativeZF 和原 FirstOrder.Derives：`Derives nativeZF [] (Con_ZF → Con_U)`，U = ZF + PP + ACwo + ¬AC。Con 覆盖所有内部证明码，包括外部看来非标准的码；蕴含是对象公式。现成 ZFC 特化 Proof/Sat 需要 ZF/U 适配，不另建通用核或 Sat。

## 本批实际源迁移

固定原源 ProbeMargins.lean：rawHeight:210、height:220、height_old:223、height_cons:224；直接消费者是 height_bounds:239 及 heightCost:494。没有替换原高度公式。

- ConstructionProbeHeightOperation 直接消费已有一般切割乘积和加法，构造 `offset(s) + scale(s) × v` 的实际仿射运算。用原生函数构造器将它扩为总运算；在实际字母与切割输入上保留精确方程。
- ConstructionProbeHeightFold 取内部载体 `N = S ∪ R`，原生恒等图嵌入字母，直接调用未修改的 ConstructionProbeHomEvaluation 及 HomEvaluationSyntax.exists_lift_graph。这个现成求值器只需要总二元运算，不要求仿射运算满足结合、消去或单子律。
- 从现有求值历史的根步骤直接证明结果仍在 R，再将同一个实际 Word 图的值域细化到 R；没有把值域封闭当作假设。原 old 和 cons 方程在同一图上成立。
- 完整图的唯一性复用已有 HomExt.agreement 公式、Raw.raw_induction 和原生关系图外延性；覆盖所有内部有限长度，不用外部 Lean List 归纳代替。
- ConstructionProbeHeightFoldSyntax.construction_kernel_certificate 返回纯成员语言的原 `FirstOrder.Derives nativeZF [] …`。前提仅为 Omega／空零／零在 Omega、精确分数与切割载体、旧 H／字母 offset/scale 的实际 MapsTo 和实际 WordCarrier；结论构造唯一 W→R 高度图及原递归方程。没有预设高度图、递归历史、界或 HeightCost 字段。

**已完成的是实际 Word 高度图及其唯一递归方程。** height_bounds、实际 rawCost/cost 图、后继 margin 和旧成本上确界保持仍未完成；不能把本证书说成完整 HeightCost。成本还依赖当前词的 gateCap，不能仅把高度仿射式改名。

本批新增 31 项声明，定向严格构建和 --trust=0 预审均退出 0。新原核终点继承 31 项已存在的依赖；相较本工程既有可信基，没有新增依赖。现有 HomEvaluation／Raw 归纳模块未修改。正式 scripts/verify.py 已退出 0：2921 项构建，29811 项声明（956 项无公理依赖、28855 项有已记录依赖）；九条命令全部退出 0，其中五次 --trust=0，零警告。2481 份当前文件指纹和 75 份固定源哈希全部匹配。日志：verification/probe-height-fold-full-verification.log。没有新增持久生成脚本。

## 当前必要顺序与停止项

按固定源继续：实际 Word 高度图已有；接原 height_bounds、gateCap 和 rawCost/cost 图，再接严格 margin 与旧 cost 上确界保持 → 完整 Probe → Merger → Placement／ConservativeHull → 最终单子。再与第 6 阶段接口、第 9 阶段模型应用和第 10 阶段全部内部证明码归约汇合。

初始 Base、其旧 margin／order 适配、heightIntervals 三图、差值、加法及实际乘法／min 均已有；本批 Word 高度图和唯一 old/cons 方程也不再列作待构造。下一步接原高度界与词相关 gateCap／成本递归，仍复用现成函数图、序列求值和 gate/profile 接口，不复制通用递归后端。

停止：NatPacket／reader 兼容、泛滤 atomic_truth 支线、独立 L 重建、当前消费者不需要的完整实数域。工作树清理按精确依赖闭包执行；已证明不等于主线需要，未找到接口也不等于数学不存在。

## 本轮清理复审与执行边界

此前“291 个 Packet 模块仍被其他证明引用，所以保留”的结论不够完整。反向追踪发现，这 291 个模块只牵连 67 个同属冻结兼容支线的内部消费者；总共 358 个模块，没有其他保留证明模块 import 它们。对应 14 个专用检查函数、263 个重复测试、3219 项专用声明审计及 19 项兼容状态输出也列入同一退役提案。通用保留源码编译、完整声明审计、原核 trust=0 及最终 Con 验收门均保留。

**该批量删除被自动审批拒绝，尚未执行。** 拒绝理由是删除范围大、涉及验证脚本／审计调整，当前授权未明确覆盖这份具体清单。现已完成逐文件哈希、358 份源码及原检查文件的 ZIP 归档校验，并生成完整拟议 patch；拟议 verifier 已通过 Python AST 解析，剩余源码指向候选模块的 import 为 0。这是静态方案检查，不是删除后编译验收。

精确方案：verification/retired-packet-closure-review.json；归档：同名 .zip；拟议差异：同名 .patch。恢复基点为 7828bfe。待用户批准这份具体清单后执行并重新全量验收；不通过另一条命令绕过审批。

本轮只删除已由正式 Audit 覆盖的本轮重复预审输入，成功构建／预审／全量验收日志全部保留，本批清单见 verification/cleanup-probe-height-fold-20261027.json。没有残留 Lean/Lake 编译进程；没有终止其他项目或应用进程。Agent 广场本轮连接拒绝，未写入其数据文件；需要使用时可双击 C:/Users/17857/AgentPlaza/启动广场.bat。


本批收尾进程复核：全量验收句柄已明确退出 0，复核时没有 Lean/Lake 进程。此前其他 BTBMS 工程的编译未被干预。358 项退役提案的 patch 在新主线改动后只读检查仍可应用，但依然未执行。
