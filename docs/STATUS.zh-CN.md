# 当前状态：原 1–11 阶段

本批输入基点 `fb06cb4`。完整 Base margin、初始旧 margin/order 适配及实际 heightIntervals 三图均为既有成果。本批只补固定 ProbeMargins.rawHeight/rawCost 所需的一般非负乘法与 min，复用原生内部算术和集合构造。**连续完整验收到第 1–3 阶段；主开发仍在第 8 阶段，最终对象 Con 未证明，不是收尾。**

| 原阶段 | 已完成／已经存在 | 真正剩余 |
|---|---|---|
| 1 | 全八构造器、首末 binder 对应、语言桥与原核连线 | 原范围已验收，不重做 |
| 2 | 重命名、替换、有限支撑、19 条源规则及双向外部证书传输 | 原范围已验收；全部内部码归约归 10 |
| 3 | 完整 ZF 模式互导及两种 AC 对应 | 已验收，不再列为缺口 |
| 4 | 原 Main 的 8998 项构建和五端点审计有既有验收 | 完整 Comparator 未运行，缺 Linux/landrun；本轮未重跑原 4.34.1 环境 |
| 5 | 内部集合／图／ω／序列／递归、名字及作用／HS 基础已有 | 具体系统消费者归 8–10，不重建基础 |
| 6 | 新版 7979336 的任意 ZF 模型内部 L→ZF/ZFC 和完整模式已有；此前已核对版本及干净工作树，本批未重跑或修改供体 | 固定旧版、当前对象语言相对化与原核接口未接通；不是缺少 L 数学 |
| 7 | forces_ZF 固定公理和全部模式已有逐实例原核证书 | 仍保留源单子／Presentation／正规滤子前提，待具体系统实例化；全部内部码归 10 |
| 8 | 初始 Base 及严格 margin；内部 Path/Alphabet/Word、old/generator/probe 图、呈现、大小界、保守模拟、条件并、profile 保持、pushout；floor、条件式 cost 界、加法/max、正整数除法、/4 与四倍和恢复已有。一般加法结合律已有；一般差值精确加回／所有切割解唯一性、加法序反映／相消已有；逐字母区间及统一锥外 cost 界已有；规范旧成本上确界和实际 heightIntervals 三图已有；初始 Base 的旧 UniformMargins／HeightOrder 输入已消去；本批构造一般切割乘法实际函数图及基本单调／零／正性定律，min 的唯一实际值、界和正性也已接通 | 后继 Word height/cost/margin 和 Probe 装配；Merger、Placement、ConservativeHull、最终饱和单子 |
| 9 | Models 固定源码已有 | 同一系统中的全秩 SVC、ACwo、商单射和非选择见证尚未迁移完成 |
| 10 | 原 Main 链与内部 Con 合同固定；底座通用 Proof/Sat 已有 | 全秩 PP/Main 装配、ZF/U 特化、全部内部矛盾证明码归约与最终闭句 |
| 11 | 现有验收工具可复用 | 最终主定理验收未开始 |

目标保持纯成员／等词语言、完整 nativeZF 和原 FirstOrder.Derives：`Derives nativeZF [] (Con_ZF → Con_U)`，U = ZF + PP + ACwo + ¬AC。Con 覆盖所有内部证明码，包括外部看来非标准的码；蕴含是对象公式。现成 ZFC 特化 Proof/Sat 需要 ZF/U 适配，不另建通用核或 Sat。

## 本批实际源迁移

固定原源 `ProbeMargins.lean`：rawHeight:210 是 `offset + scale * rawHeight`；rawCost:216 是 `min (scale * rawCost) gateCap`；cost_bounds:257 使用乘积正性和 min 的正性／界。后续消费者仍是 heightCost:494、extensionHeightCost:573 和 extension_old_cost_supremum:584。

- ConstructionFractionProduct 用原生内部自然数乘法给出分数乘积，保留不同但等值的坐标码，证明总性、唯一性、交换和非负单调性。四因子换序直接复用原生结合律和现有 mul_swap；没有重建自然数算术。
- ConstructionCutProduct 用原生 Separation 构造实际乘积切割；原有 omitted-bound 与分数单调性证明任意两个切割的乘积仍 proper，不保留待求乘积的界作为假设。通过既有可定义函数构造器取得实际 R×R 载体、MapsTo 及精确图。交换、单调、零吸收和非空乘积正性在同一图上成立。
- ConstructionCutMinimum 直接复用现有 cuts_total，构造字面交集；值等于一个输入，唯一、低于两者，两个非空输入给非空输出。没有再造序或完备性基础。
- ConstructionWordArithmeticSyntax.construction_kernel_certificate 返回纯成员语言的原 `FirstOrder.Derives nativeZF [] …`：在内部 Omega 与精确分数／切割载体下，构造上述实际乘法图、定律及所有 min 实例。ModelTransfer 仍用既有所有对应模型的回传，不取单个外部模型作替代。

**本批不是完整 Word 递归或后继 margin 的验收。** 一般乘法的单位、结合／分配及进一步严格比较须按原 Word 消费者接入；不因基本乘法已构造就把全部实数运算或 HeightCost 标为完成。原 Base 数值估计、原切割加法／差／除法、完整模式、内部递归、Proof/Sat 和已有 L 数学均不重做。

本批 60 项声明的定向严格构建和 --trust=0 预审均退出 0。新对象终点继承已有 25 项依赖，没有新增可信依赖。正式 scripts/verify.py 已退出 0：2918 项构建、29780 项声明（956 项无公理依赖、28824 项有已记录依赖），九条命令全部退出 0，其中五次 --trust=0，零警告。2478 份当前受验文件指纹和 75 份固定主链源哈希全部匹配。日志：verification/word-arithmetic-full-verification.log。没有新增持久生成脚本。

## 当前必要顺序与停止项

按固定源继续：依原 Raw.rawHeight／rawCost 公式接实际 Word height/cost、严格 margin 和旧 cost 上确界保持 → 完整 Probe → Merger → Placement／ConservativeHull → 最终单子。再与第 6 阶段接口、第 9 阶段模型应用和第 10 阶段全部内部证明码归约汇合。

初始 Base、其旧 margin／order 适配、heightIntervals 三图、差值与加法定律均不再列作缺口。scale×height／scale×cost 与 min 的实际内部值／图本批已构造；自然数缩放也保持既有状态。下一步直接消费这些运算和已有 Raw 递归接口，按原公式构造同一 Word 的 height/cost，再迁移实际消费的运算律及严格 margin／旧成本上确界保持，不扩建无消费者的完整实数域。

停止：NatPacket／reader 兼容、泛滤 atomic_truth 支线、独立 L 重建、当前消费者不需要的完整实数域。工作树清理按精确依赖闭包执行；已证明不等于主线需要，未找到接口也不等于数学不存在。

## 本轮清理复审与执行边界

此前“291 个 Packet 模块仍被其他证明引用，所以保留”的结论不够完整。反向追踪发现，这 291 个模块只牵连 67 个同属冻结兼容支线的内部消费者；总共 358 个模块，没有其他保留证明模块 import 它们。对应 14 个专用检查函数、263 个重复测试、3219 项专用声明审计及 19 项兼容状态输出也列入同一退役提案。通用保留源码编译、完整声明审计、原核 trust=0 及最终 Con 验收门均保留。

**该批量删除被自动审批拒绝，尚未执行。** 拒绝理由是删除范围大、涉及验证脚本／审计调整，当前授权未明确覆盖这份具体清单。现已完成逐文件哈希、358 份源码及原检查文件的 ZIP 归档校验，并生成完整拟议 patch；拟议 verifier 已通过 Python AST 解析，剩余源码指向候选模块的 import 为 0。这是静态方案检查，不是删除后编译验收。

精确方案：verification/retired-packet-closure-review.json；归档：同名 .zip；拟议差异：同名 .patch。恢复基点为 7828bfe。待用户批准这份具体清单后执行并重新全量验收；不通过另一条命令绕过审批。

本轮只删除已由正式 Audit 覆盖的本轮重复预审输入，成功构建／预审／全量验收日志全部保留，本批清单见 verification/cleanup-word-arithmetic-20261027.json。没有残留 Lean/Lake 编译进程；没有终止其他项目或应用进程。Agent 广场本轮连接拒绝，未写入其数据文件；需要使用时可双击 C:/Users/17857/AgentPlaza/启动广场.bat。


本批收尾进程复核：全量验收句柄已明确退出 0，复核时没有 Lean/Lake 进程。此前其他 BTBMS 工程的编译未被干预。358 项退役提案的 patch 在新主线改动后只读检查仍可应用，但依然未执行。
