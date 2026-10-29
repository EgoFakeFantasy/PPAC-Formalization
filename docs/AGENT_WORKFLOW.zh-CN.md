# 原 1–11 阶段迁移流程（2026-10-29）

沿用最初 f28b0334a740108057adf18a24dc11abd866efbe 的阶段编号。旧批次验收叙述由 Git 和各验收报告保留，本表只列当前执行入口。

**仍在原第 8 阶段。实际 Same 协变已有普通 nativeZF 原核证书；完整 Works/Selected 全条件协变现已取得同一内部 L 相对化的 nativeZF 原核证书，全量验收已通过。稳定性产生同一个内部ω工作码现也已取得原核证书并通过全量验收；OrdinalCodes/CodeLinks、第 9–11 阶段及最终内部 Con 仍未完成。** 构建数和声明数不表示整体完成比例。

| 阶段 | 原任务与输入 | 已有实际成果 | 真正还需要完成／验收门 |
|---|---|---|---|
| 1 | 语言桥接 | SourceSyntax、SourceStatements、Translation、Contract；全八构造器、首末 binder 及原核连线已验收 | 已完成，保留；不重做 |
| 2 | 句法与源推导传输 | 重命名、替换、有限支撑、19 规则及反向编译，原核 Derives 证书 | 已完成外部证书迁移；内部任意码归约归阶段 10，不回滚本项 |
| 3 | 全理论对应 | 完整 Separation/Replacement ↔ 原 Separation/Collection，全部固定公理、两种 AC；ZF/U 双向回放 | 已完成；不得把完整模式再报成未证明 |
| 4 | 原 Lean 4.34.1 外部基线 | 固定源 78 份副本哈希全部匹配；原 Main 完整构建 8998 任务通过；五个关键端点以 --trust=0 审计通过，仅标准三项依赖 | 完整 Comparator 仍未运行，缺 Linux/landrun；本仓 CheckStep4 不是此验收。原 4.34.1 环境与目标 4.33.1 保持隔离 |
| 5 | 内部名字、图、元组、递归 | 对象配对／图／ω／序列／内部递归、Def 与历史接口已验收；原 Child 归纳、IsName、evaluate、mapConditions 及作用律已验收；checkName、pairName、unionName 的精确构造、求值及条件作用均已验收 | 本基础名字包不再列为待做；实际统一条件／群作用、HS 实例及强迫公式解释也已接通。真正剩余消费者为 8–10 的最终具体单子及模型装配；不重造现成基础或重启字节兼容 |
| 6 | 背景、解释、universe | 供体完整 L/ZFC 已在固定旧版复用；原生与源语言逐公理／全模式、Choice、全局序及非空原核证书齐备。ConstructibleSource 逐点域对应、源 binder 对应、解释背景和非空前提实际消去，既有 InterpretedZF 已被真实消费 | 原 f28b033 第 6 行固定背景／universe、逐实例 Derives、不加不可达的验收门已完成；不再列作待做。全部内部／非标准 Proof/Con 归 10，不重证 L 或增加 GCH |
| 7 | 源强迫前端 | 原子／公式／固定证明保真、实际作用／正规滤子、全秩 HS、七条固定公理与完整 Separation／Replacement 已验收；已接通原 forces_ZF，逐源公理／模式有原核证书 | 前端合同已闭合，保留原单子／呈现／正规滤子前提；第 8 阶段提供具体构造。全部内部公式／证明码归约仍属 10；不能把此逐实例证书说成最终内部 Con |
| 8 | 源代数／构造核心 | 完整Base/Probe/Merger、内部塔/覆盖/精确转移、全部理想/补集/基数端点、实际μ/K；同一完整乘法图上Base→ObjectFields已装配，所有几何父前提消去；同一实际最终T行及全部ObjectFields/饱和/基数性质均有原核对象证书 | 实际商集/投影/限制图及局部商限制单射/精确交集已接；资格谓词/反射/实际 Obj 已接；eligibleSystem 实际限制图、三条实际定律及资格交集已接；同一内部索引族及完整 System 统一装配已完成；实际 availability 已接；精确 Fiber/限制双射已接；Component 纤维族/箭头相容已完成；Matches 与实际 Glued/toGlued 已完成；同一实际最终 T 的标签系统/全部纤维及粘合基数、共同分量字面集合相等已完成，探针/基数前提已消去；不同系统的 availability/精确纤维重标号与实际标签 app 族已完成；移动顶点/整分量粘合已完成；实际移动滤子及局部相等保反射已完成；实际名字/商双射与限制方块已完成；资格类坐标传输和逐图实际 app 已完成；完整 app 函数族及自然性联合装配、At 双向传输及同码协变已完成；持久选择通用单调/唯一/稠密性已完成，实际 Same 已接入；逐条件 Works 与 Selected 特化已完成；Same 协变已完成；Works/Selected 全条件协变已通过全量验收；稳定工作码构造已完成；后续 OrdinalCodes/CodeLinks 消费者未完；Placement、Product descent、countable conservative hull 已完成；顶点/箭头/整个 Common 分量共尾链本批接入，不重做 Base/T 或底座 |
| 9 | 源模型应用 | Models 27 文件已锁定，尚未完成目标端迁移 | 接同一系统的 SVC、ACwo、全局商编码单射、非选择见证；不得只证局部／定秩替代物 |
| 10 | 原 Main 全局装配与对象内部化 | 原 Main 证明链及最终对象 Con 合同已固定；专用内部检查器尚未闭合 | 接原 reverse_injection_dense→forces_PP→forces_target；复用底座证明图实例化 ZF/U，再在 ZF 内证明全部内部矛盾证明码的归约与最终 Con 蕴含 |
| 11 | 终验与发布评审 | 现有审计工具可复用；最终验收未开始 | 核对源到目标对应、命题量词、依赖及原核主句；发布另按用户授权，不把辅助构建通过当最终通过 |

## Agent 执行入口

| 顺序 | 固定源消费者 | 复用输入 | 验收门 |
|---|---|---|---|
| 8 已完成 | ConcreteSystem.Vertex.permute/Arrow.move/Common.move；QuotientTransport.ReindexIso.gluedEquiv_toGlued:252–293 | 原图置换、完整顶点/箭头/Common、实际纤维限制图、实际整个分量商与 toGlued 交换律均已消费 | 两个普通 nativeZF 原核端点；全量验收见本批报告。未宣称整个 RootGroup 的单位/复合作用律已迁移 |
| 8 已完成 | QuotientTransport.eligibleSystemTransport:309–337 | 已有逐图 assemble_app、Data 唯一性和原生函数构造器；两侧已有对象/限制族 | ForcingEligibleReindex.construction_kernel_certificate 同时构造全 app 函数并证明 Apps/Natural；不再列作待做 |
| 8 已完成 | QuotientTransport.rebaseGlued/componentEquiv:353–421 | 现有 Common 传递性、同一商集/投影、全分量传输及自然性 | ForcingComponentRebase.construction_kernel_certificate 将目标换回原根，保留同一双射图；原组件稳定条件显式保留 |
| 8 当前 | TailGraphs → PersistentCodes → OrdinalCodes → CodeLinks | 共尾链、实际资格系统/纤维/粘合和全族传输已有；ChainCode/At/Represents、代表码存在/唯一性、原根 componentEquiv、At 保反射及同码协变均已接入 | 通用持久选择的单调/唯一/稠密性已取得原核证书；实际主滤子及 Same 定律/表示相等已接入；逐条件 Works 和实际 Selected 特化已接入；Same 协变已完成；Works/Selected 全条件协变已通过全量验收；主滤子 forcedAvailability 与实际 eligibleSystem 可用性及精确纤维桥接已取得原核证书并通过全量验收；exists_working_code_of_stable 的同一个内部ω链码在全部加强条件下的表示已取得原核证书并通过全量验收；其直接消费者为 CodeCardinals.ordinalType_lower_count:235，与后续 OrdinalCodes/CodeLinks 汇合。逐滤子 leastCode 不在最终消费者链上，取消其迁移前置地位；不重建名字/选择/L/商后端 |
| 9 | Models／具体 ProductNames | 同一具体系统、全秩 HS／正规滤子／强迫前端 | SVC、ACwo、全局商编码单射、¬AC，保留源全部量词 |
| 10 | PP／Main 和内部矛盾码归约 | 源反向单射链；底座 ObjectProofNode/ReducedProofPresentation/PureProvability/Sat | ZF/U 全模式专用公理检查、全部内部/非标准证明码的正确性及原核内部 Con 蕴含 |
| 11 | 最终交付 | scripts/verify.py、源锁/足迹/原核端点 | 最终主句、完整理论/语言/背景核查及干净检出复现；当前本地验收不替代终验 |
| 4 独立未验项 | 原 Comparator | 隔离原 Lean 4.34.1 的 Main 与五端点已通过 | Linux/landrun；本仓 CheckStep4 不是 Comparator |

本批 ReindexIso 的通用原核端点允许不同源/目标 System；实际标签端点进一步构造唯一 app 函数族并证明全部自然性。两个端点均为普通 nativeZF 推导；整分量 gluedEquiv_toGlued 已由本批原核端点完成；移动滤子 eligibleSystemTransport 的全 app 族与自然性现已由 ForcingEligibleReindex 接入，使用两侧实际对象/限制族；完整模型应用仍须按上表继续。源码与精确依赖由 SOURCE_LOCK、THEOREM_COVERAGE 保留。新的辅助引理必须有上表实际消费者；不恢复 Packet/reader，不重复完整 L/公理模式/递归/Proof/Sat/函数商后端。无当前调用的 localName_of_raw、顶点 quotient/zigzag API 不作为主线前置。发布仍须独立授权。

本轮 OrdinalCodes 入口：ForcingOrdinalRanks 已构造任意内部良序上的实际 rank 名字函数和同一 selectionType，保留精确前驱收集方程，并通过内部良序归纳证明全部 IsName；普通 nativeZF 原核证书及全量验收已通过（2970 构建、33320 声明、9 条命令／5 次 trust=0，原 33285 足迹不变）。接下来只需在这个 SAME 函数上接入现成 collect_HS/fixed 的内部归纳和源强迫定理；不得重做坍缩、递归、函数图、名字收集。HS/固定性及后续 CodeLinks 尚未完成，原阶段仍为 8。

本轮接续：ForcingOrdinalFixed 已将同一实际 rank 图和 selectionType 的 HS／共同 H 字面固定性接入普通 nativeZF 原核；全量验收通过（2971 构建、33341 声明、9 条命令／5 次 trust=0，原 33320 足迹不变）。下一项是固定源 mem_selectedRank/mem_selectionType，复用 mem_iff、edge_collected 和本批 rank_collected。随后按源链接传递性、OrdF 和 PersistentCodes.ordF_eq_check_le:521 的决定结论，再进入 CodeLinks；现成名字/HS/固定性/前驱集/内部归纳不得重建。阶段仍为 8。

本轮接续：ForcingOrdinalMembership 已接通源 79/94/102/108/115/124 六个成员／初段包含结论和三个普通 nativeZF 原核端点，全量验收通过：2972 项构建、33369 项声明，新增 28 项；全部 33341 项旧依赖足迹不变。9 条命令及 5 次 trust=0 检查均退出 0，零警告、无新增公理依赖；75 项固定源和 2527 项当前文件哈希一致。见 verification/ordinal-membership-acceptance.json。下一实际消费者是 transF_selectedRank/transF_selectionType → ordF_selectedRank/ordF_selectionType → 原 ordF_eq_check_le，再进入 CodeLinks；既有实际 rank、HS/固定性、成员方程及 SubsetF 不重做。OrdF 的源辅助性质不替代完整对象 ordinal 公式。原阶段仍为 8。
