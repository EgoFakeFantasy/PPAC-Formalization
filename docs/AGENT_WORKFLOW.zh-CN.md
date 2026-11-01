# 原 1–11 阶段迁移流程（2026-11-01）

## 当前执行入口：原 App 公式和关系图应用已刻画 → 图函数／双射消费者

`88db176` 已验收实际关系图的 HS／支撑、强迫成员密集刻画及有序对成员刻画。本批 `ForcingPairFormula` 直接迁移固定源 `OrbitNames.forces_unorderedPair/forces_orderedPair/app_iff_mem_opair`，在同一实际全秩 HS 域内证明原纯集合语言的有序对公式和 `edge`／`App` 公式刻画；实际中间配对名字由原有配对构造和 HS 闭包提供。

`ForcingRelationGraphApplication` 显式证明动作公式重新索引不改变原 stabilizer／HS 定义，然后组合已有密集图刻画，取得原 `TailGraphs.BinaryRelation.app_graph`：图应用等价于两个有界成员条件和关系成立。三个完整对象闭句均返回原 `FirstOrder.Derives nativeZF`。全量验收通过：3178 jobs、36952 项声明、2733 文件哈希；36936 项旧依赖指纹不变，16 项新增声明，9 条命令（5 条 trust=0）退出 0，零警告，无新增公理依赖。报告：verification/graph-application-acceptance.json。

**仍在原第 8 阶段。** 真正未完：完整 `graph_functionOn/mapsTo/surjection/injection`、具体 Assigned 关系 bounds/move/one/inj/total/onto 与父输入实例化、assignmentGraph_bijection、具体商双射及同一最终父输入装配。下一步严格保留源 functionOn 中排除非有序对和域外条目的合取，消费已证明 mem_graph、forces_orderedPair、app_graph，以及既有 force_all/imp/ex/rename；不以外部函数代替内部图。L 解释、完整公理模式、完整 16 函数族、Assigned 兼容性以及本批 App 桥接均不重做。第 9–11 阶段、最终内部 Con 和原 Comparator 仍未完成。

| 阶段 | 原任务与输入 | 已有实际成果 | 真正还需要完成／验收门 |
|---|---|---|---|
| 1 | 语言桥接 | SourceSyntax、SourceStatements、Translation、Contract；全八构造器、首末 binder 及原核连线已验收 | 已完成，保留；不重做 |
| 2 | 句法与源推导传输 | 重命名、替换、有限支撑、19 规则及反向编译，原核 Derives 证书 | 已完成外部证书迁移；内部任意码归约归阶段 10，不回滚本项 |
| 3 | 全理论对应 | 完整 Separation/Replacement ↔ 原 Separation/Collection，全部固定公理、两种 AC；ZF/U 双向回放 | 已完成；不得把完整模式再报成未证明 |
| 4 | 原 Lean 4.34.1 外部基线 | 固定源 78 份副本哈希全部匹配；原 Main 完整构建 8998 任务通过；五个关键端点以 --trust=0 审计通过，仅标准三项依赖 | 完整 Comparator 仍未运行，缺 Linux/landrun；本仓 CheckStep4 不是此验收。原 4.34.1 环境与目标 4.33.1 保持隔离 |
| 5 | 内部名字、图、元组、递归 | 对象配对／图／ω／序列／内部递归、Def 与历史接口已验收；原 Child 归纳、IsName、evaluate、mapConditions 及作用律已验收；checkName、pairName、unionName 的精确构造、求值及条件作用均已验收 | 本基础名字包不再列为待做；实际统一条件／群作用、HS 实例及强迫公式解释也已接通。真正剩余消费者为 8–10 的最终具体单子及模型装配；不重造现成基础或重启字节兼容 |
| 6 | 背景、解释、universe | 供体完整 L/ZFC 已在固定旧版复用；原生与源语言逐公理／全模式、Choice、全局序及非空原核证书齐备。ConstructibleSource 逐点域对应、源 binder 对应、解释背景和非空前提实际消去，既有 InterpretedZF 已被真实消费 | 原 f28b033 第 6 行固定背景／universe、逐实例 Derives、不加不可达的验收门已完成；不再列作待做。全部内部／非标准 Proof/Con 归 10，不重证 L 或增加 GCH |
| 7 | 源强迫前端 | 原子／公式／固定证明保真、实际作用／正规滤子、全秩 HS、七条固定公理与完整 Separation／Replacement 已验收；已接通原 forces_ZF，逐源公理／模式有原核证书 | 前端合同已闭合，保留原单子／呈现／正规滤子前提；第 8 阶段提供具体构造。全部内部公式／证明码归约仍属 10；不能把此逐实例证书说成最终内部 Con |
| 8 | 源代数／构造核心 | 同一 Base/T、饱和终行及理想/基数；实际 System、纤维/粘合、标签/传输、持久选择、rank/type、CodeLinks；Preliminary 定律与实际全量词密集总性/满射性、实际索引图及对齐、cell/attachment 下降门、内部有限下降定理、推送粘合/消去、实际比较与换元、两类 cell 参数原像、两类生成性、实际普通闭包、有限旧系数、Attachment 传输、实际参数集／可数性、单 attachment 可数依赖图／保留词消费、内部首次出现索引、选中阶段计数及精确阶段像／保守范围、固定内轮记录函数族、实际依赖索引良序、全阶段cut后继及无前驱传输、统一实际阶段图与完整 Timeline；秩与表已构造；固定内部 cell 族、同一 V 上的全局依赖函数、可数性及精确活动行已验收；统一 conditionSelector／Selected、具体 component_selector_dense、StableAt 定义及双向置换、corrected_stable 已验收；corrected_total 已验收；corrected_onto 已验收；OrbitAssignment 定义、RootGroup 等价及 orbit/label/mono/restrict/permute/congr/descend/stable/eq_iff 已验收；完整轨道等价／全商／投影与代表函数、orbit_rep、统一 orbitChain、全量词 orbitAssignment_total_at／onto_at、orbitAssignment_index、全根群计数归约及实际代表链 total/onto、Assigned 公式/同轨道归约及固定参数族下 eq_iff/total/onto、label/mono/permute/restrict/stable、实际代码数据、选择器呈现、全轨道商统一记录函数及完整 16 字段函数族，以及实际 Assigned 理想、标签顶点/箭头和 at_extension 已验收；两条兼容性、GraphWitness/GraphHolds 关系定律及实际条目函数图已全量验收；有序对强迫相等及 raw 关系名字构造已全量验收 | 实际赋值图及 assignmentGraph_bijection；实际父输入统一、局部列表消费者及具体商双射 |
| 9 | 源模型应用 | Models 27 文件已锁定，尚未完成目标端迁移 | 接同一系统的 SVC、ACwo、全局商编码单射、非选择见证；不得只证局部／定秩替代物 |
| 10 | 原 Main 全局装配与对象内部化 | 原 Main 证明链及最终对象 Con 合同已固定；专用内部检查器尚未闭合 | 接原 reverse_injection_dense→forces_PP→forces_target；复用底座证明图实例化 ZF/U，再在 ZF 内证明全部内部矛盾证明码的归约与最终 Con 蕴含 |
| 11 | 终验与发布评审 | 现有审计工具可复用；最终验收未开始 | 核对源到目标对应、命题量词、依赖及原核主句；发布另按用户授权，不把辅助构建通过当最终通过 |

## Agent 执行入口

| 顺序 | 固定源消费者 | 复用输入 | 验收门 |
|---|---|---|---|
| 8 已完成 | ConcreteSystem.Vertex.permute/Arrow.move/Common.move；QuotientTransport.ReindexIso.gluedEquiv_toGlued:252–293 | 原图置换、完整顶点/箭头/Common、实际纤维限制图、实际整个分量商与 toGlued 交换律均已消费 | 两个普通 nativeZF 原核端点；全量验收见本批报告。未宣称整个 RootGroup 的单位/复合作用律已迁移 |
| 8 已完成 | QuotientTransport.eligibleSystemTransport:309–337 | 已有逐图 assemble_app、Data 唯一性和原生函数构造器；两侧已有对象/限制族 | ForcingEligibleReindex.construction_kernel_certificate 同时构造全 app 函数并证明 Apps/Natural；不再列作待做 |
| 8 已完成 | QuotientTransport.rebaseGlued/componentEquiv:353–421 | 现有 Common 传递性、同一商集/投影、全分量传输及自然性 | ForcingComponentRebase.construction_kernel_certificate 将目标换回原根，保留同一双射图；原组件稳定条件显式保留 |
| 8 当前 | ConcreteQuotients.component_selector_dense → actual selector → OrbitAssignments → AssignedGraphs.assignmentGraph_bijection → ConcreteQuotients.quotient_bijection_above | 同一固定 cell／全局 dependencies_at、实际阶段闭包、完整 restrict_selected、有向并集／unionLift 和完整 Square.union 已验收 | 完整 future_cut 与实际 future/reordered 已取得原核证书：现成逆同态、推送消去与实际顶点均被消费；现成可数 hull 已接入 countable_reordering，实际索引有限下降已取得原核证书；alignment 消费与全商可数编码已接通；具体初始底/flattening 消费及 countable_germs 已接通；实际尾探测函数及完整可数坐标集已接通；不同 coset 的 detector_separates 已取得原核证书；实际 fill、Complete 覆盖扩张和 countable_fusion 已取得原核证书；实际标签对稠密要求、统一严格比特界与同一 Complete 条件已接通；实际 rows／Eventual 商与 rawPattern 函数已构造；rawPattern_congr、pattern 下降、bounded-pattern 单射性和具体 good_dense 已完成；Complete.pattern_eq／置换保持、Good.mono 与 rawPattern_moveRows 已完成；整个 germ 商左乘、pattern_covariance、distinguishes_moveRows_iff 和 Good.permute 已接通；内部 leastBound、Complete 最小界和扩张／置换稳定性已接通；bestCoset 最小值／区分界唯一性／协变与共同固定 pattern 顺序已接通；统一 conditionSelector／Selected 的完整函数图及六项定律已接通；具体 component_selector_dense 与实际置换协变已从同一终行接通；Corrected 定义及 selected／common／mono／restrict／congr／eq_iff／permute／descend、StableAt 及 corrected_stable／total／onto 均已验收；OrbitAssignment 定义、RootGroup 等价及 orbit／label／mono／restrict／permute／congr／descend／stable／eq_iff、完整轨道商／投影、代表函数、统一 orbitChain、total_at／onto_at、实际轨道索引、全根群计数归约及实际代表链密集性已验收，Assigned 公式、同轨道归约及 eq_iff/total/onto 已验收；五条主线 Assigned 定律现已验收；实际逐轨道代码数据、固定呈现选择器、全轨道商统一记录函数及完整 16 字段函数族已验收；实际 Assigned 理想、标签顶点/箭头及 at_extension 已验收；两条兼容性已验收；本批 GraphWitness/GraphHolds 关系定律、有序对名字及实际条目函数图已全量验收；本批进一步取得有序对强迫相等刻画、保留两条成员测试的实际 raw 关系名字构造及精确条目方程；test 置换/HS 支撑已完成全量原核验收；强迫图成员与有序对成员刻画已取得原核证书；原 App 公式与实际图应用刻画已取得原核证书；下一项为完整图函数/双射消费者、具体 Assigned 图双射与父输入/记录见证对齐。保留同一终端单子与精确生成子幺半群 |
| 9 | Models／具体 ProductNames | 同一具体系统、全秩 HS／正规滤子／强迫前端 | SVC、ACwo、全局商编码单射、¬AC，保留源全部量词 |
| 10 | PP／Main 和内部矛盾码归约 | 源反向单射链；底座 ObjectProofNode/ReducedProofPresentation/PureProvability/Sat | ZF/U 全模式专用公理检查、全部内部/非标准证明码的正确性及原核内部 Con 蕴含 |
| 11 | 最终交付 | scripts/verify.py、源锁/足迹/原核端点 | 最终主句、完整理论/语言/背景核查及干净检出复现；当前本地验收不替代终验 |
| 4 独立未验项 | 原 Comparator | 隔离原 Lean 4.34.1 的 Main 与五端点已通过 | Linux/landrun；本仓 CheckStep4 不是 Comparator |

源码与精确依赖由 SOURCE_LOCK、THEOREM_COVERAGE 保留。新辅助引理必须有当前源主线消费者；不恢复 Packet/reader、leastCode 或 classFiber_dense_lower 旁支，不重复完整 L、公理模式、递归、Proof/Sat、函数或商后端。无实际调用的 localName_of_raw 和顶点 quotient/zigzag API 不作为前置。发布仍须独立授权。

历史分批验收及已被后续完成的旧待办保留在 Git `6a0a3d0`；当前待办只以上表和页首执行入口为准。
