# 原 1–11 阶段迁移流程（2026-11-01）

## 当前执行入口：完整 restrict_selected 已验收 → CellReorder.future_cut／reordered

ConstructionCellRestriction 已将 Probe／Merger 两类实际原像、模拟及 work 接到同一固定 cell／Retained，取得完整原呈现的 Cell 和 Attachment 见证、实际内部逆、旧元素固定方程与精确范围。限制方块的四条包含均保留同态和保守性，并给出完整 IsPushout。

actual_stages 从同一保存的内轮 Trace、外层 Matrix 和终端 Row 复用 map_comp／range_closed，证明所有实际阶段的保守闭包；selected_actual 直接消费这些实际记录，阶段闭包不再是新增 oracle。四个普通 nativeZF 原核对象证书是 restrictCell、selected、actualStages、selectedActual；未添加新对象公理或重建底座。

本批完整验收：3080 项构建、35577 项声明、40 项新增声明、4 个普通 nativeZF 原核对象证书；9 条命令／5 次 trust=0，零警告。35537 项旧声明依赖全部不变，2635 项文件哈希、75 项固定源哈希匹配，无新增公理依赖。记录见 verification/cell-restriction-acceptance.json。

**仍在原第 8 阶段。** 统一 restrict_selected 与实际阶段闭包本批完成，不再列作待办。下一源消费者是 future_cut／reordered，随后为 germ-selector／OrbitAssignments／具体商双射。既有 identity、paste、cancel_left、map_apex、change_left 直接复用；不能因这些接口已有就声称 future_cut 的完整中间附件与极限并集装配已完成。第 9–11 阶段、全部内部／非标准证明码的最终 Con 蕴含及原 Comparator 仍未完成。

| 阶段 | 原任务与输入 | 已有实际成果 | 真正还需要完成／验收门 |
|---|---|---|---|
| 1 | 语言桥接 | SourceSyntax、SourceStatements、Translation、Contract；全八构造器、首末 binder 及原核连线已验收 | 已完成，保留；不重做 |
| 2 | 句法与源推导传输 | 重命名、替换、有限支撑、19 规则及反向编译，原核 Derives 证书 | 已完成外部证书迁移；内部任意码归约归阶段 10，不回滚本项 |
| 3 | 全理论对应 | 完整 Separation/Replacement ↔ 原 Separation/Collection，全部固定公理、两种 AC；ZF/U 双向回放 | 已完成；不得把完整模式再报成未证明 |
| 4 | 原 Lean 4.34.1 外部基线 | 固定源 78 份副本哈希全部匹配；原 Main 完整构建 8998 任务通过；五个关键端点以 --trust=0 审计通过，仅标准三项依赖 | 完整 Comparator 仍未运行，缺 Linux/landrun；本仓 CheckStep4 不是此验收。原 4.34.1 环境与目标 4.33.1 保持隔离 |
| 5 | 内部名字、图、元组、递归 | 对象配对／图／ω／序列／内部递归、Def 与历史接口已验收；原 Child 归纳、IsName、evaluate、mapConditions 及作用律已验收；checkName、pairName、unionName 的精确构造、求值及条件作用均已验收 | 本基础名字包不再列为待做；实际统一条件／群作用、HS 实例及强迫公式解释也已接通。真正剩余消费者为 8–10 的最终具体单子及模型装配；不重造现成基础或重启字节兼容 |
| 6 | 背景、解释、universe | 供体完整 L/ZFC 已在固定旧版复用；原生与源语言逐公理／全模式、Choice、全局序及非空原核证书齐备。ConstructibleSource 逐点域对应、源 binder 对应、解释背景和非空前提实际消去，既有 InterpretedZF 已被真实消费 | 原 f28b033 第 6 行固定背景／universe、逐实例 Derives、不加不可达的验收门已完成；不再列作待做。全部内部／非标准 Proof/Con 归 10，不重证 L 或增加 GCH |
| 7 | 源强迫前端 | 原子／公式／固定证明保真、实际作用／正规滤子、全秩 HS、七条固定公理与完整 Separation／Replacement 已验收；已接通原 forces_ZF，逐源公理／模式有原核证书 | 前端合同已闭合，保留原单子／呈现／正规滤子前提；第 8 阶段提供具体构造。全部内部公式／证明码归约仍属 10；不能把此逐实例证书说成最终内部 Con |
| 8 | 源代数／构造核心 | 同一 Base/T、饱和终行及理想/基数；实际 System、纤维/粘合、标签/传输、持久选择、rank/type、CodeLinks；Preliminary 定律与实际全量词密集总性/满射性、实际索引图及对齐、cell/attachment 下降门、内部有限下降定理、推送粘合/消去、实际比较与换元、两类 cell 参数原像、两类生成性、实际普通闭包、有限旧系数、Attachment 传输、实际参数集／可数性、单 attachment 可数依赖图／保留词消费、内部首次出现索引、选中阶段计数及精确阶段像／保守范围、固定内轮记录函数族、实际依赖索引良序、全阶段cut后继及无前驱传输、统一实际阶段图与完整 Timeline；秩与表已构造；固定内部 cell 族、同一 V 上的全局依赖函数、可数性及精确活动行已验收 | 完整 restrict_selected／实际阶段闭包已接通；继续 future_cut／重排 → germ-selector／OrbitAssignments／具体商双射；不重造已完成底座 |
| 9 | 源模型应用 | Models 27 文件已锁定，尚未完成目标端迁移 | 接同一系统的 SVC、ACwo、全局商编码单射、非选择见证；不得只证局部／定秩替代物 |
| 10 | 原 Main 全局装配与对象内部化 | 原 Main 证明链及最终对象 Con 合同已固定；专用内部检查器尚未闭合 | 接原 reverse_injection_dense→forces_PP→forces_target；复用底座证明图实例化 ZF/U，再在 ZF 内证明全部内部矛盾证明码的归约与最终 Con 蕴含 |
| 11 | 终验与发布评审 | 现有审计工具可复用；最终验收未开始 | 核对源到目标对应、命题量词、依赖及原核主句；发布另按用户授权，不把辅助构建通过当最终通过 |

## Agent 执行入口

| 顺序 | 固定源消费者 | 复用输入 | 验收门 |
|---|---|---|---|
| 8 已完成 | ConcreteSystem.Vertex.permute/Arrow.move/Common.move；QuotientTransport.ReindexIso.gluedEquiv_toGlued:252–293 | 原图置换、完整顶点/箭头/Common、实际纤维限制图、实际整个分量商与 toGlued 交换律均已消费 | 两个普通 nativeZF 原核端点；全量验收见本批报告。未宣称整个 RootGroup 的单位/复合作用律已迁移 |
| 8 已完成 | QuotientTransport.eligibleSystemTransport:309–337 | 已有逐图 assemble_app、Data 唯一性和原生函数构造器；两侧已有对象/限制族 | ForcingEligibleReindex.construction_kernel_certificate 同时构造全 app 函数并证明 Apps/Natural；不再列作待做 |
| 8 已完成 | QuotientTransport.rebaseGlued/componentEquiv:353–421 | 现有 Common 传递性、同一商集/投影、全分量传输及自然性 | ForcingComponentRebase.construction_kernel_certificate 将目标换回原根，保留同一双射图；原组件稳定条件显式保留 |
| 8 当前 | CellReorder.future_cut/reordered → GermSelectors → OrbitAssignments → AssignedGraphs.assignmentGraph_bijection → ConcreteQuotients.quotient_bijection_above | 同一固定 cell／全局 dependencies_at、实际阶段闭包和完整 restrict_selected 已验收 | 按原 future_cut 的基点／选中后继／遗漏后继／极限分支接入现成证明；再接 reordered。保留同一终端单子和精确生成子幺半群，不扩大为任意保守闭包 |
| 9 | Models／具体 ProductNames | 同一具体系统、全秩 HS／正规滤子／强迫前端 | SVC、ACwo、全局商编码单射、¬AC，保留源全部量词 |
| 10 | PP／Main 和内部矛盾码归约 | 源反向单射链；底座 ObjectProofNode/ReducedProofPresentation/PureProvability/Sat | ZF/U 全模式专用公理检查、全部内部/非标准证明码的正确性及原核内部 Con 蕴含 |
| 11 | 最终交付 | scripts/verify.py、源锁/足迹/原核端点 | 最终主句、完整理论/语言/背景核查及干净检出复现；当前本地验收不替代终验 |
| 4 独立未验项 | 原 Comparator | 隔离原 Lean 4.34.1 的 Main 与五端点已通过 | Linux/landrun；本仓 CheckStep4 不是 Comparator |

源码与精确依赖由 SOURCE_LOCK、THEOREM_COVERAGE 保留。新辅助引理必须有当前源主线消费者；不恢复 Packet/reader、leastCode 或 classFiber_dense_lower 旁支，不重复完整 L、公理模式、递归、Proof/Sat、函数或商后端。无实际调用的 localName_of_raw 和顶点 quotient/zigzag API 不作为前置。发布仍须独立授权。

历史分批验收及已被后续完成的旧待办保留在 Git `6a0a3d0`；当前待办只以上表和页首执行入口为准。
