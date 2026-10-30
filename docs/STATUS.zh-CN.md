# 当前状态：原 1–11 阶段（2026-10-30）

## 当前执行入口：Merger 的实际模拟推送

ConstructionMergerPushout 已迁移固定源 MergerPushouts.roots_satisfy/map_roots_satisfy/satisfies_map_iff/mergerSimulation_pushout。它先调用现有生产者构造映射处方及两侧完整 Merger，再构造实际诱导同态、证明旧系数／根方程和 ConservativeExtensions.mergerSimulation_snoc 的字面方程，最后证明任意内部目标单子上的完整推送通用性质。

24 个输出集合／图均在纯成员闭句内部存在量化；原核端点为 nativeZF 的 FirstOrder.Derives。没有把呈现或推送当前提，没有限制外部标准字长，也未新增目标保守性或 conical 前提。复用现有 Copies、单子乘法、旧嵌入、根、处方映射、presentedLift 和图复合；不重建基础后端。

本批全量验收：3045 项构建、34651 项声明、9 条命令／5 次 trust=0、零警告；34627 项旧声明依赖保持，2600 项文件哈希匹配，无新增公理依赖。见 verification/merger-pushout-acceptance.json。

下一实际源消费者是 ConservativeCells 的保守态射包装、生成性与有限旧系数。这里须严格区分：本批已经证明模拟的同态、字面方程和推送；ConservativeCells.simulation 另要求 mergerSimulation_conservative 的四项条件。当前检索定位到的显式 transport_conservative 是 Probe 专用，不能当作 Merger 已接入，也不能以推送代替。继续先核对现成因子／共下界接口并适配固定源的对应传输，再接 CellCuts 选中后继像识别与 CellReorder。此前已有的 Merger 旧嵌入保守性、锥、根和处方映射保留复用。

**仍在原第 8 阶段。Merger 实际呈现与推送已完成；模拟保守态射包装、生成性／有限旧系数、选中后继、可数重排、完整 germ/selector 与赋值商双射，以及第 9–11 阶段和最终内部 Con 仍未完成。** 已有 L、全公理模式、闭包、推导核、Probe 完整模拟／推送、两类参数原像、有限下降及对齐不再列为待做。

固定源 OpenAI 1581d4cbdd69a0faf34b2089614fe2a814316a6a；活动 YesMetaZFC 039c8e132cc19671d73a3933c66b4799d2599dd6；供体 79793365c2145c53db37eaf8ab23a64826bd9738。三者干净，均未修改。

| 原阶段 | 已完成 | 真实未完项 |
|---|---|---|
| 1 语言桥接 | 全构造子、binder、语义与原核连线 | 无 |
| 2 源推导传输 | 重命名／替换、19 规则、有限支撑及反向编译 | 标准证书部分已完成；全部内部码归 10 |
| 3 全理论对应 | ZF 全模式、Replacement/Collection、AC 双呈现、ZF/U 回放 | 无；不再重报完整模式缺失 |
| 4 原外部基线 | 隔离 Lean 4.34.1 原 Main 8998 构建、五端点 trust=0 | 原 Comparator 未运行，缺 Linux/landrun；CheckStep4 不是它 |
| 5 名字／图／递归基础 | 完整已验收基础包、实际条件／作用／HS 接线 | 后续同一具体系统消费者归 8–10 |
| 6 背景／解释／universe | 同一任意原生 ZF 模型内部完整 L/ZFC、原生与源全模式、Choice/order/非空、逐点域与解释背景实际消去 | 原范围已完成；内部 Proof/Con 归 10 |
| 7 强迫前端 | 固定 ZF 公理与全模式原核证书、实际作用／滤子／全秩 HS 合同 | 第 8 的最终具体系统实例化；全部内部码归 10 |
| 8 构造核心 | 同一 Base/T 与饱和终行、理想/基数；实际 System、纤维/粘合、标签与传输；Works/Selected、rank/type、CodeLinks、固定序数表及 Preliminary；实际 OrdinalCount、全部内部条件下的密集总性/满射性、链对齐与实际索引图、cell/attachment 下降门及内部有限下降定理、完整推送粘合/消去、实际比较与换元、两类 cell 参数原像 | 分量 germ/selector、OrbitAssignments、assignmentGraph_bijection；实际父输入统一、局部列表消费者及具体商双射 |
| 9 模型应用 | 源及条件前端已锁定 | 同一具体系统的 SVC、ACwo、全局商编码单射、¬AC |
| 10 PP/Main/内部 Con | 源 Main 链、Con 固定规格及底座通用 Proof/Sat 已有 | 全秩 PP/Main、ZF/U 专用内部检查、全部非标准矛盾码传输、最终闭句 |
| 11 终验 | 审计工具现成 | 最终主定理终验未开始 |

## 已验收前置

上一批 Same 协变及显式呈现下的表示传输已提交为 e1ea12c；验收记录为 verification/persistent-covariance-acceptance.json。本轮在其上实际生成全部逐条件输入，完成 Works/Selected 协变，见下文。

流程纠错：TailGraphs 的逐滤子 leastCode 仅通往 QuotientActions 的小写 preliminary 支线；最终 GermSelectors.Preliminary:38–47 使用持久 Selected 和 ordinalType/ordinalRank。此前把“模块被导入”误当“声明被主定理消费”，导致错误添加前置。未提交的 ForcingLeastCodes 草稿已归档删除，两项专用生产者改动已撤回；现有有效 At/Represents 证明保留。精确来源与裁决见 SOURCE_LOCK.selected_route_consumer_audit。

已批准的 358 模块、263 专用测试块和 3219 专用审计已于提交 53b5b17 退役并验收。本轮复核 358 路径全部不存在、无剩余 import，恢复 ZIP/补丁哈希均匹配。清单不会重复执行。

## 继续顺序与边界

| 顺序 | 固定源消费者 | 复用输入 | 验收门 |
|---|---|---|---|
| 8 已完成 | ConcreteSystem.Vertex.permute/Arrow.move/Common.move；QuotientTransport.ReindexIso.gluedEquiv_toGlued:252–293 | 原图置换、完整顶点/箭头/Common、实际纤维限制图、实际整个分量商与 toGlued 交换律均已消费 | 两个普通 nativeZF 原核端点；全量验收见本批报告。未宣称整个 RootGroup 的单位/复合作用律已迁移 |
| 8 已完成 | QuotientTransport.eligibleSystemTransport:309–337 | 已有逐图 assemble_app、Data 唯一性和原生函数构造器；两侧已有对象/限制族 | ForcingEligibleReindex.construction_kernel_certificate 同时构造全 app 函数并证明 Apps/Natural；不再列作待做 |
| 8 已完成 | QuotientTransport.rebaseGlued/componentEquiv:353–421 | 现有 Common 传递性、同一商集/投影、全分量传输及自然性 | ForcingComponentRebase.construction_kernel_certificate 将目标换回原根，保留同一双射图；原组件稳定条件显式保留 |
| 8 当前 | GermSelectors → OrbitAssignments → AssignedGraphs.assignmentGraph_bijection → ConcreteQuotients.quotient_bijection_above | 实际 OrdinalCount、全量词密集总性/满射性、Preliminary 相等/局部性/尾群协变已接通 | 核对并迁移分量 germ/selector 与赋值图消费者；实际 parent/list/outside 见证按源统一。不能把尾群协变冒称完整分量选择器 |
| 9 | Models／具体 ProductNames | 同一具体系统、全秩 HS／正规滤子／强迫前端 | SVC、ACwo、全局商编码单射、¬AC，保留源全部量词 |
| 10 | PP／Main 和内部矛盾码归约 | 源反向单射链；底座 ObjectProofNode/ReducedProofPresentation/PureProvability/Sat | ZF/U 全模式专用公理检查、全部内部/非标准证明码的正确性及原核内部 Con 蕴含 |
| 11 | 最终交付 | scripts/verify.py、源锁/足迹/原核端点 | 最终主句、完整理论/语言/背景核查及干净检出复现；当前本地验收不替代终验 |
| 4 独立未验项 | 原 Comparator | 隔离原 Lean 4.34.1 的 Main 与五端点已通过 | Linux/landrun；本仓 CheckStep4 不是 Comparator |

完整 Base/T、饱和、L/ZFC 全模式、内部递归、名字/函数/商后端、支撑下降和规范化均已完成且被复用，不再列作数学缺口。localName_of_raw 与未使用的顶点商图/zigzag API 没有当前真实调用，不增列前置；实际纤维粘合商已由本批完成。

最终目标仍是 Derives nativeZF [] (Con_ZF → Con_U)，其中 U=ZF+PP+ACwo+¬AC，Con 覆盖全部内部/非标准证明码。原第 4 阶段完整 Comparator 仍缺 Linux/landrun；原 Main 的 8998 构建和五端点通过不能替代它。第 11 阶段历史 304 个 CRLF/LF 文件的干净检出源码锁复现仍未验收，本批没有重写历史证明。

历史分批验收及已被后续完成的旧待办保留在 Git `6a0a3d0`；当前待办只以上表和页首执行入口为准。
