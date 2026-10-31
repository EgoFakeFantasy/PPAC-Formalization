# 当前状态：原 1–11 阶段（2026-11-01）

## 当前执行入口：两类实际原像模拟与 work 已证明 → 固定 cell 的统一 restrict_selected 端点

ConstructionRestrictedCellSimulation 已构造 Probe／Merger 的实际原像完整呈现、到原固定呈现的保守模拟、生成性和完整推挤性质。原目标呈现是输入的同一对象，没有重选。Merger 的整个处方表映回原表；ConstructionStepCell 同步保留了已有 mapped graph 生产者证明的 WellFormed，避免把该条件转嫁给调用者。

ConstructionRestrictedCellPushout.work 已消费同一模拟与选中词，构造原后继和保留后继的乘法图、终端嵌入及两个内部逆，再实际调用已有 map_apex/change_left。其结果保留同一复合图、旧元素固定方程、精确范围、限制包含和完整 IsPushout 通用性质；普通子幺半群限制直接复用现有单位／结合律，不增加因子／并闭包前提。

本批完整验收：3079 项构建、35537 项声明、25 项新声明、3 个普通 nativeZF 原核对象证书；9 条命令／5 次 trust=0，零警告。35512 项旧声明依赖全部不变，2634 项文件哈希、75 项固定源哈希匹配，无新增公理依赖。记录见 verification/restricted-cell-acceptance.json。

**仍在原第 8 阶段。** 完整 restrict_selected 尚需将上述分支生产者和 work 接到同一固定 cell／Retained 的解包，保留原完整 cell 类型与各包含的同态类型，并形成全部选中阶段的统一对象端点。这是装配现有证明，不重证原像、模拟、逆、推挤或精确像。之后才接 future_cut／重排及后续源消费者；第 9–11 阶段和最终全部内部／非标准证明码的 Con 蕴含未完成。原 Comparator 仍独立未验。

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
| 8 构造核心 | 同一 Base/T 与饱和终行、理想/基数；实际 System、纤维/粘合、标签与传输；Works/Selected、rank/type、CodeLinks、固定序数表及 Preliminary；实际 OrdinalCount、全部内部条件下的密集总性/满射性、链对齐与实际索引图、cell/attachment 下降门及内部有限下降定理、完整推送粘合/消去、实际比较与换元、两类 cell 参数原像、两类生成性、实际普通闭包、有限旧系数、Attachment 传输、实际参数集／可数性、单 attachment 可数依赖图／保留词消费、内部首次出现索引、选中阶段计数及精确阶段像／保守范围 | 分量 germ/selector、OrbitAssignments、assignmentGraph_bijection；实际父输入统一、局部列表消费者及具体商双射 |
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
| 8 当前 | CellCuts.restrict_selected → CellReorder.future_cut/reordered → GermSelectors → OrbitAssignments → AssignedGraphs.assignmentGraph_bijection → ConcreteQuotients.quotient_bijection_above | 同一固定 cell／全局 dependencies_at 已验收；局部 selected_word、参数原像、simulation 与 pushout 已有 | 全局选中词、限制基底、精确像、两分支原像模拟和 work 推挤传输已证明；接固定 cell 的统一限制端点，再接源重排；不重证局部生产者，也不把当前全局依赖误报为未完成 |
| 9 | Models／具体 ProductNames | 同一具体系统、全秩 HS／正规滤子／强迫前端 | SVC、ACwo、全局商编码单射、¬AC，保留源全部量词 |
| 10 | PP／Main 和内部矛盾码归约 | 源反向单射链；底座 ObjectProofNode/ReducedProofPresentation/PureProvability/Sat | ZF/U 全模式专用公理检查、全部内部/非标准证明码的正确性及原核内部 Con 蕴含 |
| 11 | 最终交付 | scripts/verify.py、源锁/足迹/原核端点 | 最终主句、完整理论/语言/背景核查及干净检出复现；当前本地验收不替代终验 |
| 4 独立未验项 | 原 Comparator | 隔离原 Lean 4.34.1 的 Main 与五端点已通过 | Linux/landrun；本仓 CheckStep4 不是 Comparator |

完整 Base/T、饱和、L/ZFC 全模式、内部递归、名字/函数/商后端、支撑下降和规范化均已完成且被复用，不再列作数学缺口。localName_of_raw 与未使用的顶点商图/zigzag API 没有当前真实调用，不增列前置；实际纤维粘合商已由本批完成。

最终目标仍是 Derives nativeZF [] (Con_ZF → Con_U)，其中 U=ZF+PP+ACwo+¬AC，Con 覆盖全部内部/非标准证明码。原第 4 阶段完整 Comparator 仍缺 Linux/landrun；原 Main 的 8998 构建和五端点通过不能替代它。第 11 阶段历史 304 个 CRLF/LF 文件的干净检出源码锁复现仍未验收，本批没有重写历史证明。

历史分批验收及已被后续完成的旧待办保留在 Git `6a0a3d0`；当前待办只以上表和页首执行入口为准。
