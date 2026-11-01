# 当前状态：原 1–11 阶段（2026-11-01）

## 当前执行入口：Assigned 理想与实际扩张已迁移 → 两条兼容性定律与赋值图

基点 `9d93355` 已完成全轨道商统一记录函数及全部 16 个参数函数。本批沿固定源继续：`ForcingForcedAvailabilityCongruence` 证明实际可用性理想的 EqF 同余；`ForcingAssignedIdeal` 直接从已完成的 assigned_stable 取得当前条件的理想，并用现成顶点编码单射性对齐。

`ForcingLabelVertices` 用已有 SystemAvailability 理想与纤维构造实际标签顶点，证明唯一性、标签成员关系和实际箭头；收缩合同直接复用 availability_sub。`ForcingAssignedExtension` 按源 assigned_at_extension 顺序组合已有 label、mono、实际箭头与 restrict，并复用 assigned_reindex 处理箭头见证，保留同一个标签和名字。目标顶点满足实际 LabelVertex 关系，其存在由上一构造提供。

五个原核端点：可用性同余、标签顶点构造、标签箭头及 Assigned 扩张属于普通 nativeZF；Assigned 理想端点相对化到同一已有内部 L。没有新建 L、全模式、递归、函数图、商或理想基础设施。

全量验收通过：3168 个构建任务、36809 项声明、2723 个文件哈希；27 项新增声明，36782 项旧依赖指纹完全不变。9 条命令（含 5 条 trust=0）全部退出 0，零警告，无新增公理依赖；75 个源哈希与三份干净固定版本匹配。报告：verification/assigned-ideal-acceptance.json。

**仍在原第 8 阶段。** 真正后续为源 assigned_compatible_one/assigned_compatible_inj、赋值图和具体商双射，以及同一最终父输入的实例化与实际记录见证对齐。已完成的 16 函数族、assigned_ideal、labelVertex/arrow 和 assigned_at_extension 不再列为缺失。第 9–11 阶段、最终内部 Con 和原 Comparator 仍未完成。

| 原阶段 | 已完成 | 真实未完项 |
|---|---|---|
| 1 语言桥接 | 全构造子、binder、语义与原核连线 | 无 |
| 2 源推导传输 | 重命名／替换、19 规则、有限支撑及反向编译 | 标准证书部分已完成；全部内部码归 10 |
| 3 全理论对应 | ZF 全模式、Replacement/Collection、AC 双呈现、ZF/U 回放 | 无；不再重报完整模式缺失 |
| 4 原外部基线 | 隔离 Lean 4.34.1 原 Main 8998 构建、五端点 trust=0 | 原 Comparator 未运行，缺 Linux/landrun；CheckStep4 不是它 |
| 5 名字／图／递归基础 | 完整已验收基础包、实际条件／作用／HS 接线 | 后续同一具体系统消费者归 8–10 |
| 6 背景／解释／universe | 同一任意原生 ZF 模型内部完整 L/ZFC、原生与源全模式、Choice/order/非空、逐点域与解释背景实际消去 | 原范围已完成；内部 Proof/Con 归 10 |
| 7 强迫前端 | 固定 ZF 公理与全模式原核证书、实际作用／滤子／全秩 HS 合同 | 第 8 的最终具体系统实例化；全部内部码归 10 |
| 8 构造核心 | 同一 Base/T 与饱和终行、理想/基数；实际 System、纤维/粘合、标签与传输；Works/Selected、rank/type、CodeLinks、固定序数表及 Preliminary；实际 OrdinalCount、全部内部条件下的密集总性/满射性、链对齐与实际索引图、cell/attachment 下降门及内部有限下降定理、完整推送粘合/消去、实际比较与换元、两类 cell 参数原像、两类生成性、实际普通闭包、有限旧系数、Attachment 传输、实际参数集／可数性、单 attachment 可数依赖图／保留词消费、内部首次出现索引、选中阶段计数及精确阶段像／保守范围；统一 conditionSelector／Selected、具体 component_selector_dense、StableAt 定义及双向置换、corrected_stable 已验收；corrected_total 已验收；corrected_onto 已验收；OrbitAssignment 定义、RootGroup 等价及 orbit/label/mono/restrict/permute/congr/descend/stable/eq_iff 已验收；完整轨道等价／全商／投影与代表函数、orbit_rep、统一 orbitChain、全量词 orbitAssignment_total_at／onto_at、orbitAssignment_index、全根群计数归约及实际代表链 total/onto、Assigned 公式/同轨道归约及固定参数族下 eq_iff/total/onto、label/mono/permute/restrict/stable、实际代码数据、选择器呈现、全轨道商统一记录函数及完整 16 字段函数族，以及实际 Assigned 理想、标签顶点/箭头和 at_extension 已验收 | Assigned 两条兼容性与 assignmentGraph_bijection；实际父输入统一、局部列表消费者及具体商双射 |
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
| 8 当前 | ConcreteQuotients.component_selector_dense → actual selector → OrbitAssignments → AssignedGraphs.assignmentGraph_bijection → ConcreteQuotients.quotient_bijection_above | 同一固定 cell／全局 dependencies_at、实际阶段闭包、完整 restrict_selected、有向并集／unionLift 和完整 Square.union 已验收 | 完整 future_cut 与实际 future/reordered 已取得原核证书：现成逆同态、推送消去与实际顶点均被消费；现成可数 hull 已接入 countable_reordering，实际索引有限下降已取得原核证书；alignment 消费与全商可数编码已接通；具体初始底/flattening 消费及 countable_germs 已接通；实际尾探测函数及完整可数坐标集已接通；不同 coset 的 detector_separates 已取得原核证书；实际 fill、Complete 覆盖扩张和 countable_fusion 已取得原核证书；实际标签对稠密要求、统一严格比特界与同一 Complete 条件已接通；实际 rows／Eventual 商与 rawPattern 函数已构造；rawPattern_congr、pattern 下降、bounded-pattern 单射性和具体 good_dense 已完成；Complete.pattern_eq／置换保持、Good.mono 与 rawPattern_moveRows 已完成；整个 germ 商左乘、pattern_covariance、distinguishes_moveRows_iff 和 Good.permute 已接通；内部 leastBound、Complete 最小界和扩张／置换稳定性已接通；bestCoset 最小值／区分界唯一性／协变与共同固定 pattern 顺序已接通；统一 conditionSelector／Selected 的完整函数图及六项定律已接通；具体 component_selector_dense 与实际置换协变已从同一终行接通；Corrected 定义及 selected／common／mono／restrict／congr／eq_iff／permute／descend、StableAt 及 corrected_stable／total／onto 均已验收；OrbitAssignment 定义、RootGroup 等价及 orbit／label／mono／restrict／permute／congr／descend／stable／eq_iff、完整轨道商／投影、代表函数、统一 orbitChain、total_at／onto_at、实际轨道索引、全根群计数归约及实际代表链密集性已验收，Assigned 公式、同轨道归约及 eq_iff/total/onto 已验收；五条主线 Assigned 定律现已验收；实际逐轨道代码数据、固定呈现选择器、全轨道商统一记录函数及完整 16 字段函数族已验收；实际 Assigned 理想、标签顶点/箭头及 at_extension 已验收；下一项为两条兼容性定律、赋值图与父输入/记录见证对齐。保留同一终端单子与精确生成子幺半群 |
| 9 | Models／具体 ProductNames | 同一具体系统、全秩 HS／正规滤子／强迫前端 | SVC、ACwo、全局商编码单射、¬AC，保留源全部量词 |
| 10 | PP／Main 和内部矛盾码归约 | 源反向单射链；底座 ObjectProofNode/ReducedProofPresentation/PureProvability/Sat | ZF/U 全模式专用公理检查、全部内部/非标准证明码的正确性及原核内部 Con 蕴含 |
| 11 | 最终交付 | scripts/verify.py、源锁/足迹/原核端点 | 最终主句、完整理论/语言/背景核查及干净检出复现；当前本地验收不替代终验 |
| 4 独立未验项 | 原 Comparator | 隔离原 Lean 4.34.1 的 Main 与五端点已通过 | Linux/landrun；本仓 CheckStep4 不是 Comparator |

完整 Base/T、饱和、L/ZFC 全模式、内部递归、名字/函数/商后端、支撑下降和规范化均已完成且被复用，不再列作数学缺口。localName_of_raw 与未使用的顶点商图/zigzag API 没有当前真实调用，不增列前置；实际纤维粘合商已由本批完成。

最终目标仍是 Derives nativeZF [] (Con_ZF → Con_U)，其中 U=ZF+PP+ACwo+¬AC，Con 覆盖全部内部/非标准证明码。原第 4 阶段完整 Comparator 仍缺 Linux/landrun；原 Main 的 8998 构建和五端点通过不能替代它。第 11 阶段历史 304 个 CRLF/LF 文件的干净检出源码锁复现仍未验收，本批没有重写历史证明。

历史分批验收及已被后续完成的旧待办保留在 Git `6a0a3d0`；当前待办只以上表和页首执行入口为准。
