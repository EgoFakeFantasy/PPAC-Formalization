# 当前状态：原 1–11 阶段（2026-11-07）

## 本批验收（2026-11-07）：实际逆图与持久列表外成员，仍为阶段 8

`ForcingUniformInverseGraph` 消费已完成的最小下标关系，迁移固定源 `UniformInverse.least_move/relation_move:212–233`、实际逆图／限制逆图单射 `UniformNames:239–277`，以及 `outside_uniformRange:282–311` 对实际完整局部名字列表的消费者 `ClassFibers.outside_localList:224–241`。现有条件置换的逆像保持每个更强条件下的负相等，现有 `map_checked` 给出核名字固定性；现有 HS 图构造器与 `graph_injection` 产生真实受支撑图和完整强迫单射公式。

非良序性直接排除这个实际单射，再用已有成员正则性取得稠密的持久列表外成员；未把不存在单射或逆图当作额外前提。`construction_kernel_certificate` 与 `outside_kernel_certificate` 均为普通 `nativeZF` 中的原 `FirstOrder.Derives` 对象闭句证书，量化全部内部 HS 名字、条件与下标。局部载体／序数枚举／根支撑的父输入仍显式保留，其生产者 `ForcingLocalList.construct` 已有。

全量验收已通过：9 条命令（5 条 trust=0）退出 0，零警告，37104 项旧声明足迹不变，无新增公理依赖。报告：`verification/uniform-inverse-graph-acceptance.json`。

下一项仍是固定源 `outsideClassSet_denseBelow:265`：把成员与实际商的 canonical 类对齐，扩图覆盖条件支撑及标签，并证明右因子非平凡；随后接 `nonwellorderable_quotient_bijection`。这些及阶段 9–11、最终内部 Con 尚未完成。L、全公理模式、递归与 Proof/Sat 基础继续复用，不重建。

## 此前已验收：核名字序数强迫与良序反射（ForcingCheckOrdinal）

本节保留此前验收记录；当前待办以页首为准。

`ForcingCheckOrdinal` 已迁移固定源 `UniformNames.transF_checkOrdinal:336–341`、`ordF_checkOrdinal:343–352`、`forces_membershipWellFounded:354–379`、`forces_checkOrdinal:381–386` 以及 `ClassFibers.wellorderableFormula:12–13`、`wellorderable:15–17`、`forces_wellorderable:27–63`、`wellorderable_of_check_injection:65–71`、`no_check_injection_of_not_wellorderable:73–93`。在纯 `nativeZF` 中（无需对象 Choice）证明任意内部序数 `α` 的核名字 `check(α)` 被强迫满足 `TransF`、`OrdF`、`membershipWellFounded` 与 `OrdinalF`，并建立 `WellorderableF` 与向 `check(α)` 的强迫单射（`ForcingRelationGraphFunctions.injection`）之间的双向反射及逆否消去引理 `no_check_injection_of_not_wellorderable`。

`kernel_certificate` 是原 `nativeZF` 对闭句 `sentence` 的 `FirstOrder.Derives` 证书，仅依赖 7 条纯 ZF 公理证书与标准三项公理，不引入 Choice。

全量验收：3193 jobs、37079 项声明、2748 文件哈希；全部 37065 项旧足迹不变，14 项新增声明；9 条命令（5 条 trust=0）退出 0，零警告，无新增公理依赖。75 份固定源哈希和三个干净依赖版本已核对。报告：verification/forcing-check-ordinal-acceptance.json。

**仍在原第 8 阶段。** 下一项是迁移 `ClassFibers` 的非良序判别接口（`outsideClassSet_denseBelow` / `not_wellorderable_of_outsideClassSet_dense`），将已验收的 `quotient_bijection_above` 与 `ForcingCheckOrdinal` 接入 `ConcreteQuotients.nonwellorderable_quotient_bijection:401–443` / `not_wellorderable_quotient:446`，并完成最终共同父输入装配。已有 Candidates 名字载体、理想、L、完整模式、递归和 Proof/Sat 不重做。具体 Cardinals/mark/补集及全局父参数仍须最终统一消去。第 9–11 阶段、最终内部 Con 和原 Comparator 仍未完成。

| 原阶段 | 已完成 | 真实未完项 |
|---|---|---|
| 1 语言桥接 | 全构造子、binder、语义与原核连线 | 无 |
| 2 源推导传输 | 重命名／替换、19 规则、有限支撑及反向编译 | 标准证书部分已完成；全部内部码归 10 |
| 3 全理论对应 | ZF 全模式、Replacement/Collection、AC 双呈现、ZF/U 回放 | 无；不再重报完整模式缺失 |
| 4 原外部基线 | 隔离 Lean 4.34.1 原 Main 8998 构建、五端点 trust=0 | 原 Comparator 未运行，缺 Linux/landrun；CheckStep4 不是它 |
| 5 名字／图／递归基础 | 完整已验收基础包、实际条件／作用／HS 接线 | 后续同一具体系统消费者归 8–10 |
| 6 背景／解释／universe | 同一任意原生 ZF 模型内部完整 L/ZFC、原生与源全模式、Choice/order/非空、逐点域与解释背景实际消去 | 原范围已完成；内部 Proof/Con 归 10 |
| 7 强迫前端 | 固定 ZF 公理与全模式原核证书、实际作用／滤子／全秩 HS 合同 | 第 8 的最终具体系统实例化；全部内部码归 10 |
| 8 构造核心 | 同一 Base/T 与饱和终行、理想/基数；实际 System、纤维/粘合、标签与传输；Works/Selected、rank/type、CodeLinks、固定序数表及 Preliminary；实际 OrdinalCount、全部内部条件下的密集总性/满射性、链对齐与实际索引图、cell/attachment 下降门及内部有限下降定理、完整推送粘合/消去、实际比较与换元、两类 cell 参数原像、两类生成性、实际普通闭包、有限旧系数、Attachment 传输、实际参数集／可数性、单 attachment 可数依赖图／保留词消费、内部首次出现索引、选中阶段计数及精确阶段像／保守范围；统一 conditionSelector／Selected、具体 component_selector_dense、StableAt 定义及双向置换、corrected_stable 已验收；corrected_total 已验收；corrected_onto 已验收；OrbitAssignment 定义、RootGroup 等价及 orbit/label/mono/restrict/permute/congr/descend/stable/eq_iff 已验收；完整轨道等价／全商／投影与代表函数、orbit_rep、统一 orbitChain、全量词 orbitAssignment_total_at／onto_at、orbitAssignment_index、全根群计数归约及实际代表链 total/onto、Assigned 公式/同轨道归约及固定参数族下 eq_iff/total/onto、label/mono/permute/restrict/stable、实际代码数据、选择器呈现、全轨道商统一记录函数及完整 16 字段函数族，以及实际 Assigned 理想、标签顶点/箭头和 at_extension 已验收；两条兼容性、GraphWitness/GraphHolds 关系定律及实际条目函数图已全量验收；有序对强迫相等及 raw 关系名字构造已全量验收；四条图函数结论和实际 Assigned 关系的 Source 公式／三项基本定律已验收；实际 quotientName 及其成员／固定性已验收；实际 Assigned 图两个成员界限及实际图置换、实际标签分离及实际图单值性／单射性／全域性／满射性、源理想稠密稳定化、实际局部类可用性／顶点、实际赋值图／assignmentGraph_bijection 及具体商双射（preliminary_ordinalCount／quotient_bijection_above）已验收 | 非良序商稠密双射（nonwellorderable_quotient_bijection）、实际父输入统一及局部列表消费者 |
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
| 8 当前 | ConcreteQuotients.component_selector_dense → actual selector → OrbitAssignments → AssignedGraphs.assignmentGraph_bijection → ConcreteQuotients.quotient_bijection_above | 同一固定 cell／全局 dependencies_at、实际阶段闭包、完整 restrict_selected、有向并集／unionLift 和完整 Square.union 已验收 | 完整 future_cut 与实际 future/reordered 已取得原核证书：现成逆同态、推送消去与实际顶点均被消费；现成可数 hull 已接入 countable_reordering，实际索引有限下降已取得原核证书；alignment 消费与全商可数编码已接通；具体初始底/flattening 消费及 countable_germs 已接通；实际尾探测函数及完整可数坐标集已接通；不同 coset 的 detector_separates 已取得原核证书；实际 fill、Complete 覆盖扩张和 countable_fusion 已取得原核证书；实际标签对稠密要求、统一严格比特界与同一 Complete 条件已接通；实际 rows／Eventual 商与 rawPattern 函数已构造；rawPattern_congr、pattern 下降、bounded-pattern 单射性和具体 good_dense 已完成；Complete.pattern_eq／置换保持、Good.mono 与 rawPattern_moveRows 已完成；整个 germ 商左乘、pattern_covariance、distinguishes_moveRows_iff 和 Good.permute 已接通；内部 leastBound、Complete 最小界和扩张／置换稳定性已接通；bestCoset 最小值／区分界唯一性／协变与共同固定 pattern 顺序已接通；统一 conditionSelector／Selected 的完整函数图及六项定律已接通；具体 component_selector_dense 与实际置换协变已从同一终行接通；Corrected 定义及 selected／common／mono／restrict／congr／eq_iff／permute／descend、StableAt 及 corrected_stable／total／onto 均已验收；OrbitAssignment 定义、RootGroup 等价及 orbit／label／mono／restrict／permute／congr／descend／stable／eq_iff、完整轨道商／投影、代表函数、统一 orbitChain、total_at／onto_at、实际轨道索引、全根群计数归约及实际代表链密集性已验收，Assigned 公式、同轨道归约及 eq_iff/total/onto 已验收；五条主线 Assigned 定律现已验收；实际逐轨道代码数据、固定呈现选择器、全轨道商统一记录函数及完整 16 字段函数族已验收；实际 Assigned 理想、标签顶点/箭头及 at_extension 已验收；两条兼容性已验收；本批 GraphWitness/GraphHolds 关系定律、有序对名字及实际条目函数图已全量验收；本批进一步取得有序对强迫相等刻画、保留两条成员测试的实际 raw 关系名字构造及精确条目方程；test 置换/HS 支撑已完成全量原核验收；强迫图成员与有序对成员刻画已取得原核证书；原 App 公式与实际图应用刻画已取得原核证书；四条完整图函数消费者及实际 Assigned Source 关系／三项基本定律已验收；实际 quotientName 构造、完整成员等价与固定性已取得两个原核证书；实际 Assigned 记录字段已对齐并消费已有稳定性，GraphWitness/GraphHolds 两个成员界限已取得同一内部 L 中的原核证书；实际图置换现已取得普通 nativeZF 原核证书，界固定性从实际 labelBound 消去；实际标签分离（ProductNames.label_not_equal）已由现有 Cohen 分离和 checkName 反射接通并取得原核证书；实际图单值性现已从两份真实稠密见证和共同条件接通并取得同一内部 L 原核证书；实际图单射性现已从同一记录、原始条目和共同条件的输出相等取得同一内部 L 原核证书；实际图全域性及内部 AllCounts 公式已取得同一内部 L 原核证书；源理想稠密稳定化现已取得同一内部 L 原核证书；实际局部类的可用性族、理想性、稳定化与真实顶点／Entry／StableAt 已取得同一内部 L 原核证书；实际图满射现已接通实际商成员、局部类构造／唯一性、稳定顶点与全轨道记录／assigned_onto 并取得同一内部 L 原核证书；实际赋值图（exists_assignmentGraph）及强迫双射（assignmentGraph_bijection）现已合成并取得同一内部 L 原核证书；全轨道参数计数（all_counts）及具体商双射（quotient_bijection_above）现已接通并取得同一内部 L 原核证书；下一项为非良序商稠密双射（nonwellorderable_quotient_bijection）及最终父输入对齐。保留同一终端单子与精确生成子幺半群 |
| 9 | Models／具体 ProductNames | 同一具体系统、全秩 HS／正规滤子／强迫前端 | SVC、ACwo、全局商编码单射、¬AC，保留源全部量词 |
| 10 | PP／Main 和内部矛盾码归约 | 源反向单射链；底座 ObjectProofNode/ReducedProofPresentation/PureProvability/Sat | ZF/U 全模式专用公理检查、全部内部/非标准证明码的正确性及原核内部 Con 蕴含 |
| 11 | 最终交付 | scripts/verify.py、源锁/足迹/原核端点 | 最终主句、完整理论/语言/背景核查及干净检出复现；当前本地验收不替代终验 |
| 4 独立未验项 | 原 Comparator | 隔离原 Lean 4.34.1 的 Main 与五端点已通过 | Linux/landrun；本仓 CheckStep4 不是 Comparator |

完整 Base/T、饱和、L/ZFC 全模式、内部递归、名字/函数/商后端、支撑下降和规范化均已完成且被复用，不再列作数学缺口。localName_of_raw 与未使用的顶点商图/zigzag API 没有当前真实调用，不增列前置；实际纤维粘合商已由本批完成。

最终目标仍是 Derives nativeZF [] (Con_ZF → Con_U)，其中 U=ZF+PP+ACwo+¬AC，Con 覆盖全部内部/非标准证明码。原第 4 阶段完整 Comparator 仍缺 Linux/landrun；原 Main 的 8998 构建和五端点通过不能替代它。第 11 阶段历史 304 个 CRLF/LF 文件的干净检出源码锁复现仍未验收，本批没有重写历史证明。

历史分批验收及已被后续完成的旧待办保留在 Git `6a0a3d0`；当前待办只以上表和页首执行入口为准。
