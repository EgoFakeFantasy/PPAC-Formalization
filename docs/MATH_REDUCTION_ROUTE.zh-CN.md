# 原源证明的必要迁移链

对象目标仍为纯成员语言、完整 nativeZF、原 FirstOrder.Derives 中的 `Con_ZF → Con_U`，U = ZF + PP + ACwo + ¬AC。沿固定 OpenAI 1581d4cb 的构造；不另造一个只具有同名目标的证明。

采用直接证明归约：U 的矛盾证明 → ZFC 的矛盾证明 → ZF 的矛盾证明。中间 ZFC 不等于给最终背景增添 AC。下表是实际数学义务，不是开发次数估计。

| 必要环节 | 原源／现成供体 | 当前状态与下一接口 |
|---|---|---|
| L 解释和全模式 | 新版 YesMetaZFC 7979336：InnerModel.l_model_zf_l / l_model_zfc_l | 任意 ZF 模型中的内部 L 完整数学已经存在，ZFC 定向构建与端点审计通过。移植版本／语言对应，再接既有 Relativization/InterpretedZF/ModelTransfer；停止重建另一套 L。旧 ZFSet LCarrier 不是全部可用资产 |
| 原核全理论与相对化 | ReverseZFReplay、ChoiceNativeBridge、Relativization、InterpretedZF | 全模式、AC 两种呈现、19 规则回放已完成；具体解释非空及背景由实际供体接口提供，不当作假设偷渡 |
| 内部名字及作用 | ForcingNames、NameActions；本仓 ForcingNames/Evaluation/MapConditions/ConditionAction | 内部递归、check/pair/union、实际统一条件作用／群律已验收；具体阶段 8 单子仍待提供 |
| 小支撑正规滤子 | SupportFilter → ProductNames.system:89–92 | 标签置换、Fix、共轭图及像已验收；实际 subgroupFilter、有限并支撑界和全部四项正规性已构造；直接使用新版底座五个原证明，ω 基数性不再作为额外前提。实际 ProductNames.actionHom 和支撑 Context 已接通；非平凡性按源 ChoiceFailure 消费者另接 |
| 全秩 HS 和强迫前端 | SymmetricNames、AtomicForcing、ForcingQuotient、ForcingTruth.forcing_sound | 实际 HS 定义、空/check/pair/union、实际统一作用、原子与完整公式强迫、固定证明保真已完成；七条固定 ZF 公理与完整模式现均有原核证书。具体阶段 8 代数仍待实例化 |
| 全 ZF 在同一 HS 解释中成立 | SymmetricChoice.forces_ZF:203–217 | 目标端 ForcingZFAxioms.kernel_certificate 已接通全部九个源公理构造器。源宿主见证选择通过原生 Collection 适配，保留全群轨道和下游证明。仍有源代数／呈现／正规滤子前提；不是全部内部证明码归约或最终 Con |
| 源构造核心 | Algebra、Construction | 初始 Base.M、完整 height/cost/margin 已迁移；Probe Path 的因子／终端图、transition、有向系统、实际直极限字母商／投影和共同阶段相等判据已有。本批构造商上动作／target 图，并证明恒等、复合、单射与 target 等变性。exit 图、等变性、dvd_target_of_inCone、head_separation 与实际 Alphabet 已有原核证书。锥判据、锥交、共同倍数、初始 profile 和字母基数界已证明。Raw 内部载体和 old/cons 全案例已取得原核证书；原 oldAct/headDiv、实际 reduced/Word、唯一 quotient 图和 letterAct 七项定律现已取得原核证书；Raw.eval 总性／唯一性、闭包及 old/cons 方程也已回传原核；求值作用律／单射及实际 Word 左消去单子也已回传原核；实际 oldHom、因子／整除反映和 Word conical 已回传原核；下一步接 generator、呈现与大小界，再接 Probe/Merger 实际扩张、保守嵌入／margin 延拓、Placement/ConservativeHull 和最终单子。完整实数域不作为额外前置，不以字段假定核心结论 |
| 目标模型应用 | ChoiceFailure.forces_not_AC、OrdinalChoice.forces_ACwo、Models 中同一系统的 SVC／商单射 | 源完整证明已有，目标端主链未迁移；不换成局部或定秩见证 |
| 全秩 PP 和 Main | reverse_injection_dense → forces_PP → forces_target | 等待原依赖装配。保持所有满射的反向单射，不改成原满射截面 |
| 全部内部 Proof/Con | 底座 ObjectProofNode、ReducedProofPresentation、PureProvability 等 | 工具已存在；仍需 ZF/U 理论特化、完整公理测试及全部非标准内部证明码的正确归约。固定标准证明回放不等价于此项 |
| 最终封闭 | 上述两段内部归约 | 最终 Derives 尚未取得，阶段 11 未开始 |

排除：NatPacket/字节兼容、外部泛滤选择与 atomic_truth 分支、为主线新增 GCH 参数特化。源码 ConcreteSystem 的一般 ZFC 基数路线保持不变。不得删去源 PP 证明中实际使用的 ACwo 构造以形成循环。

当前 5–6 的接口工作和 7–10 的数学迁移必须区分；不能因供体未接入就把现成定理列作新的数学研发。新版供体源码及版本差异锁在 SOURCE_LOCK.companion_candidates；原源消费者、译入模块及公理足迹锁在 source_proof_adaptations。

原源：../openai-math-ppac-source/lean/OAI/SetTheory/PartitionConsistency/。BMS 的完备性回传已用于 ModelTransfer；IBLP 的具体集合满足关系只在背景对应后引用，不重复造 Sat。禁止恢复用户退役的旧反射实现。
