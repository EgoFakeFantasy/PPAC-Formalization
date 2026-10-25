# 原源证明的必要迁移链

对象目标仍为纯成员语言、完整 nativeZF、原 FirstOrder.Derives 中的 `Con_ZF → Con_U`，U = ZF + PP + ACwo + ¬AC。沿固定 OpenAI 1581d4cb 的构造；不另造一个只具有同名目标的证明。

采用直接证明归约：U 的矛盾证明 → ZFC 的矛盾证明 → ZF 的矛盾证明。中间 ZFC 不等于给最终背景增添 AC。下表是实际数学义务，不是开发次数估计。

| 必要环节 | 原源／现成供体 | 当前状态与下一接口 |
|---|---|---|
| L 解释和全模式 | 新版 YesMetaZFC 7979336：InnerModel.l_model_zf_l / l_model_zfc_l | 任意 ZF 模型中的内部 L 完整数学已经存在，ZFC 定向构建与端点审计通过。移植版本／语言对应，再接既有 Relativization/InterpretedZF/ModelTransfer；停止重建另一套 L。旧 ZFSet LCarrier 不是全部可用资产 |
| 原核全理论与相对化 | ReverseZFReplay、ChoiceNativeBridge、Relativization、InterpretedZF | 全模式、AC 两种呈现、19 规则回放已完成；具体解释非空及背景由实际供体接口提供，不当作假设偷渡 |
| 内部名字及作用 | ForcingNames、NameActions；本仓 ForcingNames/Evaluation/MapConditions/ConditionAction | 内部递归、check/pair/union、作用律已验收；具体 ProductNames 条件／群同态呈现仍待接 |
| 小支撑正规滤子 | SupportFilter → ProductNames.system:89–92 | 标签置换、Fix、共轭图及像已验收；实际 subgroupFilter、有限并支撑界和全部四项正规性已构造；直接使用新版底座五个原证明，ω 基数性不再作为额外前提。下一接口是具体 ProductNames.actionHom；非平凡性按源依赖另接 |
| 全秩 HS 和强迫前端 | SymmetricNames、AtomicForcing、ForcingQuotient、ForcingTruth.forcing_sound | 实际 HS 定义、空/check、通用 HS.smul、原子递归／定律／对称性及固定公式／证明保真已完成。具体系统实例、HS pair/union 和解释公理仍待接 |
| 全 ZF 在同一 HS 解释中成立 | SymmetricChoice.forces_ZF:203–217 | 源证明已有，目标端迁移未完成；复用完整 Replacement/Collection 对应。新版底座普通 forcing ZF 保持不自动等同于 HS 解释，先核对合同 |
| 源构造核心 | Algebra、Construction | Monoid/Placement/ConservativeHull 及实际不变量待迁移，不能以字段假定核心结论 |
| 目标模型应用 | ChoiceFailure.forces_not_AC、OrdinalChoice.forces_ACwo、Models 中同一系统的 SVC／商单射 | 源完整证明已有，目标端主链未迁移；不换成局部或定秩见证 |
| 全秩 PP 和 Main | reverse_injection_dense → forces_PP → forces_target | 等待原依赖装配。保持所有满射的反向单射，不改成原满射截面 |
| 全部内部 Proof/Con | 底座 ObjectProofNode、ReducedProofPresentation、PureProvability 等 | 工具已存在；仍需 ZF/U 理论特化、完整公理测试及全部非标准内部证明码的正确归约。固定标准证明回放不等价于此项 |
| 最终封闭 | 上述两段内部归约 | 最终 Derives 尚未取得，阶段 11 未开始 |

排除：NatPacket/字节兼容、外部泛滤选择与 atomic_truth 分支、为主线新增 GCH 参数特化。源码 ConcreteSystem 的一般 ZFC 基数路线保持不变。不得删去源 PP 证明中实际使用的 ACwo 构造以形成循环。

当前 5–6 的接口工作和 7–10 的数学迁移必须区分；不能因供体未接入就把现成定理列作新的数学研发。新版供体源码及版本差异锁在 SOURCE_LOCK.companion_candidates；原源消费者、译入模块及公理足迹锁在 source_proof_adaptations。

原源：../openai-math-ppac-source/lean/OAI/SetTheory/PartitionConsistency/。BMS 的完备性回传已用于 ModelTransfer；IBLP 的具体集合满足关系只在背景对应后引用，不重复造 Sat。禁止恢复用户退役的旧反射实现。
