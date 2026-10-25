# 2026-10-26 源码重审结论（当前状态）

| 已有资产 | 本轮实读的精确证据 | 正确裁决 |
|---|---|---|
| YesMetaZFC 全公理模式 | 固定 039c8e1，SetTheory/Axioms/ZF.lean 的 Axiom.separation/collection 对任意参数数目和任意矩阵；Separation.lean、Collection.lean 的模型接口 | 已完成，直接复用；不是待证明基础 |
| 本仓全模式原核迁移 | ReverseZFReplay.replay_project_axiom 枚举所有原生构造器；derives_iff/source_sentence_iff/target_derives_iff；CollectionFromReplacement.native_project_matrix | 已完成，不能把新解释中的接线叫作重证全模式 |
| 完整 L 模型数学 | lean-constructible-universe-stage4 固定 7f5a7d0；ZFModel.lean:28 lCarrier_models_ZF 的分支包括任意 n、phi 的 Separation 和 Replacement；StageHistoryGraphSystem.lean:171 lCarrier_models_ZFC 无额外未消前提 | 已完成于该库的 LCarrier；继续复用其构造及证明，不从零造 L |
| 精确 L 终局类型 | Model.lean 中 ClassCarrier M = {x : ZFSet // x∈M}，LCarrier 为实际 L 的子类型；ZFModel 目标为 Mathlib FOL 的模型断言 | 该精确类型不量化所有 nativeZF 模型。当前已查的固定底座及本地 YesMetaZFC／stage4 桥中，尚未定位到可直接调用的 `Derives nativeZF [] α^L` 全模式终局；这是定位／适配状态，不宣称其他位置没有做过 |
| 原核收尾方法 | BMS SecondOrderCompleteness.derives_m 调原 strong_completeness；本仓 ModelTransfer 已适配纯成员语言、任意对应 Type 0 模型和实际 nativeZF | 已接入，不再复制调度／完备性。具体 LCarrier 真值不能填“所有模型”参数 |
| 相对化中的全模式接线 | 新 InterpretedZF 的 source_sentence/native_sentence/project_axiom/collection，全部由已证 ReverseZFReplay、Relativization、CollectionFromReplacement 组合 | 本轮正式检查通过，记为第 6 阶段接口；相对化 ZF 背景和域非空明确保留，不声称完整 L 解释或 Con 已闭合 |

原 PPAC 数学链已开始接入其实际入口：ForcingNameInduction 保留原 ForcingNames.Child 的 `∃condition, pair(subname,condition)∈parent`，把 child_wf 的三次成员下降通过已有集合归纳模式回传为原核闭句。通用底座 WellFounded.Recursion.solve 要求宿主 WellFounded，不能用于任意可能外部不良基的 nativeZF 模型；本适配改用已经完成的 SetInduction.native_induction，不复制递归器。完整名字定义／递归与强迫关系未被这条归纳模式替代。固定源 SHA、实际消费者和 18 项精确依赖见 SOURCE_LOCK.source_proof_adaptations。

ForcingNames 本批继续消费同一固定源的 IsName／isName_iff。原 ConditionAction.conditions 是 ZFSet，目标采用内部集合参数 P；不声称覆盖任意不可定义的外部类条件。内部 Closed(P,S) 要求 S 中每个名字的每个条目具有原 Kuratowski 配对形状，条件属于 P、子名字属于 S；IsName(P,σ) 定义为存在这样的 S 包含 σ。直接消费已有 Collection、Separation、KP.exists_union／exists_insert 合并子名字见证；Collection 中的杂项先经完整分离筛掉，没有抽取选择函数。原两合取展开式、intro／edges、child／condition 和空名字均已构造；现有 Child 归纳还给出任意参数公式解的唯一性模式，并回传原 Derives。定向及完整验收均已通过：37 项新增声明全部审计，2838 构建任务、28855 声明、9 命令退出 0、5 条 trust=0、零警告；四类原核证书仅继承标准三项和原七项 ZF 句子证书。该 IsName 批次没有实现名字函数递归；本轮 evaluate 的实际完成范围见下一段。

ForcingEvaluation 继续适配原 evaluate／evaluate_eq／mem_evaluate_iff／evaluate_empty。它用模型内部集合图表示部分求值；已有 Child 公式归纳证明不同图在共同名字上的值相等，已有 Collection 收集子名字图并通过 Separation 清除不合格杂项，Union 合并相容图，Kuratowski 配对和插入扩展当前节点。值集合直接由原活跃条目方程经 Union 与 Separation 构造。原核闭句覆盖每个内部集合 G、每个原始集合名字 σ 的存在、唯一、成员展开和空名字；不限制名字秩、不预设 IsName、不使用宿主 WellFounded。原外部泛型滤子与内部参数的解释对应仍属阶段 6–7，mapConditions 的本批范围见下段，原子强迫递归现已由本文末 Atomic 批次构造；原子定律现已由本文末 Basic/Laws 批次接入；具体条件呈现和真值引理待接。本批完整验收通过：44 项新增声明全部覆盖，2839 构建任务、28899 声明、9 命令退出 0、5 条 trust=0、零警告；四条原核证书未增加原七项 ZF 句子证书之外的依赖。

ForcingMapConditions 适配同一源文件第 96–128 行：原 child_wf.fix 在目标端用已验收的 Child 公式归纳及内部集合图实现；函数式 Replacement、笛卡尔积和完整分离直接调用 YesMetaZFC，逐变量翻译复用 ProjectSyntax.binary／GodelDefRecursion.encode_semantics。共享辅助的算子全定义性、单值性和子名字依赖性均由具体映射算子证明，没有假定目标递归已存在。五类原核闭句模式保留条件映射的对象全函数前提，覆盖所有内部原始名字。外部不可定义函数不在此公式模式的声明范围；原恒等律、复合律、IsName 保持、公式类 evaluate 相容性和具体 actCode 实例现已验收，见下文对应模块；任意外部泛型滤子解释仍待接。新增 69 项声明（含结构构造器及三个字段）预审计只使用标准三项和原七项 ZF 句子证书，完整验收已通过。

ForcingMapLaws 按原第 130–165 行的 Child 归纳推进 `mapConditions_id`、`mapConditions_comp`、`IsName.mapConditions`；直接消费既有名字边／子名字性质、映射成员／边方程及唯一性，不再构造递归。原第 425–439 行对 actCode 函数的外延替换通过逐点等价关系给出对象图同余。恒等律的 IsName 条件、复合次序 f∘g 及名字保持的 P→Q 条件均与源一致。四类原核证书和全部 33 项声明已定向构建、预审计通过，完整验收已通过。实际 actCode 实例及公式定义条件类的 evaluate_mapConditions 现已验收；任意不可定义外部泛型滤子的解释仍待接，不能从内部集合 G 或公式类结果推定完成。

ForcingClassEvaluation／ForcingEvaluationCovariance 继续消费同一源的 evaluate、成员方程及 169–181 行协变证明。条件类由任意参数公式给出，旧内部集合 G 求值通过 membershipPredicate 实例取得对象等价；逆像由存在量词、原映射关系与条件谓词直接构造，不假设它是集合。递归复用 ForcingNameRecursion，值域界复用 coordinate_bound，输出使用原完整 Separation；相容性直接调用已证 Child 归纳、映射边方程和求值唯一性。五类原核证书、43 项声明已定向构建和预审计通过，完整验收已通过。此公式模式不是任意不可定义外部泛型滤子的表示定理，后者仍在源解释链中待接。

原 actCode 消费端已核对固定底座 SetTheory/FunctionConstruction.lean 的 exists_identityBijection、exists_inverseBijectionWithPairs、exists_compositionBijection：背景为任意 Project ZF 模型，配对约定显式给出，逆图保留精确边对应。通过既有 ModelTransfer.project_models_iff 与 KuratowskiZF.interpretation 可接本仓；不另造恒等、逆或复合双射。接口定位现已由下一段所列适配实际消费；这一旧定位记录不再构成待办。

ForcingConditionGraphs／ForcingConditionAction 已实际消费上述接口。原 functionOn AST 未重定义；其纸面语义与底座 IsSetFunctionFromTo／IsSetBijectionFromTo 建立精确对应。恒等图采用 exists_setFunctionFromTo_of_denote 的 identityValue 实例、逆图采用 exists_inverseBijectionWithPairs、复合图采用 exists_compositionFunction；这些返回实际边方程，避免把只保证“某个双射”的推论冒充指定恒等或复合。原 actCode 的内／外条件分支保留，名字作用只调用已证的 mapping、恒等、复合、同余与求值相容性，不把作用律设为字段。九类原核证书和 70 项声明预审计没有新增可信基依赖，完整验收已通过。SOURCE_LOCK 同时锁定所消费 FunctionConstruction.lean 的 SHA-256。原具体群同态族与完整对称系统尚未实例化。

ForcingPairName／ForcingUnionName 本批沿固定 ForcingNames 第 239–348 行及 Name.smul_pair 迁移：配对使用 KP.exists_pair 和既有 Kuratowski 编码；并名字通过既有坐标界、Union、ZF.exists_cartesianProduct、Separation 获得全部共同加强条件的精确范围。求值和映射直接消费已有成员方程及单值性。并名字求值明确保留源滤子的包含、向上闭包和定向性，不假设二元交或选择加强条件。64 项声明、12 类原核证书已通过完整验收（2848 构建任务、29178 声明审计、9 命令成功、5 条 trust=0、零警告）。checkName 和 unionName 作用律现已由本批下述模块迁移并验收；既有配对、集合并、笛卡尔积及分离不是待重做的基础。

checkName 的下一复用入口已实读：固定底座 SetTheory/Ord/Recursion.lean:1297 recursiveSequence_exists、1322 recursionValue_exists、1339 transfiniteRecursion_isClassFunctionOnOrdinals，在任意 Project ZF 模型中工作，保留可定义序列算子的全定义／单值前提，不要求宿主 WellFounded。本仓 ConstructibleHistory:531 与 GodelDefRecursion:176 已消费这一组入口。后续应接原 checkName 的具体算子及成员递归对应，而不是再次建设超限递归；该接口定位不表示递归基础缺失；本批 checkName 的原成员递归直接消费已验收的集合归纳，而不是把序数序列算子冒用为成员递归。

ForcingUnionAction 逐成员复用原第 494–532 行的两个方向，保持全体条件码上的序不变前提；满射置换图给出源逆作用所需原像。ForcingCheckName 专门表示原第 184–201 行的成员递归值域，复用 SetInduction.native_induction、既有 comparison/union_edge/insert_edge、Collection／Separation 和配对／积；没有新通用递归器，也未要求任意模型外部良基。ForcingCheckNameLaws 按原第 203–237、474–478 行完成三个成员归纳证明及固定条件作用。74 项声明、10 类证书完整验收通过；具体 HS 与泛型解释仍未完成。

本轮未修改任何其他仓库或固定依赖。IBLP 的集合 Sat 是先前已读的候选，本轮没有重新编译或将其计为新迁移成果。旧批次的重复验收数字不用于判断当前阶段。

# 优先复用的已完成接口（2026-10-25 用户纠正后）

纠正：此前仓库评估停在粗略目录／README层，没有继续消费已经完成的具体接口，导致重复开发。当前 YesMetaZFC 固定提交 039c8e132cc19671d73a3933c66b4799d2599dd6 已核对等于 EgoFakeFantasy/YesMetaZFC 远端 main；本轮不更新依赖、不改其他项目的脏工作区。

下表的“复用”包括定义、已证算法、原核证明和终局装配方式；不能因配套证明位于模型命名空间就把整组资产丢弃，也不能把它的背景或量词悄悄改成最终目标。

| 现成资产 | 精确入口 | 本工程的处理 |
|---|---|---|
| 集合结构满足关系、公式阶段、赋值压栈及对象定义规格 | FormalSystem/TarskiTruth.lean 的 formula_satisfaction_condition、assignment_update_condition、formula_satisfaction_semantics_theory | 撤掉本轮重复的 SetSatisfactionRow；先消费既有定义及配套，仅核对到纯ZF的支撑消去 |
| 完整公式识别与实际解码 | Automation/ObjectFormulaSound.lean:239，ObjectFormulaSyntax.checked_decode | 不重做识别／解码链；核对纯签名嵌入与目标理论参数 |
| 四种语法变换、27类逻辑公理 | ObjectSyntaxTransformSpec.checked_iff；ObjectLogicalAxiomSpec.checked_decode_iff | 直接消费现成规则图，不再逐标签复刻程序 |
| 六规则节点、整树证明图与 quotation | ObjectProofNode.ofNodeTest；ReducedProofPresentation.presentation | 使用通用构造，只提供本任务公理测试及所需背景证书；不要求无效外壳逐值等于另一算法 |
| 支撑语言消去、裸理论对象可证明性与一致性公式 | PureSentenceTransfer.derives_iff_m；PureProvability.provable_m／consistency_m | 复用装配和消去方法；具体ZFC实例不得冒名为ZF／U的证明谓词 |
| 全部内部码上的图／规范扩张对应 | PureSourceLocalTests.codeProof_agreement、provableCode_agreement | 复用同一族局部测试和模型回传；不把逐标准 numeral 的正确性误当作这项完整对应 |
| 纯成员语言的固定公平调度与强完备性 | PureRosserSchedule.target；Completeness.strong_completeness | 直接使用，不重写调度。可对任意纯理论T从所有Type 0模型中的同一句子返回原 Derives T [] φ；不要求T为ZFC |
| 其他项目的原核收尾 | BMS SecondOrderCompleteness.derives_m、PowerlessBMSNonemptyTransfer.derives_m、SecondOrderHereditaryBMSWellOrder.derives_m | 复用“逐模型消去全部实际候选前提，再经原完备性回传”的闭合方式。背景／签名／universe须对应，不复制BMS结论或额外公理 |
| 已有 L／Def／Gödel运算与逐公式编译 | 本地 lean-constructible-universe-stage4 的 FormulaGodel、RudimentaryConstructible、CodedSatisfaction、LStageZF、BasicAxioms、Choice | 使用已完成的构造和证明路线，不再到外部项目重建L。只补其实际语言与原ZF推导接口之间的桥 |
| 已有集合Sat支持条件与有限纯公式 | IBLP 的 SetSatisfaction、SetSatisfactionFormula；BMS 的 PowerlessSourceCompilation | 复用已编码的赋值、支持与公式迁移，不再新造同类语法／递归后端 |

YesMetaZFC 文件相对于 `.lake/packages/YesMetaZFC/YesMetaZFC/`。BMS 本地已核对源码位于 `../bms-publish-20260928/ConstructibleBridge/BMSConstructibleBridge/`；现行最终 derives_m 另已从所连接 GitHub 仓库核对。构造L的本地项目位于工作区根的 `lean-constructible-universe-stage4/`；有scope差异的终局模块不能直接改名当作本项目主定理。

本轮撤回的重复候选在 `.local/superseded-set-satisfaction-20261025/`，源文件与恢复副本 SHA-256 一致，未接入PPAC／正式审计／验收状态。已完成一次定向编译不使它成为需要保留的新主线。

现有语法／证明图资产已经完成；接下来的工作必须是选定这些接口后的ZF／U公理测试、背景消去、语言对应或实际数学证明传输。新增基础模块前必须先给出具体接口不适用的类型／前提证据，不能再以“对象层需要”为理由从头重建。

## 当前可直接消费的接口

- `ModelTransfer.project_models_iff` 精确连接任意 nativeZF 模型与 Project ZF；`derives` 直接消费原强完备性和既有调度。BMS 收尾方法已适配，不待重造。
- `DefinableMinimaChoice`、`InternalWellOrderChoice` 已取得 `Min_lt → AC` 和 `CoverWO → AC` 的原核证书。原 L 工程的最小元证明路线已经复用；实际 L 域满足其前提仍要通过精确对象接口接入。
- `KuratowskiZF` 复用底座配对约定；`InterpretedZF` 复用全部 ZF 模式回放。后者保留相对化背景和域非空条件，不冒充 nativeZF 已证明全部 L 公理。
- 本轮 `ForcingPairInduction` 消费已有 `ForcingMapLaws.formula_induction` 两次，构造对称加强谓词，取得左／右／交换下降的原核归纳模式。源依据是固定 `AtomicForcing.pairLower_left/right/swap`；本批实际消费者为 `ForcingAtomicGraphs.compatible` 和 `ForcingAtomicRecursion.exists_value`，不再列为待接的归纳接口。不是新的良基或递归后端。

2026-10-26 再审核实读：固定底座 Axioms/ZF.lean 的两个模式构造器；本仓 ReverseZFReplay、CollectionFromReplacement、ModelTransfer；L 工程 ZFModel、Model、StageHistoryGraphSystem；BMS SecondOrderCompleteness。未重新编译这些外部仓库，也未修改其源码。旧重复段落可从 Git `3deb896` 恢复。

本批原子递归直接消费固定底座 `SetTheory/Collection.lean:69 collection_exists_d`。既有 `ForcingMapConditions.binary_semantics` 连接原 Source 矩阵与底座 Project 二元模式；Collection 的非精确见证族经已有 Separation 过滤后取 Union。源码 SHA 锁入 SOURCE_LOCK。初次从 CollectionSyntax.core 展开整个复杂矩阵造成化简超时，已改用这个现成语义入口，无需扩大 heartbeat 或重建 Collection。底座和其他仓库均未修改。

ForcingAtomicBasic 直接消费原子递归方程和既有 Child 归纳；只把源 Preorder 的自反／传递条件翻译成同一 Source 关系 R 的对象前提，没有新造序理论。固定底座 Project/Order 的既有接口包含严格序等条件，不能把严格偏序直接冒作源非严格 Preorder。ForcingTripleInduction 使用六个标准公式置换，加强三个 Child 归纳的谓词；实际消费于 ForcingAtomicLaws.atomic_laws 的原四个递归分支。八类证书沿用 ModelTransfer，未重建完备性或递归核。
