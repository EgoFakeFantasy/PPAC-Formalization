# 现成接口复用与精确边界（2026-10-26 重审）

本表取代重复的逐批进度叙述；旧验收段可从 Git `629b815` 恢复。固定 YesMetaZFC 为 `039c8e132cc19671d73a3933c66b4799d2599dd6`，本轮未更新活动依赖或修改供体源码；另核对了新版 YesMetaZFC 7979336，见下文。源码位置与依赖指纹以 SOURCE_LOCK 为准。

| 已有资产 | 精确入口／本仓实际消费者 | 正确状态和边界 |
|---|---|---|
| 完整 ZF 模式 | YesMetaZFC/SetTheory/Axioms/ZF.lean 的任意参数 separation/collection；ReverseZFReplay、CollectionFromReplacement | 已完成并消费，不能再报为数学缺口 |
| 集合配对、并、插入、积、分离、收集 | KP.exists_pair/exists_union/exists_insert、ZF.exists_cartesianProduct、Collection.collection_exists_d；KuratowskiZF、ForcingNames、ForcingAtomicRecursion、ForcingHS | 已消费。内部 Collection 见证族经 Separation 过滤再合并；不抽取对象选择函数 |
| 内部序数递归 | SetTheory/Ord/Recursion.lean:1297 recursiveSequence_exists、1322 recursionValue_exists、1339 transfiniteRecursion_isClassFunctionOnOrdinals；GodelDefRecursion、ConstructibleHistory | 已消费全部内部序数接口。另一个 WellFounded.Recursion.solve 要求宿主 WellFounded，不能用于任意可能外部不良基的 nativeZF 模型 |
| 集合／名字归纳与递归 | SetInduction.native_induction → ForcingNameInduction/ForcingMapLaws → ForcingPairInduction/ForcingTripleInduction；ForcingNameRecursion | 已消费到名字、映射、原子递归和定律；后两种归纳有实际证明消费者，不是待重建后端 |
| 内部函数空间 | FunctionSpaceConstruction.lean 的 ZF.exists_functionSpace；ForcingLabelPermutations.exists_carrier | 本轮直接消费其全部内部函数图集合，再分离置换；没有重建幂集／积或函数空间。固定源文件哈希纳入 SOURCE_LOCK |
| 条件图构造 | SetTheory/FunctionConstruction.lean 的实际恒等、逆、复合图入口；ForcingConditionGraphs/ForcingConditionAction | 已消费，保留指定图的精确边方程。固定载体的统一标签作用、逆与共轭已接入；原 omega/2 已特化；源单子/conical 合同下偏序已接通；具体单子构造仍属阶段 8 |
| 原核收尾 | BMS SecondOrderCompleteness.derives_m 的 strong_completeness 模式；本仓 ModelTransfer.derives/project_models_iff | 已接入纯成员语言、对应 Type 0 全模型。不是待重做的完备性；本批 L 相对化已核对任意同一 universe 模型的前提，不拿单个 LCarrier 替代 |
| 旧 LCarrier 工程的完整模型数学 | lean-constructible-universe-stage4 固定 7f5a7d0；ZFModel.lean:28 lCarrier_models_ZF、StageHistoryGraphSystem.lean:171 lCarrier_models_ZFC | 该旧工程已完成完整模式，但 LCarrier 是 ZFSet 子类。这个限制不能概括新版 YesMetaZFC：其任意 ZF 模型的内部 L 定理已存在，见下一行 |
| 新版原生 L 数学 | 供体 7979336 的 l_model_zf_l／l_model_zfc_l／js_l_model_l；现由 PPAC/Companion 必要闭包及 ConstructibleGround.relative／zfc_axiom_kernel／global_order_kernel／nonempty_kernel 消费 | 固定旧版 039c8e1 编译通过并实际取得 nativeZF 中全部原生 ZF/ZFC 公理／模式、Choice、L 内全局序和非空的相对化原核证书。140 份数学正文不变；源域公式和解释背景消费本批也已验收，内部 Con 仍未完成。不能再报版本适配、原生／源全模式解释未完成；GCH 非本项目义务 |
| L 的实际语法／递归与选择收尾 | 原 FormulaGodel、RudimentaryConstructible、BareStageHistory；本仓 GodelDefOutput/Recursion、ConstructibleHistory/Parameters、InternalWellOrderChoice | 已有构造被复用。Min_lt/CoverWO→AC 已证；本批改为直接消费完整原生内部 L/ZFC 与全局序，不再把旧局部入口当前提。具体源域公式消费已由 ConstructibleSource 接通 |
| 全模式相对化传输 | InterpretedZF.source_sentence/native_sentence/project_axiom/collection；Relativization、ReverseZFReplay | ConstructibleSource.replay／nonempty_kernel 现已实际消去同一 L 的解释背景／非空前提，取得源全模式与 Choice 的原核 L 相对化；标准证书变换不是全部内部 Proof/Con |

当前第 8 阶段的唯一后继接口为 ConstructionRoundSelection：在同一实际 L 内，直接消费既有完整 probe_step／merger_step，以原 Kuratowski 配对打包九个字段；现成 Jensen 全局序的集合初段、KP.exists_insert 与 ZF.separation_exists_d 选出整个候选元组的最小者。无候选输入取 zero，因此对全部输入唯一且总定义；原完整父输入保证候选存在并保留原请求见证／fromBase。没有添加对象全局选择公理或通用选择后端。ConstructionTowerSuccessor 现实际消费同一选中元组，以现成 function composition／functionalImage／set-function constructor 构造全部旧阶段的新腿族；完整 MapFields、profile、Stable 和原有 fromBase 自然性同步传输，旧当前腿为恒等时新图精确等于 O。原生 IsSequenceOfLength.exists_append 又实际追加载体行和新阶段自身的恒等腿，close_extended 在同一选中输出上调用两者。没有复建 graph insertion／递归后端。ConstructionTowerLimit 又直接消费完整加权 colimit，在同一对象／同一 K 上取得完整 FullLegs／ProfileLegs、实际唯一 fromBase 和全部三角交换；只取一个已有阶段见证后用原生复合，旧 directedness／OriginNatural／K Stable 证明各阶段所得像一致，没有逐元素选择。加权通用性质、规范商／投影、原条件式基数结论均保留。PersistentProfile 的 mapped 现补上源函数类型所要求的 MapsTo；旧的边对应本身容许非关系杂项，会使全称 hP 过强。两个旧消费者已有所需 MapsTo，typed_profile 原核端点现从真实 transition Profiles 导出 hP。真实历史／规范数据包单值性、其余字段与转移表、原生递归及全塔时间仍须装配，不能写成完整塔已完成。

## 内部证明码：复用现有配套，不重建

以下均为固定底座已有接口。当前剩余义务是为 ZF/U 实例化并消去实际背景，不能把已有 ZFC 特化的结论直接改名。

| 现成入口 | 对本工程的用途 |
|---|---|
| FormalSystem/TarskiTruth 的 formula_satisfaction_condition、assignment_update_condition、formula_satisfaction_semantics_theory | 现有集合结构满足关系及赋值配套；不用重复 SetSatisfactionRow。它不等于全宇宙统一真值谓词 |
| ObjectFormulaSyntax.checked_decode；ObjectSyntaxTransformSpec.checked_iff；ObjectLogicalAxiomSpec.checked_decode_iff | 公式识别、四种语法变换、27 类逻辑公理，复用原图与正确性 |
| ObjectProofNode.ofNodeTest；ReducedProofPresentation.presentation | 六规则节点、整树证明图；本任务只补实际理论公理测试与背景证书 |
| PureSentenceTransfer.derives_iff_m；PureProvability.provable_m/consistency_m | 支撑语言消去和对象一致性装配；原 ZFC 实例不冒名为 ZF/U |
| PureSourceLocalTests.codeProof_agreement/provableCode_agreement | 全部内部码的正确性方法，不用逐标准 numeral 证明替代 |
| PureRosserSchedule.target；Completeness.strong_completeness | 原公平调度和原核回传，已经用于 ModelTransfer |

IBLP 的 SetSatisfaction/SetSatisfactionFormula 和 BMS 的 PowerlessSourceCompilation 是可参考的已有集合 Sat 与公式迁移代码；其具体背景和语言须对应，不从目录名推断能直接导入。已撤回重复的 SetSatisfactionRow，未接入正式入口。不得恢复用户退役的反射实现。

## 实际源消费者与复用裁决

| OpenAI 原证明链 | 本仓已完成的复用与迁移 | 仍需接入 |
|---|---|---|
| AtomicForcing.relations/atomic_laws/atomic_symmetry → SymmetricNames.atomic/atomic_regular | 现有名字递归、二／三名字归纳、原子方程及定律、实际条件图作用 | 具体 PPAC 条件呈现 |
| Force/force_of_dense → forcing_sound | 固定公式、19 规则的固定证明保真，原核模式证书 | 任意内部证明码归约归阶段 10 |
| Name.HS.smul → forces_symmetry | 字面稳定子、实际 HS 定义、Child 归纳、共轭传输；通用 HS 作用及公式对称性已完成 | 本批以具体统一 A、实际支撑滤子构造 Context 并消费 HS.smul；本批具体作用族的 HS 域公式对称性已接通；完整单子/偏序系统仍待装配 |
| SupportFilter.inf_mem/isNormalFilter → ProductNames.system | 固定底座函数空间、幂集、分离；新版 Card/Omega/InfiniteBound 五段原证明正文；实际小支撑族与四项正规性 | 已接统一条件作用和支撑滤子 Context；bot_not_mem 按 ChoiceFailure 消费者处理，完整系统仍待装配 |
| Diagram.sub/permuteOrderIso → ProductForcing.permuteOrderIso → ProductNames.actionHom | ForcingDiagramCarrier/Order 直接调用原函数空间、分离、可定义函数和复合；消费既有 Injection/CompositionGraph/标签作用。构造整张子图、实际载体与关系自同构，集合级作用律已证 | 单子代数律和 conical 条件由原阶段 8 构造提供；已接 Cohen 群律、Product 与 WithTop 扩展；统一标签作用族及支撑滤子 Context 本批已接入。任意乘法表的平移关系不变性不冒充偏序存在 |
| Cohen coordinatePerm/permute/permuteOrderIso → ProductForcing.permuteOrderIso | 原积／函数构造、幂集／分离、既有 exists_image/small_image；实际条件载体和保序双射装配完成 | B=2、w=ω 已由 ProductParameters 消费已有构造；跨标签作用律、Product 与 WithTop 扩展已有；统一作用族已接通，源 omega/2 参数已接通，一般源代数合同下的偏序已接入，具体单子构造仍待阶段 8 |
| ProductNames.Poset/actionHom.withTopCongr | ForcingWithTopCarrier/Action：直接消费 KP.exists_empty/exists_singleton、ZF.exists_powerSet、已有 Separation 和可定义函数；内部空集／singleton 编码，完整载体和扩展置换 | 逐个扩展及作用律已证明；本批统一 A、Family/Covariance、支撑滤子 Context 与 HS 作用已实现。源 omega/2 参数特化及实际 HS 域公式对称性已接通；源单子/conical 合同下偏序已由 ProductPoset 接入；具体单子构造仍待阶段 8 |

本批参数特化与具体公式对称性的 2 项原核证书依赖标准三项及七项已有基础句子 FreeClosed 证书。没有扩大此前活动可信基。此前正规滤子批次已消费的 15 项递归和 9 项基数 native Bool 证书仍保留记录及重算，不能改称整个工程仅有标准三项。

## 新版库的强迫合同核对

读查同一固定新版 7979336 的三个入口，源码哈希见 SOURCE_LOCK.companion_candidates.native_internal_forcing_contract_review；本批没有编译这些供体入口，也没有替换底座。

- `Internal.Npair_d / npair_l`：所有条件作权重的配对名字；源 pairName 是指定顶条件的两个边。存在语义用途，但不能原名替换后声称字面名字已对应。本仓已完成源 pairName，故不重做。
- `Internal.Aut_d / aut_bij_l`：内部条件双射及序／排除值保持。它没有给出源 ProductNames 的标签群具体作用；现有本仓条件图已经具备相应基础，继续复用它们。
- `Internal.preserves_zf_l`：对任意内部 ZF 模型，在 `Cond_order_d` 与 `Generic_d` 前提下证明完整泛滤商扩张满足 ZF。不是 HS 限制域的 ZF 定理，也不是对象内部 Con。不能为了套用该结论重开泛滤真值支线。

## 不能重复建设或误报的部分

新版 L 的域是任意 M 内的 `{x : M.Domain // L_d x}`；完整 ZF/ZFC 已有。223 模块依赖差异是版本整合工作量证据，不是 142 项未证明数学；GCH 不增加为本项目义务。BMS 完备性回传方法已在 ModelTransfer 中应用，BMS 供体此前存在无关脏改动；本轮未修改。新版 YesMetaZFC 本轮确认干净。

既有全模式、内部序数递归、Proof/Sat 配套已经存在。ZF/U 特化和全部内部码正确性尚未接通，但不另建通用证明核、编码器或满足关系。其他库接口未定位时写“未定位到精确合同”，不能写“数学不存在”。

`atomic_truth`、决策稠密集、`exists_truth_generic` 仅服务未选的泛滤分支；NatPacket／字节兼容继续冻结。旧的独立 L 重建路线停止扩写。保留具有实际依赖或尚未完成裁剪判断的已验收证明；不以已投入成本作为继续开发理由。


## 现行代数构造复用入口

下表只保留当前可调用入口及边界；逐批过程记录由 Git 保留。源声明、所选供体正文哈希和精确依赖见 SOURCE_LOCK；已迁移结论见 THEOREM_COVERAGE，实际验收见 STATUS。

| 当前消费者 | 已实际复用的入口 | 边界 |
|---|---|---|
| 全部强迫 ZF 模式 | Collection.collection_exists_d、Replacement.exists_functionalImage、SeparationSyntax；既有 HS、轨道和支撑图 | 前端已证；最终具体单子／呈现待实例化 |
| Base.M 和初始 margin | 固定底座 Ord/Natural、Arithmetic、NaturalPrime；新版 Descriptive/Dyadic 方法；本仓 ConstructionRealCuts.bounded_union、ConstructionCutWeights.exists_bounded_weights | 初始 Base 已证；后继 margin 未接通。不扩建消费者不需要的实数域；RealPair 不是实数域 |
| Probe Path、商字母与字母模拟 | 原生 FunctionConstruction、Replacement、Separation；Representatives；exists_factor_table/exists_terminal_table；letter_eq_iff、transition_total/unique、inCone_letter_iff | factor/terminal、共同阶段商、动作、target/exit、AlphabetSimulation 已证。不增加过渡映射单射性 |
| 字母／Word 大小界 | ExistingCardinalBounds.infinite_product_l；原生 Comparison.exists_rightInverseInjection_of_surjection_from_ordinal；ExistingFiniteSequenceBounds.fseq_bound_l | 使用序数最小原像及全内部有限序列统一编号，不选商代表、不加可数选择。新版四段序列证明保留正文哈希 |
| Raw、Word、quotient、letterAct | 原生 FiniteSequenceParsing、序列限制、函数图；已有 raw_induction、IsOmega.induction | 所有内部有限长度，非宿主 List 或外部标准长度 |
| evalHom/liftHom 与呈现 | 原生 recursiveSequenceIn_existsUnique；ConstructionProbePresentedLift.existsUnique_presentedHom；ConstructionProbeIndexedGenerators.presentedHom_ext | 任意内部目标单子，不增加左消去条件；实际图、关系及唯一性已有 |
| 实际 Word、old 嵌入及条件并 | ConstructionProbeConditionalJoins.exists_extension；现成 raw_induction、实际乘法图、ForcingConditionGraphs.exists_identity 和共享 Gate | 同一 W/unit/J/G 及三项代数性质已构造；基础条件并仍是源前提，不能替代最终饱和单子 |
| 映射 Path 与 Raw/Word 传输 | ConstructionProbeMappedPath.exists_node_map → ZF.exists_compositionFunction；ZF.exists_restriction；现成序列长度、prefixHead/reduced 判据 | 实际像图和 Word 图已构造；没有重造序列、递归或商后端 |
| 完整保守模拟、old/probe 方程 | ConstructionProbeSimulation.exists_simulation；既有 raw_induction、head_transport_some、letterAct_injective、共享 gate、division_reflection | 同一个 H 上的四字段 Conservative 和端点方程已证；具体路径／字母合同保留 |
| 初始全 profile 与旧 profile 保持 | ConditionalJoins.exists_extension；Generator.exists_generator_graph；IndexedGenerators.exists_probe_graph；gate_dvd_old_iff/gate_old_intersection/gate_existence；exists_node_map | 一个实际后继扩张保持所有旧 profile；Merger 专用 factors_of_old/gates 尚待迁移 |
| 模拟 pushout | existsUnique_presentedHom、presentedHom_ext、exists_simulation、exists_node_map | 原核证书覆盖任意内部目标单子；Presentation 只打包具体图合同，未假定普遍性质。完整 Probe 装配仍待完成 |
| letterFloor 与高度像集 | ConstructionRealCuts.bounded_union；ZF.separation_exists_d / exists_setFunctionFromTo_of_denote；dvd_target_of_inCone、one_inCone | 已构造所有字母的实际图与上下界；旧高度正性／单调性保留。一般加法/max、正整数除法及 /4 四倍和已迁移；一般切割差本批已证，逐字母 intervals 已证，实际 heightIntervals 内部图本批已装配，不把上确界存在误报为完整 margin |
| Probe 锥内／锥外 cost 界 | 既有 FractionAddition.Sum／sum_right_lt_iff、Separation、ConditionalJoins、ConeLaws、floor 图及原核 ModelTransfer | 已有有界和切割及两界；一般旧 PointBound 输入保留，初始 Base 的该输入已由本批消去。原逐字母严格区间及实际 heightIntervals 三图均已有；完整 Word HeightCost 本批已接通，Path／Probe 装配仍待接通 |
| 初始 Base 的 PointBound | ConstructionBaseHeightGap.cut_gap/source_margin；ConstructionBaseCostBound.missing_cost_bound；原生自然数算术；既有实际图构造器 | 已在同一组图上保留完整严格 margin 并给出 PointBound；只做所需加法界适配，不重证 Base 或声称任意加法全等价 |
| 原区间的一般加法与 maximum | 已有 principal_add_bound / bound_inputs_mono / exists_bounded_sum、cuts_total、笛卡尔积与可定义函数图 | 全 CutCarrier 加法图、非严格序性质／零定律和唯一 maximum 已构造；差值及加法严格序／相消本批已接，逐字母区间已证，heightIntervals 函数图本批已装配，不扩写成完整实数域 |
| 原区间的 /4 | ConstructionFractionDifference.scaled_equiv；既有 mul_swap/mul_le_iff；原生 Separation／可定义函数图；digits_exists | 正整数除法及实际四分之一图、正性和序反映已有；本批复用 same_den_sum、原生后继算术及除法序反映，接通实际四倍和恢复定律。字母区间及其三张内部函数图均已完成；分数及主切割差也已有，不再列为待做 |
| 全部对象层证书收尾 | 既有 ModelTransfer.derives/project_models_iff，复用 BMS 式原核 strong_completeness 路径 | 需所有对应 Type 0 模型的前提；不能用单个具体模型替代；没有另建完备性核 |

| 一般切割差／相消 | 原生 Separation、KP.mem_minimal_exists_d、IsOmega.exists_predecessor_of_mem_of_nonempty；既有分数差、same_den_sum、加法结合／序反映 | 内部网格逼近、一般差精确加回及所有切割解唯一性、加法包含／严格包含反映和相消均有本批原核证书。非标准内部指标不丢失；逐字母区间已证，heightIntervals 函数图本批已装配 |
| 原逐字母区间及统一成本界 | 既有差值、相消、max、/4、quarter_fourfold、cut_assoc；同一 F/H/C/K/E 图的 FloorLaws、CostBounds 与 MapsTo 唯一性 | 按原公式构造并证明两个严格区间和同一 K 的全部锥外成本界；保留旧 UniformMargins。Recipe 的三个输出对固定 C 唯一。本批已规范旧成本上确界并直接消费既有 native function constructor 构造三图，不引入内部选择函数假设 |
| HeightIntervals 的实际函数图 | 原生 Separation、exists_setFunctionFromTo_of_denote；已有 bounded_union、cap/recipe 唯一性、MapsTo；原生 le_iff 已用于本批初始 Base 旧 margin 适配 | 构造规范遗漏成本上确界和实际 offset/scale/outsideBound 三图；同一数据的所有源字段及实际差值 inside_cost 已接通。旧 uniform margin／floor/cost 输入保留，完整 Word margin 和原父输入 ProbeData 装配均已完成，直接由 ConstructionProbeParentSyntax 消费 |
| 已完成 Base margin 的表示适配 | 既有 source_margin、height_mono、le_iff、weights_bounded、base_point_bound；原生函数图构造器原已给出 MapsTo | PrincipalAdd→SumCut 已精确接通；保留原生 MapsTo 的新入口与旧 API 兼容。实际 Base 构造输出完整原 margin、HeightOrder、UniformMargins，初始这两个输入已消去；后继完整 Word margin 与 ProbeData 父输入装配已有原核证书，不再作为缺口 |

| 原 Raw/Word 所需乘法与 min | 原生 ordinalMultiplication 的总性／结合／交换／零方程；现有分数码与 mul_swap、dense、cuts_total；原生 Separation 与可定义函数图构造器 | 本批取得实际一般切割乘法图，交换／单调／零吸收及正性；min 的实际唯一值、界和正性。完整原核证书只使用现有可信依赖。乘法单位已由源高度／成本界实际消费；本批按 same-head 的实际需要接通分配和正仿射缩放；未扩建乘法结合／逆或完整域。成本估计和完整 Word 严格／上确界 margin 均已接通；Word 高度递归已接在下行，不扩建完整实数域；后继完整 HeightCost 已有实际原核证书 |

| 原 rawHeight／Word.height | 未修改的 ConstructionProbeHomEvaluation、HomEvaluationSyntax.exists_lift_graph；原生 exists_unionOfTwo／恒等图／函数构造；现成 HomExt.agreement 和 Raw.raw_induction | 仿射运算在 N=S∪R 上喂入现有总二元代数求值器；没有附加结合、消去或单子律。实际根步骤细化输出范围到 R，同一 Word 高度图满足精确 old/cons 方程，且整个图唯一。此项已接通，不再把高度图本身列作缺口；高度界、成本界和完整上确界／严格 margin 均已接通，且已经由 ProbeData 父输入生产者消费 |

| 原 OldMinimum／gateCap | 现成 PersistentProfiles.OldGate 的精确旧倍数轮廓；已有 LeftCancelMonoid／Conical；原生可定义函数构造与图外延性 | 实际唯一 cap 图、精确最小旧成本／默认 unit 分支、正性和非严格上界已证。没有重证门存在性，不选任意更大旧倍数，不强化所有词有门 |
| 原 rawCost／Word.cost／cost_bounds | 未修改的 evalHom／Word lift；上批 HeightFold.eval_range 根步骤范围细化；现成 Raw 公式归纳、agreement、一般乘积／min；原生状态图和函数构造 | 状态保持当前词的证明已完成，使用 cap(当前新词)；同一 Word 实际成本图具有原 old/cons 方程、整体唯一性及 0<cost≤unit。证书同时构造 cap，无 cap／成本图 oracle；单位 1 的切割表示由既有 Base 数据供给 |

本批 ConstructionProbeSuccessor.exists_probe_successor 已直接消费 exists_profile_extension、exists_conservative_old、initial_profile、exists_mapped_profile、extension_cardinal_le 和 exists_heightCost，在同一实际 W/G/O/HL/LC 上构造原请求与加权对象／inclusion 全字段；Syntax 提供纯成员原核证书。没有另建 Object/Hom 框架或重证 profile／基数／权重。ConstructionProbeParent 本批已从原父输入统一调用这些存在性生产者，并由现成 monoid/cut/uniform 定律给出 HeightOrder/PointBound 接口；父输入纯闭句的原核证书不再接收字母表／floor／interval。原 MergerData 父输入装配现亦已完成，后续消费者由当前流程统一给出。Base、heightIntervals、原算术、实际高度／cap／成本图、height_bounds、cost_bounds、cost_le_scale 和 cost_old_factor 均已有。只继续源消费者需要的估计及严格 margin，不重复这些构造，不新建通用递归、Proof/Sat 或完整实数域。

本轮复用复核：活动底座仍为 039c8e1，新版供体仍为 7979336，两者工作树干净。回读 Jensen/ZF/Model.lean:15 和 Jensen/ZF/Choice.lean:14，前提确为任意 M.Models ZF；不是 ZFSet 子类限制，也没有新增 L 证明任务。本轮不修改供体。新权重界直接消费已有 Raw 对象公式归纳、HeightFold/CostFold、interval 三图和 min 界；old-factor 直接抽取已有 EmbeddingLaws 字段和 HasOldGates，不重建 gate 或递归。

原 Gate/成本/margin 消费：ConstructionProbeCostMargins.minimum_of_gate 直接调用 gate_dvd_old_iff；cost_le_gate 复用既有 minimum 成本界；outside-block 因子使用现成 gate_existence、EmbeddingLaws，old–old 严格 margin 直接消费 cost_old_factor 和旧 UniformMargins。原核 Syntax 中调用这些既有生产者，消去 ExitGates／HasOldGates／EmbeddingLaws／Word 单子前提；仅保留原实际字母表、Word／乘法／旧嵌入、旧条件并与保守性、权重方程和旧 margin 输入。没有重做 Gate、嵌入、归纳或实数算术。

混合 margin／上确界批次：old–new 直接用既有 floor、inside_bounds、差值/max、cost_le_scale 和 outside-block 因子；new–old 直接调用原 generator 构造与 generator_dvd_of_head／generator_dvd_old_iff、旧 UniformMargins 和 cost_old_factor，等号分支取实际零切割。Word old_cost_supremum:515 复用现成 Family／Cap／exists_family／bounded_union／cap_unique，以旧成本不变嵌入和新成本的旧支配构造两边实际集合及公共唯一上确界；空集和无序端点不丢失。没有重建上确界设施，也没有增加域运算。

完整 Word HeightCost 批次：正有理缩放通过既有 ConstructionFractionScaling.Times/order_iff 和 scaled_equiv 取得，公共分母和 native mul_add 给出分配；严格切割缩放由已有差值、正乘积和加法序反映推出。same-head 直接消费现成 generator 乘法／left_mul_dvd_iff 和 old_factor_of_other_block。统一证明只调用既有 Raw 对象公式归纳，atTarget 同时量化被比较词和两个高度值，覆盖非标准内部长度。最后调用既有 canonical_uniform，为所有新严格比较构造实际 Cap 和严格间隙，精确对应 DiagramOrder.HeightCost.margin:67；没有重证上确界设施。

已完成的装配复用：ConstructionPersistentProfiles.exists_probe_successor:187 提供实际 W/unit/J/G/O、WordCarrier、MultiplicationGraph、左消去／conical／条件并、OldGraph／Conservative／HasOldGates 和全部旧 profile 映射保持。ConstructionProbeSuccessor 已组合它与 exists_heightCost；ConstructionProbeParent 已从原父输入消去所有辅助生产者前提。不得再次把此组合列作待做。

Merger 当前消费：ConstructionMergerRelations/Copies/Action 将固定原关系（不是传递闭包）实例化为已验收 ProbeLetters 的具体 class／投影构造模式，直接调用原生 Separation／functionalImage／setFunction；product-coded representatives 及 projected/indices/range 直接复用。右自由性是固定 copy 的旧因子单射性；不要求右消去或提供 action oracle。本批直接以 Raw.exists_carrier/Old/Cons 承担 Merger Word；构造器末尾追加正是 source snoc，此前倒序存储描述已纠正。Word 乘法复用未改 evalHom 的 total/unique/old/cons 及泛化的 HeightFold.eval_range，原生函数构造提供旧行／操作／乘法图。不重建序列／parser／基础归纳或通用递归。本批原 Word 单子律、左消去及 conical 已消费这些实际图和未改 Raw 对象公式归纳。长度取已有 sequence length_eq；加法取既有 Base 内部 ω 加法图／消去律和 native ordinalAddition_successor_iff，不新增算术／编码设施。本批已用既有 ConstructionProbeConditionalJoins.left_mul_dvd_iff、ConditionalJoins、JoinProperty，直接迁移源 residual／same-copy／overlap／copies_hasConeJoins；HasConeJoins 已作为同一实际生产者的结论进入原核闭句。Word.dvd_snoc_iff／snoc_cone_intersection／exists_cone_join 本批已接通；旧嵌入／根实现本批已有原核证书；下一消费者为源权重／基数界及完整加权 MergerData。

本批复用裁决：Probe 的 old_dvd_iff_headDiv 依赖特殊 Alphabet/Word 商，不能仅改名套入不同 Merger Word；其泛型 left_mul_dvd_iff 则只依赖 LeftCancelMonoid，已原样复用。Raw 已含旧系数及末尾追加，本批已按原 MergerWords.leading／dvd_snoc_iff 适配现有表示，以 oldDivAt/coneAt/joinAt 使用 Raw.raw_induction 完成旧整除及全部 Word 条件并；不新建序列解析、归纳或递归后端。

本批 Word 条件并实际复用：长度比较直接调用 ConstructionMergerWordLength.product_length 与 ConstructionBaseMonoid.le_iff；锥交和共同上界归纳使用未修改的 Raw 对象归纳；旧整除保留 Raw 中的实际旧系数；旧共同倍数／锥交保持供原 ConservativeExtensions.Word.oldHom_conservative 消费。新的同一载体生产者返回 ConditionalJoins W H，不接受该结论为前提。现成 ConstructionProbeConservative.Conservative、ConstructionPersistentProfiles.HasOldGates/exists_mapped_profile、ConstructionProbeLiftHom.PreservesProducts 都是泛型合同，本批旧嵌入已直接消费这些泛型合同。特殊 Probe WordCarrier 的 exists_old_graph 生产者没有被直接改名套用；本批用同一原生可定义函数构造模式适配实际 Merger Carrier。

本批旧嵌入／根实际消费：Conservative 四字段分别复用 Old 注入、factors_of_old、preserve_old_cone_intersection、old_common_multiple_iff；HasOldGates 直接给出 old 分支，不建额外 gate。所有旧 profile 调用未改 exists_mapped_profile，映射节点复用 native composition。根函数图由原生函数构造器、projected 与 Raw.exists_cons 组成；root*old 的字面式消费已有 CopyLaw 与 Word action/product laws，精确关系消费 copy_eq_iff，根新颖性消费 old_ne_cons。完整 Pure forall7 证书保留同一实际生产者数据，不另建 Object/Hom 框架。

当前 Merger 权重已消费既有任意正内部 n 的 ConstructionCutDivision.Value、实际坐标行、Raw evaluator 和 Cut sum/product 图。有限平均／min 乘积除法函数图、全部逐点界、copies 严格统一 margin／真实上确界、完整 copiesHeightCost／同一原父生产者均已有原核证书；不能再列为待实现。Word 实际字面权重及完整 HeightCost／实际上确界 margin、任意旧对成本族与上确界保持也已验收。Word margin 直接复用现成 atTarget／Raw 归纳、可除性分解、copies margin 和 canonical_uniform；没有新通用后端。snoc 的存在性见证用 room*quarter，源字面权重公式保持。当前真实状态见 STATUS。

Merger 基数界已直接复用 ConstructionProbeWordCardinality.raw_cardinal_le、ConstructionProbeCardinality.indexed_quotient_bound、原生 infinite_product_l 和 ConstructionMergerCopies.projection_onto，现有原核证书。ConstructionMergerParentSyntax 已组合同一原父生产者与完整 Word 权重，保留实际旧嵌入／所有 profile／根、指定非单位元、高度／成本／旧上确界及条件基数界；完整加权 MergerData 不再待装配。

下一直接消费者是 Request.target/inclusion 与 MonoidTowers.DirectedColimit，源 ConcreteSystem.T = Saturation.target Base.object K。本批已复用 coordinate_bound／Union／Cartesian／Separation、MergerCopies 精确类／functionalImage／函数图方法和 Kuratowski／product_unique，构造实际变动载体／共同后继等价类／同一投影／全部阶段函数图，并导出 of_map、条件 of_injective 与二／三元共同阶段表示；已有原核证书。没有以固定载体 Probe/omega 的 Letters 直接改名冒充任意变动阶段族。同一对象上的实际乘法／单位、结合律／左消去单子、条件 conical 和全部阶段实际单子同态现也已有原核证书：直接消费源实际阶段表、原左消去单子合同、共同后继相等、原生可定义函数构造器、product_unique 与现成 PreservesProducts。没有增加转移单射前提或新代数框架。源 of_factors／of_dvd_iff／of_conservative／conditionalJoins 现已完成：从原 hf 导出转移单射，实际共同后继取回指定右因子，原样复用 division_reflection；对任意极限元素构造比较阶段，使用原转移 intersections/common 和已导出整除反射证明所有阶段四字段 Conservative，随后由共同三元阶段给出极限条件并。没有添加极限保守性／HasOldGates 前提。源 probeProfile 现已完成：原 hP 显式保留所有后继阶段 profile，初始 profile 由实际恒等转移导出；任意极限元素经实际共同后继表示，在该阶段使用已完成的精确整除反射／四字段 Conservative；同一原节点图的复合交换由实际图和共同后继相等证明，直接复用 exists_node_map／ProbeProfile／NodeMap／divides_trans／product_unique。没有增加初始 profile、HasOldGates 或极限 profile 前提。实际高度／成本和完整 HeightCost 现也已完成：同一投影的源稳定性与共同后继相等证明值良定义，原生可定义函数构造器生成两张图；RangeBound／Bounds 给出四界；任意遗漏因子的实际共同后继及原 hSup 给出旧 Cap 上界，再由旧成本原样嵌入证明最小性。原样复用 Family／Cap／exists_family／bounded_union／cap_unique／canonical_uniform，覆盖所有旧对和空族，并给出实际严格 Cap margin。基数界及指定非单位元 Object／inclusion 现已装配：直接复用 YesMetaZFC 7979336 的六个 Choice／uniformize／union_bound 精确证明体，再用已有 indexed_quotient_bound／infinite_product_l 和阶段域值域／并集控制实际变动总和。对象选择只在源基数结论前件，不加入构造输入；所有阶段指定元像相等及非单位性直接使用共同后继、已验收单射和单位像。原 MonoidTowers.cocone／lift／isColimit 接口现亦已验收：ConstructionDirectedWeights.exists_graph 对任意目标集合的既有构造原样给出实际 lift；projection_equation／common_stage_pair／common_stage_three／stage_core／old_suprema／cap_unique／原生关系外延性给出完整 Hom、fac 和 uniq。既有 Replacement 加可定义函数构造器收集实际唯一阶段图族 K，所有规范 leg 字段作用在同一 K。ConstructionDirectedColimitSyntax 保留完整 Object 父输入和所有旧输出，内部量化全部目标 cocone 并构造唯一 lift；没有新增选择、类别或下降后端。两类请求参数映射现也已验收：Probe 原样复用 exists_node_map／mapped_path 和原生关系外延性，Merger 按原 valid_map_iff 的旧中间 join 证明，直接消费既有 factor_eq／Conservative.common/intersections／ConditionalJoins／rel_mul。原生 Cartesian／Separation 构造唯一实际 mapped start 图，缺失 start 不添加边，目标 Valid 不作为输入且覆盖全部新目标元素。本批已实际把这些映射数据喂给完整 ProbeParent／MergerParent，返回两类实际 Round.step 后继、原始基请求见证和同一个完整 fromBase；exists_node_map 的任意内部定义域已直接用于实际复合图，factor_eq／Cap 唯一性／原有 profile 方程接通所有 Hom 字段。ObjectFields／MapFields 仅缩写现成字段，原实际乘法图和所有旧 Cap 族不丢失。原生 Replacement 与可定义函数构造器已收集给定 Schedule 在任意内部 J／变动阶段上的唯一实际映射请求图；具体 Request 标签只复用 Kuratowski 对，不增 Proof 编码／parser。CompleteRounds 的全部 Request 集、默认 Probe、Request×K 加 top 的底层穷尽 Schedule／Place 单射现亦已验收：直接消费原生完整函数空间、PowerSet／Separation、既有 product／WithTop 和可定义函数构造器，规范部分表行且覆盖全部内部有限 n。调度的实际内部良序／规范序型及每个位置严格早于 top 现已由 ConstructionScheduleOrderSyntax 验收；直接复用新版 Choice.ordinal_enum_l、原生最小原像单射与 wellOrderType_existsUnique，源对象 Choice 显式保留。原 Hartogs 证明唯一自动化调用换为外延性，无新信任；并非新增枚举或递归数学。实际调度／位置图到该规范序型的传输现已由 ConstructionOrdinalScheduleSyntax 的完整原父输入端点验收：直接复用同一原生规范坍缩、逆／复合函数及既有 NodeMap，保留全部边方程和严格位置；真实末阶段 last 与后继成员方程也已构造。尚待原请求基数界及真实迭代塔，不能把现成递归库或给定塔合同当作实际塔。下一项是这些现成接口与已有内部 Ord.Recursion、完整后继／实际极限的实际塔接线；不能重建这些已完成的载体／乘法／单位。直接消费现成集合构造，不另建类别论或通用 quotient／递归后端。Placement/Hull 按已核对的具体消费者接入，不能按目录顺序扩写泛滤分支。

本批供体重用锁为 SOURCE_LOCK.companion_reuse.native_small_family_union；三份原文件 SHA、三个精确区块 SHA、六项声明全足迹以及实际消费者均记录。既有原 Axioms.choice、源 AC 对应已完成；本批 choice_semantics/models_zfc 仅接线。不能把一般小族并的源 ZFC 前提隐藏成 ZF 无条件结论，也不能把它加成极限对象构造前提。

本轮已实际完成此前兼容核对之后的接线：223 模块闭包中旧版已有 81 个，其余 142 项用 140 份只改导入的数学正文及 2 项既有实现重定向解决。140 个模块和 2818 项公开／生成声明均已正式验收，无新增信任；SOURCE_LOCK 锚定 L_REUSE_LOCK 的所有源码、去导入正文及精确足迹。活动依赖和供体均未修改，未读取退役反射归档。源域公式消费本批已验收；全部内部 Proof/Con 仍是实际未完项。
