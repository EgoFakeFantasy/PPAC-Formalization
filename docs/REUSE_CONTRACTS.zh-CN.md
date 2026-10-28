# 现成接口复用与精确边界（2026-10-28 复核）

本表取代重复的逐批进度叙述；旧验收段可从 Git `629b815` 恢复。固定 YesMetaZFC 为 `039c8e132cc19671d73a3933c66b4799d2599dd6`，本轮未更新活动依赖或修改供体源码；另核对了新版 YesMetaZFC 7979336，见下文。源码位置与依赖指纹以 SOURCE_LOCK 为准。

| 已有资产 | 精确入口／本仓实际消费者 | 正确状态和边界 |
|---|---|---|
| 完整 ZF 模式 | YesMetaZFC/SetTheory/Axioms/ZF.lean 的任意参数 separation/collection；ReverseZFReplay、CollectionFromReplacement | 已完成并消费，不能再报为数学缺口 |
| 集合配对、并、插入、积、分离、收集 | KP.exists_pair/exists_union/exists_insert、ZF.exists_cartesianProduct、Collection.collection_exists_d；KuratowskiZF、ForcingNames、ForcingAtomicRecursion、ForcingHS | 已消费。内部 Collection 见证族经 Separation 过滤再合并；不抽取对象选择函数 |
| 内部序数递归 | SetTheory/Ord/Recursion.lean:1297 recursiveSequence_exists、1322 recursionValue_exists、1339 transfiniteRecursion_isClassFunctionOnOrdinals；GodelDefRecursion、ConstructibleHistory | 已消费全部内部序数接口。另一个 WellFounded.Recursion.solve 要求宿主 WellFounded，不能用于任意可能外部不良基的 nativeZF 模型 |
| 集合／名字归纳与递归 | SetInduction.native_induction → ForcingNameInduction/ForcingMapLaws → ForcingPairInduction/ForcingTripleInduction；ForcingNameRecursion | 已消费到名字、映射、原子递归和定律；后两种归纳有实际证明消费者，不是待重建后端 |
| 内部函数空间 | FunctionSpaceConstruction.lean 的 ZF.exists_functionSpace；ForcingLabelPermutations.exists_carrier | 本轮直接消费其全部内部函数图集合，再分离置换；没有重建幂集／积或函数空间。固定源文件哈希纳入 SOURCE_LOCK |
| 条件图构造 | SetTheory/FunctionConstruction.lean 的实际恒等、逆、复合图入口；ForcingConditionGraphs/ForcingConditionAction | 已消费，保留指定图的精确边方程。固定载体的统一标签作用、逆与共轭已接入；原 omega/2 已特化；源单子/conical 合同下偏序已接通；具体 Base/T 已完成；实际模型系统消费者仍属阶段 8–9 |
| 原核收尾 | BMS SecondOrderCompleteness.derives_m 的 strong_completeness 模式；本仓 ModelTransfer.derives/project_models_iff | 已接入纯成员语言、对应 Type 0 全模型。不是待重做的完备性；本批 L 相对化已核对任意同一 universe 模型的前提，不拿单个 LCarrier 替代 |
| 旧 LCarrier 工程的完整模型数学 | lean-constructible-universe-stage4 固定 7f5a7d0；ZFModel.lean:28 lCarrier_models_ZF、StageHistoryGraphSystem.lean:171 lCarrier_models_ZFC | 该旧工程已完成完整模式，但 LCarrier 是 ZFSet 子类。这个限制不能概括新版 YesMetaZFC：其任意 ZF 模型的内部 L 定理已存在，见下一行 |
| 新版原生 L 数学 | 供体 7979336 的 l_model_zf_l／l_model_zfc_l／js_l_model_l；现由 PPAC/Companion 必要闭包及 ConstructibleGround.relative／zfc_axiom_kernel／global_order_kernel／nonempty_kernel 消费 | 固定旧版 039c8e1 编译通过并实际取得 nativeZF 中全部原生 ZF/ZFC 公理／模式、Choice、L 内全局序和非空的相对化原核证书。140 份数学正文不变；源域公式和解释背景消费本批也已验收，内部 Con 仍未完成。不能再报版本适配、原生／源全模式解释未完成；GCH 非本项目义务 |
| L 的实际语法／递归与选择收尾 | 原 FormulaGodel、RudimentaryConstructible、BareStageHistory；本仓 GodelDefOutput/Recursion、ConstructibleHistory/Parameters、InternalWellOrderChoice | 已有构造被复用。Min_lt/CoverWO→AC 已证；本批改为直接消费完整原生内部 L/ZFC 与全局序，不再把旧局部入口当前提。具体源域公式消费已由 ConstructibleSource 接通 |
| 全模式相对化传输 | InterpretedZF.source_sentence/native_sentence/project_axiom/collection；Relativization、ReverseZFReplay | ConstructibleSource.replay／nonempty_kernel 现已实际消去同一 L 的解释背景／非空前提，取得源全模式与 Choice 的原核 L 相对化；标准证书变换不是全部内部 Proof/Con |

当前第 8 阶段已复用原生配对／集合函数／复合／分离／内部序数递归和原 L 全局序，取得实际完整有效有界单轮塔及全转移表；九字段记录、实际选中 raw/Picked/Pack、强新鲜性、完整来源及后续切片精确锥均保留。ConstructionCompleteRound 现从原父输入调用现成 RequestCarrier、bounded schedule、bounded tower、Execution／ProbeFamily／ProbeIndependence，生成同一 last 目标／inclusion、准确 Place 到 K 重索引、完整所有请求见证和大小界。没有新建选择／序数／编码／递归后端；实际唯一整轮后继和完整 Valid/AllSmall 追加保持现也已完成；统一外层全历史总唯一算子、实际原生递归、完整Valid/AllSmall、全表／21合同／精确相邻图也已验收；具体ω₁+1／基数参数实例化和覆盖／饱和系统也已完成；下一真实消费者为 CellTowers／纤维粘合。

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
| Name.HS.smul → forces_symmetry | 字面稳定子、实际 HS 定义、Child 归纳、共轭传输；通用 HS 作用及公式对称性已完成 | 本批以具体统一 A、实际支撑滤子构造 Context 并消费 HS.smul；本批具体作用族的 HS 域公式对称性已接通；完整 Base/T 与偏序律已有；实际模型系统装配仍待接入 |
| SupportFilter.inf_mem/isNormalFilter → ProductNames.system | 固定底座函数空间、幂集、分离；新版 Card/Omega/InfiniteBound 五段原证明正文；实际小支撑族与四项正规性 | 已接统一条件作用和支撑滤子 Context；bot_not_mem 按 ChoiceFailure 消费者处理，完整系统仍待装配 |
| Diagram.sub/permuteOrderIso → ProductForcing.permuteOrderIso → ProductNames.actionHom | ForcingDiagramCarrier/Order 直接调用原函数空间、分离、可定义函数和复合；消费既有 Injection/CompositionGraph/标签作用。构造整张子图、实际载体与关系自同构，集合级作用律已证 | 单子代数律和 conical 条件由原阶段 8 构造提供；已接 Cohen 群律、Product 与 WithTop 扩展；统一标签作用族及支撑滤子 Context 本批已接入。任意乘法表的平移关系不变性不冒充偏序存在 |
| Cohen coordinatePerm/permute/permuteOrderIso → ProductForcing.permuteOrderIso | 原积／函数构造、幂集／分离、既有 exists_image/small_image；实际条件载体和保序双射装配完成 | B=2、w=ω 已由 ProductParameters 消费已有构造；跨标签作用律、Product 与 WithTop 扩展已有；统一作用族已接通，源 omega/2 参数已接通，一般源代数合同下的偏序已接入，具体 Base/T 已完成；实际模型系统装配仍待接入 |
| ProductNames.Poset/actionHom.withTopCongr | ForcingWithTopCarrier/Action：直接消费 KP.exists_empty/exists_singleton、ZF.exists_powerSet、已有 Separation 和可定义函数；内部空集／singleton 编码，完整载体和扩展置换 | 逐个扩展及作用律已证明；本批统一 A、Family/Covariance、支撑滤子 Context 与 HS 作用已实现。源 omega/2 参数特化及实际 HS 域公式对称性已接通；源单子/conical 合同下偏序已由 ProductPoset 接入；具体 Base/T 已完成；实际模型系统装配仍待接入 |

本批参数特化与具体公式对称性的 2 项原核证书依赖标准三项及七项已有基础句子 FreeClosed 证书。没有扩大此前活动可信基。此前正规滤子批次已消费的 15 项递归和 9 项基数 native Bool 证书仍保留记录及重算，不能改称整个工程仅有标准三项。

## 新版库的强迫合同核对

读查同一固定新版 7979336 的三个入口，源码哈希见 SOURCE_LOCK.companion_candidates.native_internal_forcing_contract_review；本批没有编译这些供体入口，也没有替换底座。

- `Internal.Npair_d / npair_l`：所有条件作权重的配对名字；源 pairName 是指定顶条件的两个边。存在语义用途，但不能原名替换后声称字面名字已对应。本仓已完成源 pairName，故不重做。
- `Internal.Aut_d / aut_bij_l`：内部条件双射及序／排除值保持。它没有给出源 ProductNames 的标签群具体作用；现有本仓条件图已经具备相应基础，继续复用它们。
- `Internal.preserves_zf_l`：对任意内部 ZF 模型，在 `Cond_order_d` 与 `Generic_d` 前提下证明完整泛滤商扩张满足 ZF。不是 HS 限制域的 ZF 定理，也不是对象内部 Con。不能为了套用该结论重开泛滤真值支线。

## 不能重复建设或误报的部分

新版 L 的域是任意 M 内的 `{x : M.Domain // L_d x}`；完整 ZF/ZFC 已有。223 模块依赖差异是版本整合工作量证据，不是 142 项未证明数学；GCH 不增加为本项目义务。BMS 完备性回传方法已在 ModelTransfer 中应用，BMS 供体此前存在无关脏改动；本轮未修改。新版 YesMetaZFC 本轮确认干净。

既有全模式、内部序数递归、Proof/Sat 配套已经存在。ZF/U 特化和全部内部码正确性尚未接通，但不另建通用证明核、编码器或满足关系。其他库接口未定位时写“未定位到精确合同”，不能写“数学不存在”。

`atomic_truth`、决策稠密集、`exists_truth_generic` 仅服务未选的泛滤分支；NatPacket／reader 已按用户批准的精确清单退役。旧的独立 L 重建路线停止扩写。保留具有实际依赖或尚未完成裁剪判断的已验收证明；不以已投入成本作为继续开发理由。


## 现行代数构造复用入口

下表只保留当前可调用入口及边界；逐批过程记录由 Git 保留。源声明、所选供体正文哈希和精确依赖见 SOURCE_LOCK；已迁移结论见 THEOREM_COVERAGE，实际验收见 STATUS。

| 当前消费者 | 已实际复用的入口 | 边界 |
|---|---|---|
| 全部强迫 ZF 模式 | Collection.collection_exists_d、Replacement.exists_functionalImage、SeparationSyntax；既有 HS、轨道和支撑图 | 前端已证；最终具体单子／呈现待实例化 |
| Base.M 和初始 margin | 固定底座 Ord/Natural、Arithmetic、NaturalPrime；新版 Descriptive/Dyadic 方法；本仓 ConstructionRealCuts.bounded_union、ConstructionCutWeights.exists_bounded_weights | 初始 Base 及完整 Probe/Merger 后继 margin／权重装配均已完成。不扩建消费者不需要的实数域；RealPair 不是实数域 |
| Probe Path、商字母与字母模拟 | 原生 FunctionConstruction、Replacement、Separation；Representatives；exists_factor_table/exists_terminal_table；letter_eq_iff、transition_total/unique、inCone_letter_iff | factor/terminal、共同阶段商、动作、target/exit、AlphabetSimulation 已证。不增加过渡映射单射性 |
| 字母／Word 大小界 | ExistingCardinalBounds.infinite_product_l；原生 Comparison.exists_rightInverseInjection_of_surjection_from_ordinal；ExistingFiniteSequenceBounds.fseq_bound_l | 使用序数最小原像及全内部有限序列统一编号，不选商代表、不加可数选择。新版四段序列证明保留正文哈希 |
| Raw、Word、quotient、letterAct | 原生 FiniteSequenceParsing、序列限制、函数图；已有 raw_induction、IsOmega.induction | 所有内部有限长度，非宿主 List 或外部标准长度 |
| evalHom/liftHom 与呈现 | 原生 recursiveSequenceIn_existsUnique；ConstructionProbePresentedLift.existsUnique_presentedHom；ConstructionProbeIndexedGenerators.presentedHom_ext | 任意内部目标单子，不增加左消去条件；实际图、关系及唯一性已有 |
| 实际 Word、old 嵌入及条件并 | ConstructionProbeConditionalJoins.exists_extension；现成 raw_induction、实际乘法图、ForcingConditionGraphs.exists_identity 和共享 Gate | 同一 W/unit/J/G 及三项代数性质已构造；基础条件并仍是源前提，不能替代最终饱和单子 |
| 映射 Path 与 Raw/Word 传输 | ConstructionProbeMappedPath.exists_node_map → ZF.exists_compositionFunction；ZF.exists_restriction；现成序列长度、prefixHead/reduced 判据 | 实际像图和 Word 图已构造；没有重造序列、递归或商后端 |
| 完整保守模拟、old/probe 方程 | ConstructionProbeSimulation.exists_simulation；既有 raw_induction、head_transport_some、letterAct_injective、共享 gate、division_reflection | 同一个 H 上的四字段 Conservative 和端点方程已证；具体路径／字母合同保留 |
| 初始全 profile 与旧 profile 保持 | ConditionalJoins.exists_extension；Generator.exists_generator_graph；IndexedGenerators.exists_probe_graph；gate_dvd_old_iff/gate_old_intersection/gate_existence；exists_node_map | 一个实际后继扩张保持所有旧 profile；Merger 的专用旧因子/门和完整 Parent 已迁移；实际 Cell Attachment 消费另列 |
| 模拟 pushout | existsUnique_presentedHom、presentedHom_ext、exists_simulation、exists_node_map | 原核证书覆盖任意内部目标单子；Presentation 只打包具体图合同，未假定普遍性质。完整 Probe 装配已完成；其实际 Cell Attachment 消费另列 |
| letterFloor 与高度像集 | ConstructionRealCuts.bounded_union；ZF.separation_exists_d / exists_setFunctionFromTo_of_denote；dvd_target_of_inCone、one_inCone | 已构造所有字母的实际图与上下界；旧高度正性／单调性保留。一般加法/max、正整数除法及 /4 四倍和已迁移；一般切割差本批已证，逐字母 intervals 已证，实际 heightIntervals 内部图本批已装配，不把上确界存在误报为完整 margin |
| Probe 锥内／锥外 cost 界 | 既有 FractionAddition.Sum／sum_right_lt_iff、Separation、ConditionalJoins、ConeLaws、floor 图及原核 ModelTransfer | 已有有界和切割及两界；一般旧 PointBound 输入保留，初始 Base 的该输入已由本批消去。原逐字母严格区间及实际 heightIntervals 三图均已有；完整 Word HeightCost 本批已接通，Path／Probe 原父输入完整装配亦已完成 |
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

Merger 当前消费：ConstructionMergerRelations/Copies/Action 将固定原关系（不是传递闭包）实例化为已验收 ProbeLetters 的具体 class／投影构造模式，直接调用原生 Separation／functionalImage／setFunction；product-coded representatives 及 projected/indices/range 直接复用。右自由性是固定 copy 的旧因子单射性；不要求右消去或提供 action oracle。本批直接以 Raw.exists_carrier/Old/Cons 承担 Merger Word；构造器末尾追加正是 source snoc，此前倒序存储描述已纠正。Word 乘法复用未改 evalHom 的 total/unique/old/cons 及泛化的 HeightFold.eval_range，原生函数构造提供旧行／操作／乘法图。不重建序列／parser／基础归纳或通用递归。本批原 Word 单子律、左消去及 conical 已消费这些实际图和未改 Raw 对象公式归纳。长度取已有 sequence length_eq；加法取既有 Base 内部 ω 加法图／消去律和 native ordinalAddition_successor_iff，不新增算术／编码设施。本批已用既有 ConstructionProbeConditionalJoins.left_mul_dvd_iff、ConditionalJoins、JoinProperty，直接迁移源 residual／same-copy／overlap／copies_hasConeJoins；HasConeJoins 已作为同一实际生产者的结论进入原核闭句。Word.dvd_snoc_iff／snoc_cone_intersection／exists_cone_join 本批已接通；旧嵌入／根实现本批已有原核证书；完整加权 MergerData、大小界、候选／塔／切片全 RootSystem 和完整轮次装配现均已完成；原来源数据继续供多轮消费者使用。

本批复用裁决：Probe 的 old_dvd_iff_headDiv 依赖特殊 Alphabet/Word 商，不能仅改名套入不同 Merger Word；其泛型 left_mul_dvd_iff 则只依赖 LeftCancelMonoid，已原样复用。Raw 已含旧系数及末尾追加，本批已按原 MergerWords.leading／dvd_snoc_iff 适配现有表示，以 oldDivAt/coneAt/joinAt 使用 Raw.raw_induction 完成旧整除及全部 Word 条件并；不新建序列解析、归纳或递归后端。

本批 Word 条件并实际复用：长度比较直接调用 ConstructionMergerWordLength.product_length 与 ConstructionBaseMonoid.le_iff；锥交和共同上界归纳使用未修改的 Raw 对象归纳；旧整除保留 Raw 中的实际旧系数；旧共同倍数／锥交保持供原 ConservativeExtensions.Word.oldHom_conservative 消费。新的同一载体生产者返回 ConditionalJoins W H，不接受该结论为前提。现成 ConstructionProbeConservative.Conservative、ConstructionPersistentProfiles.HasOldGates/exists_mapped_profile、ConstructionProbeLiftHom.PreservesProducts 都是泛型合同，本批旧嵌入已直接消费这些泛型合同。特殊 Probe WordCarrier 的 exists_old_graph 生产者没有被直接改名套用；本批用同一原生可定义函数构造模式适配实际 Merger Carrier。

本批旧嵌入／根实际消费：Conservative 四字段分别复用 Old 注入、factors_of_old、preserve_old_cone_intersection、old_common_multiple_iff；HasOldGates 直接给出 old 分支，不建额外 gate。所有旧 profile 调用未改 exists_mapped_profile，映射节点复用 native composition。根函数图由原生函数构造器、projected 与 Raw.exists_cons 组成；root*old 的字面式消费已有 CopyLaw 与 Word action/product laws，精确关系消费 copy_eq_iff，根新颖性消费 old_ne_cons。完整 Pure forall7 证书保留同一实际生产者数据，不另建 Object/Hom 框架。

当前 Merger 权重已消费既有任意正内部 n 的 ConstructionCutDivision.Value、实际坐标行、Raw evaluator 和 Cut sum/product 图。有限平均／min 乘积除法函数图、全部逐点界、copies 严格统一 margin／真实上确界、完整 copiesHeightCost／同一原父生产者均已有原核证书；不能再列为待实现。Word 实际字面权重及完整 HeightCost／实际上确界 margin、任意旧对成本族与上确界保持也已验收。Word margin 直接复用现成 atTarget／Raw 归纳、可除性分解、copies margin 和 canonical_uniform；没有新通用后端。snoc 的存在性见证用 room*quarter，源字面权重公式保持。当前真实状态见 STATUS。

Merger 基数界已直接复用 ConstructionProbeWordCardinality.raw_cardinal_le、ConstructionProbeCardinality.indexed_quotient_bound、原生 infinite_product_l 和 ConstructionMergerCopies.projection_onto，现有原核证书。ConstructionMergerParentSyntax 已组合同一原父生产者与完整 Word 权重，保留实际旧嵌入／所有 profile／根、指定非单位元、高度／成本／旧上确界及条件基数界；完整加权 MergerData 不再待装配。

ConstructionDirectedColimit 已复用原生有向商、projection、完整 Hom/Conservative/profile/Cap/基数界及通用性质，Under-base 极限保留同一对象、全腿族及唯一 fromBase。ConstructionOrdinalSchedule 已复用原生规范良序型、逆／复合图取得同一 Schedule／Place／last；Request.data_cardinal_le、索引和全部塔阶段大小界已由现成基数／小族并接口接通。实际内部递归塔、21 项图表、map_succ、来源／锥、执行根图和完整 CompleteRound 均已有原核证书。下一消费者为 Saturation 多轮；不重建这些数学。Placement/Hull 只按其实际源消费者接入。

本批供体重用锁为 SOURCE_LOCK.companion_reuse.native_small_family_union；三份原文件 SHA、三个精确区块 SHA、六项声明全足迹以及实际消费者均记录。既有原 Axioms.choice、源 AC 对应已完成；本批 choice_semantics/models_zfc 仅接线。不能把一般小族并的源 ZFC 前提隐藏成 ZF 无条件结论，也不能把它加成极限对象构造前提。

本轮已实际完成此前兼容核对之后的接线：223 模块闭包中旧版已有 81 个，其余 142 项用 140 份只改导入的数学正文及 2 项既有实现重定向解决。140 个模块和 2818 项公开／生成声明均已正式验收，无新增信任；SOURCE_LOCK 锚定 L_REUSE_LOCK 的所有源码、去导入正文及精确足迹。活动依赖和供体均未修改，未读取退役反射归档。源域公式消费本批已验收；全部内部 Proof/Con 仍是实际未完项。

本轮源合同修复已完成：RoundFresh 直接调用既有强父生产者，保留实际 generator 和对当前 O 的 hNotOld；Selection 已复用原九字段末字段保存实际 Probe，Done 的原生／纯 AST 加入当前 O，候选／选中输出／Extended／全塔 map_succ 全部加强，两个当前源请求仍保持全部内部量词。不存在新的选择器／编码或 Probe/Merger 数学重造。源 probe_gate.intersections／probe_independent／Merger.RootSystem 的原操作全锥合同现均已取得原核证书；后续切片传输现亦已消费实际全塔腿完成；不能把当前阶段新鲜性再报缺失，也不能用旧因子实现代替任意新右因子的公共锥实现。

已完成的具体来源传输：MonoidRounds.ProbeData.independent:304 所需 path/quotient/action/target/exit/word/generator 数据与 CompleteRounds.creates_merger 所需 copy/free-action/word/root 数据，现由 OperationSource／RoundSource 的纯对象合同保留到候选／全塔。ProbeParent 原构造证明本体仅分解为更强出口，旧接口由投影保留；未重做既有生产者或数学后台。Probe 的零位 gate／完整旧 profile 已由同一原数据导出，精确 independent 及实际 Provenance 消费已取得原核证书；全锥 RootSystem 现也由同一原 word／copy 数据装配并取得原核证书；现已传到全部实际后续切片；完整轮次和 K 索引重复 Probe 家族亦已完成，接下来为多轮 Saturation，不再另建正规形或恢复冻结字节支线。数据存在与语义等价、单独编译都不代替后续精确锥的原核推导。

本批精确复用：ConstructionCompleteRound.exists_placement 直接使用已有内部 successor／trichotomy 和 set-function；exists_probe 将原 Place(q,k) 与同一已验收切片家族复合，保留准确 Place/ProbeAt 图并导出 K 单射／全 profile／全新右因子 JoinProperty。realizes_merger 直接消费 actual at_later 的全 RootSystem。exists_from_parent 进一步调用既有 RequestCarrier、有界调度／塔、Execution 和实际 last 行，消去请求／调度／塔／目标作为输入。forall15 原核证书使用既有内部 L，消去 Choice/order。所有单轮目标已完成；下一项为源 Saturation 多轮、模型应用和内部 Con。18 项新增声明、旧 31202 足迹不变，完整验收见 STATUS／complete-round-acceptance.json。

## Saturation 实际后继与下一处供体消费

CompleteRound.Built/built 和 exists_complete_round_built／exists_from_parent_built 保留原实际有界调度、Recursive、全矩阵／执行根图、同一 last 行及 AllSmall；旧接口类型与足迹不变。SaturationStep.Candidate/Picked 必须保留该 trace；minimum 证明直接共用从旧 RoundSelection 提取的 least_denote。SaturationSuccessor 直接消费既有 HistorySuccessor.parents、全腿函数复合、self-extension、Append.preserves，实际更新全部旧腿／base、保留精确当前 inclusion 方程，并证明追加历史完整 Valid/AllSmall 和唯一记录；无新集合、编码、选择或递归后端。两条 forall15/18 原核证书已正式验收，详见 STATUS。

| 已定位供体／底座 | 实际下一消费者 | 当前适配状态 |
|---|---|---|
| 供体 7979336，SetTheory/Card/Properties/SuccessorRegularity.lean:17，ZFC.hartogs_regular_l | 原 RoundOrdinal.countable_bounded／Saturation.countable_stage；ConcreteSystem.μ_regular | 已通过 ExistingSuccessorRegularity 的必要闭包适配，并由实际 μ/覆盖/饱和消费者使用；不重证或再报缺失 |
| 同供体 Card/CountableUnion.union_bound_l；本仓 ExistingSmallUnion.lean:153 | 后继正则性所需小族并 | 必要接口已经适配并由 DirectedCardinality 实际消费；不复制整 CountableUnion，也不重报为缺失 |
| 同供体 Card/OrdinalImage.lean | 后继正则性的序数像界依赖 | 必要原证明闭包已适配为 ExistingOrdinalImage 并被实际消费者使用；未升级活动底座 |
| 固定底座 Card/Cofinality/Boundedness.lean:282/335 | 同一内部可数族的适当阶段上界 | bounded_of_cardinality_mem／range_bounded_of_domain_mem 已存在；只接 ω₁ 与实际塔的消费者 |

已读供体源码 SHA256：SuccessorRegularity = 3ba72b4361f154a2c3bffe813a1a1d32074c99fbe30f2b235f1cb1dfb64c4edb；CountableUnion = f1c74af92e3cbd9ac0157272da447b20909e89bd71a2753ce3b7157a675cb3f5；OrdinalImage = b4d2ab883b487b5b66ce54d0af333dab9a38b2ddd7323635c28418dec146b7e0。供体未修改。初始／极限／原生内部递归／valid_of_cover 及内部反例集归纳方法已有，不新建此类后端。

## 当前外层递归消费（2026-10-28）

ConstructionSaturationIterationCases 的三个实际分支直接使用原 Initial／HistoryLimit／SaturationSuccessor；TowerCardinality.append_small 为既有后继中的小性证明提取，后继旧接口／足迹不变。SaturationIteration 的 BinarySchema15 对全部内部集合历史总唯一，实际调用原 recursiveSequence_exists；SaturationIterationValidity 的纯 Correct／内部分离反例集和序数归纳同时证明全 Valid/AllSmall，并复用原 valid_of_cover 和全字段／图表提取。全塔 map_succ_selected 保留实际完整 round trace 和原始 inclusion 方程。forall17/16 原核证书已正式验收；有界原父背景下的完整内部多轮塔不再是待做数学。

具体ω₁+1／基数参数、可数适当阶段覆盖及最终饱和系统现已全部接入；ExistingOrdinalImage与ExistingSuccessorRegularity原供体正文亦已按锁定闭包复用。实际μ/K、无几何父前提的Base和同一实际最终T行已有原核证书。这些不再是缺口。union_bound_l已适配；无需复制未消费的整个CountableUnion。

当前PlacementExtensions.countable_obstructions/exists_fresh_member直接复用已验收ExistingSmallUnion.uniformize_l、原生Separation/exists_setRelationOn_of_denote/复合单射和既有small桥。完整原集合值族的准确行关系在内部构造，障碍族选择图由两两不交性成为注入，预算可取内部ω。forall4/5原核证书相对同一现成L；Choice由已有L证书消去。未重建选择/基数/图后端，未扩展泛滤分支。排列扩张现也已完成原消费者所需的无限预算特化和精确extend_permutation_off合同；补集等势调用现成cardinal_of_set/infinite_union_two_l、原序数三歧和Cantor–Bernstein，分段图/范围/逆/复合均为原生现成构造。未重新实现其后端，也未引入新的Bool证书。实际标签I=Hartogs(μ)由既有exists_hartogsNumber_kernel构造，非小性由原Hartogs性质给出；原核证书覆盖同一实际I的全部内部位置输入。集合层paste/two/three-copy合同现也已消费现成原生函数/恒等/像图构造器、二并界、small_image和上一批off扩张，取得未相对化forall6拼接证书及同一L的forall10/10两份/三份位置原核证书。精确两交集/指定边/整个禁集/三个全像交集均保留；未新建后端。实际Diagram的范围/公共子图标签等价、固定根排列、排列图相等及ExactOverlap.of_common现也已有原核证书；直接调用旧Sub/CompositionGraph/Injection/原范围逆复合图/injection_ext/已有extend_permutation。没有重新实现这些后端；原有限Merger/给定CopyRel早已完成。实际原可选处方现已由现成产品/Separation/uniformize_formula_l构造；无对角/不交起点和垃圾行，原给定CopyRel逐项等于标签相等并有Valid。realize_family已在同一最终Row上消费旧AllMergers，返回同一实际P的identity/roots/RootSystem/精确实现；forall5/14同一L原核证书齐备。根右锥并上的实际部分单射及整个D→I共同扩张现也已构造：恒等/包含/复合给出实际全嵌入，原restriction+既有between_diagrams+现成排列扩张完成原extend_embedding的载体适配；Glue单值/单射直接来自同一P的精确产品/标签等价，由原生函数构造器生成。forall15同一L原核证书返回全部P/id/roots/RootSystem/实现及原Sub/Le方程，无给定全图。剩余固定三图/实际Cohen descent/Hull及原9–11，最终Con未完成。

固定三图消费现由 ConstructionDiagramThree 完成：用现成 digits_exists、Kuratowski 配对及原 KP pair/insert 构造内部三元族F，消费现成整个载体 amalgamate，返回原三个Le下界与forall16同一L原核证书。未新建函数/基数/选择后端；实际Cohen支撑/限制/兼容/并条件现已完成；完整Product descent现已完成；Hull/ComponentGluing仍待。验收见 verification/diagram-three-acceptance.json。

实际Cohen消费者由 ConstructionCohenCompatibility 复用原 Separation/唯一函数、ExistingOrdinalImage.ordinal_image_bound_l、原两次 coordinate lift/image、infinite_union_two_l 和KP并构造完成。支撑是原图到标签的实际投影，保留源s0限制范围与s1重叠范围各自独立；四条未相对化原nativeZF证书不加Choice。完整descent现由ConstructionDescentPlacement实际消费以上结果，不重建支撑、限制、Cohen图作用或并条件。验收见 verification/cohen-compatibility-acceptance.json。

完整Product descent由 ConstructionDescentPlacement 消费现成three_copy_placement、fixed-three amalgamate、Cohen comparison/union和原Comp/Le传输完成。只包装原范围构造+既有ordinal_image_bound_l；实际K是t范围与c支撑的并。保留s0/s1独立范围、任意反例条件及实际两次lift/image；原Kuratowski配对和Product.Le返回完整三个下界。forall28同一L原核证书不加普通ZF Choice。任意目标下降图、因子化/唯一性已存在；代码审查确认 plain monoidLift 泛性质不是当前可数 hull 前置，不据同文件排列顺序扩写其包装。验收见verification/descent-placement-acceptance.json。


本批 CountableHull／ConservativeHull 复用裁决：CountablePair、CountableUnion、CountableChain 已在现有 PPAC/Companion 闭包内，不新增复制。供体 CountableHull.cc_hull_l 是一元多值闭包；只适配其内部 powerset／iterate_l／归纳／range／union 正文方法，二元一步可数性消费现成 countable_product_l/countable_cover_l，同阶段消费 cc_increasing_of_successor_l。保留精确源 stage/carrier，覆盖空种子及非标准内部 ω。

ConservativeHull 的实际乘法表使用原 ZF.exists_restriction，包含图使用原 identity；原 divides_antisymm 识别两个 joins，不新造序或选择后端。完整装配构造源三值插入行和实际操作表；forall6/exists9 同一 L 原核证书消去 Choice。实际消费者是 CellTowers.hull:330 及其 countable/contains/deps，ConcreteQuotients:118 factor_eq；实际 CellTowers 消费者和 ComponentGluing 的后续纤维粘合仍需接入。完整源定理的 Conical 前提保留；不把独立 omit-IsConical 辅助定理的全泛化算作本批完成。
此前 CountableHull 批次的 113 项声明及两条同一 L 原核端点正式验收通过：2905 项构建、32089 项声明审计，9 条命令／5 次 trust=0 全退出 0、零警告；此前 31976 项足迹不变，无新增公理依赖。75 份固定源与 2460 份当前指纹匹配，底座／供体干净。见 verification/countable-conservative-hull-acceptance.json。

## 当前 ComponentGluing 复用与真实缺口

| 当前消费者 | 实际复用 | 状态/边界 |
|---|---|---|
| 原 contract/Arrow/共同后继 | 既有 Sub/index_unique/sub_sub、left_mul_dvd_iff/translate_cone_intersection、原生 Separation | 精确右商理想和根图保留；geometrySentence 九条定律是普通 nativeZF 原核证书 |
| 全部 Vertex carrier | 既有 ForcingDiagramCarrier、原幂集/积/Separation/Kuratowski 编码 | 构造全部内部顶点集合，无秩/可数截断；不是商集，不另建通用编码器 |
| 整个 Common 分量 cofinal chain | 既有 ConstructionIdealCofinal.directed_cofinal_sequence、唯一 contraction、exists_setFunctionFromTo_of_denote、exists_node_map | 整张内部 ω 图及所有 i≤j、整个分量覆盖；同一 L 原核证书消去 Choice，现成 ObjectFields 父背景保留 |
| CellTowers 实际 Cell 消费 | 已有 CompleteRound.Built、SaturationStep.Candidate、TowerMapSucc、OperationSource、countable conservative hull | 塔与来源已有；需同一最终 T 的 stage range 原 Attachment、有限旧系数/依赖/首次出现/重排；Merger presentedLift/simulation 精确入口尚未定位到，不能写成已有或断言数学不存在 |
| 后续真实粘合 | 现成完整 Diagram、函数与 MergerCopies 商构造方法 | 实际 System 限制/精确交集、Fiber/arrowMap、Matches 和全纤维结果仍需迁移；Component quotient 与 Common.iff_zigzag 无调用，不列为前置；需要等价类时复用 DirectedLimitCarrier／原 fiber_function_l 的已有构造 |

此前各批“下一项”仅是历史上下文；现行缺口以本节和 STATUS 为准。无实际消费者的独立 Component quotient 不增加为新前置，既有 L/全模式/塔/ω递归/计数并/商/名字后端不重做。

本批正式验收通过：2909 项构建、32174 项声明审计；新增 85 项及三条原核端点，旧 32089 项足迹不变。9 条命令／5 次 trust=0 全退出 0、零警告、无新增公理依赖。75 份固定源与 2464 份当前指纹匹配，底座／供体干净；358 个获批退役模块仍全部不存在。见 verification/component-cofinal-acceptance.json。

后续粘合仅接固定源的三段真实装配：

| 源入口 | 所需适配与已有接口 | 严格验收边界 |
|---|---|---|
| LocalRecords.System:531；AvailableRecords.eligibleSystem:265–290 | 实际对象集合族及 restriction 图；复用 range_inter_sub 和已有强迫前端 | LocalQuotients:289/445–554 的全秩 normalized local names、EqG 实际商及同代表 restriction 尚待接；不能直接假设 intersection 或把条件 System 当作实际生产者 |
| LocalRecords:549–599；AvailableRecords:405–459；ComponentGluing:213–286 | availability 由实际 restriction 原像定义；Fiber 要求完整 availability=指定 ConeIdeal；arrowMap 字面为 restriction。复用本批 contract_ideal/eq_of_contract_eq/Arrow | 原图恒等/复合/单射/交集下降和实际 arrowMap 双射，不改成任意另选双射 |
| ComponentGluing.Matches/Glued:305–398 | 完整 component point 集；已有 DirectedLimitCarrier.exists_representatives:45 的依赖和集方法、Companion Fiber.fiber_function_l:29–33 的精确类函数及 range | 全点 Matches 等价、同fiber相等判据、实际规范投影，toGlued_injective:368/surjective:375/arrow:391；不缩成链上的局部商，不选择代表 |

实际消费者为 ConcreteSystem:223/265、CodeLinks:275–309/376/426、OrdinalCodes:500–522、QuotientTransport:263–292、TailGraphs:84。DirectedLimitCarrier 的专用 Related 不能未经对应证明套用；ProbeWordQuotient 是单子右除，不能当等价类商。现有 ForcingAtomicLaws/Formula/Evaluation/PowerName 等已完成基础继续复用，不重建其后端。


## EquivariantMixing 的实际支撑下降消费者

固定源 LocalQuotients.support_descent:132–202 真实调用 equivariantMix、equivariantMix_fixed、eq_equivariantMix_at。ForcingMixName/MixLaws/EquivariantMix 已复用现成 Collected、原生 union/Separation/恒等图、AtomicBasic/Laws/Symmetry、ProductFamily.order、NameConjugacy 和 collect_HS/fixed；没有重做名字、递归或 HS 后端。源码及全部声明足迹锁在 SOURCE_LOCK 的 forcing_mix_name/forcing_mix_laws/forcing_equivariant_mix。

精确混合名字及其两条强迫定律保留全部内部索引/条件和任意秩名字。固定性/HS 证书专用于已有实际 Product/WithTop 呈现；原族等变前提保留，混合名字不变性和 Product 保序是证明结果。四条普通 nativeZF 原核证书已通过全量验收（2912 构建/32233 声明，旧 32174 项足迹不变，9 命令全部退出 0）；见 equivariant-mixing-acceptance.json。实际 active_equal 和 support_descent 已在下述后续消费者中完成；LocalName 载体、规范化、名字层限制/下降已由后续消费者接入；LocalQuotient/商限制、eligibleSystem/Fiber/粘合仍未完成；不能将这些消费者与已完成混合引理混为一项，也不能误报现成后端缺失。


## 支撑图相等与实际相容放置

| 源证明／真实消费者 | 本批实际复用 | 边界 |
|---|---|---|
| OrbitNames.smul_name_eq_of_diagram_eq:238 → LocalQuotients.active_equal_independent | ForcingConditionGraphs.exists_inverse/exists_composition；ProductCovariance.inverse；NameConjugacy.composition/inverse_action/injective；既有 fixedAll 和 AgreesOn | ForcingSupportedNames.kernel_certificate 是普通 nativeZF 中字面相等模式；全秩名字、精确支撑范围保留。没有重建名字／作用后端 |
| ProductForcing.compatible_placement:149 → ChoiceFailure.forces_at_supporting_root 和 LocalQuotients.active_equal | 已有 diagram_range、原生恒等／注射复合、extend_permutation_off、common_extension_three、Cohen exists_support/exists_moved/restricted_entry/exists_union | 实际 pi、精确范围交集、实际共同 Product 下界；对象 forall22 原核句相对化到已有同一 L。原实际基数／最终行／合并父背景保留，不假定输出置换或共同加强条件 |

RootCompatible 仅展开原根限制相容性，范围是 p 的精确内部值域，不是额外见证假设。相容放置与支撑强迫保持分别验收；源 ChoiceFailure:279/305 的稠密性消费现已由 ForcingSupportingRoot 完成，直接复用已验收的输出及强迫正则性／对称性。来源、直接复用文件及全部足迹见 SOURCE_LOCK.forcing_supported_names / construction_compatible_placement。


## 已实际消费的支撑根强迫

ForcingSupportingRoot.forces_at_supporting_root / forces_iff_restrict 直接调用现成 ForcingSeparation.symmetry（已经处理实际 Product、全秩 HS 及新作用图参数）和 ForcingFormula.of_dense/mono；不用再写一套公式对称或环境重索引。既有 small-support Filter 通过 is_normal 给出所需正规性。Code 仅展开既有 Kuratowski pair 与 WithTop singleton，moved_code 以现成图唯一性连接 compatible_placement 的输出。

construction_kernel_certificate 为任意源 Formula/参数元组的同一内部 L 原核模式；源背景、精确范围／限制和全秩 HS 均保留。后续 active_equal 与完整 support_descent 现已接入，但不再重报 root restriction 为未迁移。第 10 阶段全部内部码仍单独未验收。

## 独立活动副本比较

LocalQuotients.active_equal_independent:18 → ForcingActiveIndependent.construction_kernel_certificate（同一内部 L）；真实消费者为 active_equal:111/114。直接消费已完成的 ConstructionDescentPlacement.descent_comparison_placement、ForcingSupportedNames.name_eq_of_same_diagram、ForcingSeparation.symmetry、AtomicBasic/Laws，以及现成 Code/moved_code。新增 below_code/lift_le 仅连接已有 Product/WithTop 的原条件与下界；eq_symmetry 仅将已有公式对称性实例化为相等。未重造放置、名字作用、强迫递归或 L。此项独立比较已完整验收（2916 构建、32288 声明，旧足迹不变）；独立比较验收见 active-independent-acceptance.json；一般比较和完整支撑下降均已由后续消费者接入。

## 任意重叠的活动副本比较

LocalQuotients.active_equal:67 → ForcingActiveEquality.construction_kernel_certificate（同一内部 L）；真实消费者 support_descent:173。原 permute_le_root:58 复用现成 compatible_placement 的固定根 CompositionGraph 与 ForcingDiagramOrder.le_iff。根限制相容性由 exists_restrict/restricted_entry、实际 Moved 和 Cohen functional 直接推出。相容放置返回第三副本，两次调用 ForcingActiveIndependent.active_equal_independent，最后复用 eq_of_dense/eq_trans/eq_symm。已通过全量验收（2917 构建、32293 声明，旧足迹不变；active-equal-acceptance.json）。无新增独立性、稠密性或共同下界前提。一般支撑下降的族装配现已直接消费 ForcingReplacementOrbit.moved/moved_unique、原生 functional graph、ForcingPowerName.hs_move 和 EquivariantMixing，见下文。

## 完整支撑下降的实际装配

LocalQuotients.support_descent:132–202 → ForcingSupportDescent.construction_kernel_certificate；真实消费者 localName_descent:386。ForcingSupportOrbit 构造原固定根子群索引的精确名字函数图和激活函数图；使用固定原生 FunctionConstruction.exists_setFunctionFromTo_of_denote 与既有 group orbit/name action，无新函数图后端。实际 Product 乘法/恒等和 name composition、hs_move 给出族等变/HS/恒等项。moved_coordinates 通过现成 Cohen/Diagram 构造和作用唯一性取得原坐标。

完整 support_descent 保留原 Cohen 见证及两侧原限制；先用已证 supporting_root 限制到 v，证明嵌套限制等同原 d|s0，直接调用 active_equal 得到所有内部索引的相干性，再消费 exists_mix、fixed_and_HS、eq_at 和第二次 supporting_root。没有额外相容性、给定相干族或给定混合名字。全部 19 项声明/同一 L 原核证书通过完整验收（2919 构建、32312 声明，旧足迹不变），见 support-descent-acceptance.json。具体 LocalName 规范化及名字层下降现已消费上述输出，直接复用 normalized_bounded/normalize_eq 和 Separation/CollectedHS.fixed，见末节；不重建规范化后端。

ProductNames 的具体 Bit 及五条原性质已由 ForcingProductBits 接通：直接消费 ConstructionCohenCompatibility.Entry/entry_functional、ForcingActiveIndependent.below_code、SupportingRoot.code_le、SupportOrbit.moved_coordinates 和已有 Product 条件作用，取得五项 nativeZF 原核证书。实际消费者是源 label/smul_label/mem_label，再到 LocalName；label/labelSet 现已由 ForcingLabelNames/ForcingLabelSet 构造。具体 check 名字族与全标签图复用原生 functionalImage/setFunctionFromTo；单点小支撑复用 ω≤μ 单射与原生 constantFunction；现成 collect、HS 收集、Bit/名字作用产生实际 HS 标签及全群固定 labelSet。七项 nativeZF 原核证书已验收，见 verification/label-names-acceptance.json。具体 subsetBound、候选强迫子集及 LocalName 载体/名字层限制现已接通，见下节；checkName/collect/normalize/bound/商后端已有，不重建。


## 实际 LocalName 载体与名字层限制

ForcingLabelBound 直接消费 ForcingPowerName.Bound、实际 LabelSet 的 edge 方程和 AtomicRelations.mem_iff，给出源 labelSet_subsetBound/normalized_subset_labelSet。ForcingLocalNames 直接消费 exists_candidates、既有 SeparationSyntax、supported_mono 和 ForcingConditionGraphs.exists_identity，得到原 PowerCandidate 的字面支撑子集及限制图，不创建另一个候选类型或图构造后端。

这六项原核端点对应载体存在唯一、界等式/强迫子集和名字层限制/复合。LocalQuotient 的商和商限制仍是另一消费者。后续已接入的 separate_fixed/normalize_fixed 直接使用 ForcingSeparation.test_permute、ForcingCollectedHS.fixed；localNormalize 使用同一个 separated 名字、ForcingPowerName.normalized_bounded/normalize_eq；localName_descent 消费已完成的 ForcingSupportDescent。不能将这些现成后端或 support_descent 再列作未证明。


## 实际规范化与完整 LocalName 下降

ForcingLocalNormalize.separate_supported 保留 exists_separate 构造的同一个名字，调用 test_permute 和 CollectedHS.fixed 证明实际共同子群的固定性；没有另建规范化。actual_normalize 从实际 LabelSet.HS_and_fixed、Fixing 子群和原无限基数背景导出所有固定性/HS 前提，再消费 normalized_bounded/normalize_eq。任意新内部见证只增加值参数槽，复用 subset_relation_congr/atomic_congr；谓词、强迫关系及全秩量词不变。

ForcingLocalNameDescent.localName_descent 直接消费 ForcingSupportDescent.support_descent，再用 actual normalization、LabelBound.normalized_subset、PowerName.subset_congr 和 AtomicBasic.eq_symm/AtomicLaws.eq_trans。两个原 Cohen 限制保持；未替换成新的加强条件。普通规范化原核证书和同一 L 的完整下降原核证书均已全量验收；记录见 verification/local-normalize-acceptance.json。

localAtomic/localSetoid、实际商集/满投影和限制图已由 ForcingLocalAtomic/ForcingLocalQuotient/ForcingLocalRestriction 接通并全量验收。复用 ConstructionMergerCopies 等价类/投影构造方法与原生 Separation、functionalImage、setFunctionFromTo；不存在待建商后端。限制图保留同一代表名字，其恒等/复合和代表方程已有原核证书。

LocalQuotient.restrict_injective:511 和 intersection:536 现已由 ForcingLocalInjectivity/ForcingLocalIntersection 接通并全量验收。单射直接复用 forces_at_supporting_root 与 ConstructionCohenCompatibility.exists_restrict；交集直接消费 localName_descent（源第 550 行调用）、既有 class/projection/Restriction 和范围单调性。两个原 Cohen 限制仍在同一滤子内；精确输出是实际根商类及两条限制边。两个原核证书均在同一已有内部 L 中，Choice 消去方式不变。

下一真实消费者是 AvailableRecords.EligibleName/Eligible/eligible_restrict_iff 与 eligibleSystem:265，源码第 279、283 行分别调用本批单射和交集；ClassFibers:399 也调用交集。现成 ForcingFormula.tuple_congr、supporting_root、labelSet 固定性可用于资格接线。该系统、向移动滤子的 quotient transport 以及后续实际纤维粘合尚未宣称完成。localName_of_raw:342 仍无当前调用，不新增为主线前置。
