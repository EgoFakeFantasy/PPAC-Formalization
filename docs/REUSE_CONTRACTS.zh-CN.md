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
| 原核收尾 | BMS SecondOrderCompleteness.derives_m 的 strong_completeness 模式；本仓 ModelTransfer.derives/project_models_iff | 已接入纯成员语言、对应 Type 0 全模型。不是待重做的完备性；不能拿单个 LCarrier 模型冒充其全模型前提 |
| 旧 LCarrier 工程的完整模型数学 | lean-constructible-universe-stage4 固定 7f5a7d0；ZFModel.lean:28 lCarrier_models_ZF、StageHistoryGraphSystem.lean:171 lCarrier_models_ZFC | 该旧工程已完成完整模式，但 LCarrier 是 ZFSet 子类。这个限制不能概括新版 YesMetaZFC：其任意 ZF 模型的内部 L 定理已存在，见下一行 |
| 新版原生 L 数学 | ../yesmetazfc-analytic-comprehension，7979336；InnerModel/Jensen/ZF/Model.lean:15 l_model_zf_l、Choice.lean:14 l_model_zfc_l、GCH/Model.lean:47 l_model_gch_l | 任意 ZF 模型，完整分离／收集；本轮 ZFC 定向构建及三端点 trust=0 通过。待移植版本、Project 语言、相对化及原核接口；不是待重证的 L 数学。GCH 非当前必需工作 |
| L 的实际语法／递归与选择收尾 | 原 FormulaGodel、RudimentaryConstructible、BareStageHistory；本仓 GodelDefOutput/Recursion、ConstructibleHistory/Parameters、InternalWellOrderChoice | 已有构造被复用。Min_lt/CoverWO→AC 已证；实际 L 域满足全部前提仍待接通 |
| 全模式相对化传输 | InterpretedZF.source_sentence/native_sentence/project_axiom/collection；Relativization、ReverseZFReplay | 已接通；保留解释背景和域非空前提，不等于 nativeZF 已证明 ZFC 的全部 L 相对化 |

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

新版 L 的域是任意 M 内的 `{x : M.Domain // L_d x}`；完整 ZF/ZFC 已有。223 模块依赖差异是版本整合工作量证据，不是 142 项未证明数学；GCH 不增加为本项目义务。BMS 完备性回传方法已在 ModelTransfer 中应用，当前供体存在无关脏改动，本批只读未动。

既有全模式、内部序数递归、Proof/Sat 配套已经存在。ZF/U 特化和全部内部码正确性尚未接通，但不另建通用证明核、编码器或满足关系。其他库接口未定位时写“未定位到精确合同”，不能写“数学不存在”。

`atomic_truth`、决策稠密集、`exists_truth_generic` 仅服务未选的泛滤分支；NatPacket／字节兼容继续冻结。旧的独立 L 重建路线停止扩写。保留具有实际依赖或尚未完成裁剪判断的已验收证明；不以已投入成本作为继续开发理由。


本批已消费的 Cohen 复用：coordinatePerm 的两次 prodCongr 保留为内部精确图方程。原 `exists_cartesianProductInjection` 返回值未保留该方程，因此调用已有 `exists_setFunctionFromTo_of_denote` 留下方程用于函数性证明；不重建积或函数后端。`small_image` 在界 w=ω 时直接给出源 countable_graph 的内部保持；一般 w 的结论更强，但本批 ForcingProductParameters 已将共同载体和作用族特化到原内部 omega/2；完整单子/偏序系统仍未装配。

本批 Product 消费：Cohen 两次坐标提升、精确集合像和 Diagram 集合级作用律直接组合为 ProductForcing 的恒等／复合律。积与函数图仍调用底座 exists_cartesianProduct、exists_setFunctionFromTo_of_denote；源分量的保序性直接用于乘积关系，exists_source_action 消去分量构造前提。未重做集合构造、基数界或图编码。

本批复用原核闭合接口不变：ForcingHSAction 的原域传输证明只将共轭图参数从环境槽位放宽为任意内部图，原接口保留为直接实例；没有重复名字归纳。ForcingProductFamily 只将已证存在句子的开公式正文命名，旧句子仍定义为同一正文的闭合，供源 omega/2 特化消费。旧声明公理依赖集合预审逐项相同。

本批偏序复用：ForcingDiagramPoset.injection_ext 直接消费底座 IsSetRelation.eq_of_pairMember_iff 与既有 native_mapsTo，不另建图外延性。ProductPoset.preorder 直接返回现有 AtomicBasic.PreorderOn，原核闭合继续用 ModelTransfer.derives。源 sub_one/sub_sub/index_unique 的证明结构保留；实际单子构造仍沿 OpenAI Algebra/Construction，不能用任意现成单子替换所需的不变量。

本批 HS 配对／并集消费：原 MulAction.stabilizer 的子群义务由 ProductStabilizer 调用已证实际动作恒等／复合／逆及 NameConjugacy 完成。配对交集直接使用 KP.intersection_exists_d；正规性直接复用 NormalFilter.is_normal，名字构造与作用交换继续使用 PairName/UnionName/UnionAction。UnionAction 的同一条目证明放宽为只检查实际条件的序保持，旧接口保留且旧依赖集合不变；没有另建条件作用或名字递归。原核 HS 闭包已接通，并已由本批 ForcingPairUnion 消费到原 mem_pair/mem_union 和 forces_pairing/forces_union；其余强迫公理后来已由 ForcingZFAxioms 接通，当前剩余是具体系统实例化。

本批四条强迫公理继续复用 AtomicRelations.mem_iff/eq_iff、AtomicBasic 的自反／边引入／单调性、AtomicLaws 相等替换和 Formula 的逻辑分解；没有新建强迫代数或添加强迫公理字段。实际 HS 域只对已有 hs 公式重索引。原 codeOrder 的域限制由已证 IsName 条目性质给出字面并集等价，且实际构造消费了该等价。SourceStatements 中四条原公理本身未改写。

Foundation 迁移直接消费已经完成的 ForcingMapLaws.formula_induction → ForcingNameInduction.kernel_certificate → SetInduction.native_induction；将原 minimal_member 的归纳性质编码为纯成员公式，保留源 Child 下降和稠密见证。回传继续使用已接入的 BMS 式 ModelTransfer，不另建归纳、完备性或 L 后端。

Infinity 迁移直接消费固定底座 `ZF.exists_omega` 及内部 IsOmega 的空集／后继闭包，消费现成 checkName.exists_checked/edge_checkName/unique 和 HSCheck.check_hs。实际固定顶来自 ProductFamily.top_fixed；SuccessorOf 中的 SameMembers 由既有 ModelTransfer.extensionality 转为源等号。原 mem_check/check_successor 的稠密见证与原子相等替换保留；不另建自然数、check 递归或限制内部 ω。

收集名字迁移消费现有 coordinate_bound（两次原生并）、exists_cartesian（原生积）、SeparationSyntax 全模式，构造恰好满足原索引／条件测试的有序对值域。HS 证明消费 ProductCovariance.inverse、NameConjugacy.inverse_action、实际稳定子子群和 Normal 的上闭性。indexed_permutes_iff 核对当前对象条件与源按索引存在见证合同，而非未经证明地改写前提。族图允许关系式呈现，源函数图是精确特例；本批 Replacement 已用下述原生 Collection 适配该宿主选择步骤并证明本地见证消费者合同。

参数元组稳定子直接消费固定底座 `SetTheory/Separation.lean:98 KP.intersection_exists_d`、现有 subgroup_intersection/实际名字稳定子和 Normal 的交闭性。沿源的零元组顶群、后继有限交证明；separation_support 用追加原名字的元组取得分离所需共同支撑。原核回传仍用 ModelTransfer，不重建集合交、群作用或完备性。新版 L 的 ZF/ZFC 定理正文已再次回读，完整模式及任意内部模型范围不变；本批没有重跑或改写供体。

Separation 实例复用：内部子名字投影仅使用既有 coordinate_bound、原生积和 SeparationSyntax；没有新增函数／递归后端。normal_context 直接组合 ProductCovariance 与 Normal 的已有共轭子句，实际消费者为域传输和 separationTest_permute；不重证 HS.smul。atomic_congr/force_congr 只证明添加内部作用图／参数槽位不改变原递归或量词域，马上由实际 symmetry 和 exists_at_values 消费。mem_separate 复用原子的单调／稠密闭包及 tuple_congr；最终句子保持原 SourceStatements.separation，原核回传仍用 ModelTransfer。

幂集迁移复用：ForcingPowerName.exists_candidates 直接调用固定底座 SetConstruction.lean:362 的 ZF.exists_powerSet，再用现有 SeparationSyntax 筛出全部内部 HS 子集。候选族用已有恒等图呈现，subsetBound_fixed 和 powerCandidate_permute 消费实际稳定子、Separation.entry_permute/symmetry、HSAction 与 collect_HS；normalize 直接消费已证分离成员等价。mem_power 保留源稠密与相等替换，ForcingPowerAxiom 用已有 ModelTransfer 回到原核。没有重建幂集、分离、递归或完备性。本批再次直接回读新版 7979336 的 l_model_zf_l/l_model_zfc_l 全模式及任意模型范围；没有修改或重复编译供体。

Replacement 实例复用：固定底座 Collection.lean:69 的 ZF.collection_exists_d 在精确有效 raw-entry/condition 索引集上收集 HS 见证，经现有 Separation 过滤；它不选唯一函数。Replacement.lean:98 的 exists_functionalImage 直接构造整个内部群作用的精确像，现有实际恒等／乘法图和 NameConjugacy.composition 证明轨道闭包，collect_HS 给出界的 HS 性。bounded_local_witness 的完整源合同已实际证明，image_in_bound 与 replacementImage 沿原单值性／稠密性／分离链消费它，最终 ForcingZFAxioms 给出全源 ZF 的逐实例原核证书。没有添加对象 AC 或重建收集、函数像、递归、完备性。


阶段 8 下一消费者核对：原 Construction/MonoidBase.Base 采用内部自然数加法单子，但完整 Object 还保留条件并、真实 height/cost 和非单位元；Algebra/DiagramOrder.HeightCost 使用有界实数上确界。新版 7979336 的 Descriptive/Dyadic 已提供内部 2^n 单位分数码及比较，可作特定辅助候选；RealPair 实际是 Baire 空间配对，不是实数有序域。尚未定位与 HeightCost 全合同对应的现成接口，不能据文件名声称已接通，也不能据此次局部检索声称其他仓库没有相关数学。当前已有自然数／序数算术、图构造和递归继续优先复用；没有修改或构建供体。

本批 Base.M 已实际消费固定 039c8e1 底座 Ord/Natural.lean 的 ordinalAddition_mem_omega、members_areOrdinals/transitive，以及 Ord/Arithmetic 的存在唯一性、零元、结合、消去、序比较与右余项。FunctionConstruction.exists_setFunctionFromTo_of_denote 在原生 ω×ω 上构造精确内部加法表；Base.le_iff 与 joins 保留原自然数序／max 证明，不重新开发自然数算术。模型中全部内部 ω 都被覆盖，最后由已有 ModelTransfer 回传原核；height/cost/margin 后来已由 ConstructionBaseHeightGap 完成实际构造和原核证明，不再列为待做。新增声明使用已有 15 个递归 Bool 证书，预审未发现新的依赖；正式验收继续执行原证书复算。删除对整个 ProductParameters 的不必要导入，直接消费原生积构造。

Base 数值数据批次：实际复用新版 7979336 Descriptive/Dyadic 的 dyad_exists_l／dyad_unique_l／dyad_denominator_pos_l、dyad_le_l 的幂指数比较及 ds_digits_l 的内部数字构造方法，适配到固定旧版已有算术与原 n+1/n+3 偏移。供体单文件 SHA 已锁定，未复制其零距离分支、Baire 拓扑或整个依赖闭包。高度分子通过内部非零自然数的前驱取得，成本分子为内部一；两张函数图直接使用原生积和可定义函数图。原核证书还包含两图所有输出的 0<分子<分母；这不是完整实数解释，也不把 Dyadic 当作实数域。该批只到分数图；后续切割与完整 Base.margin 已接通，当前不再列为缺口。

分数比较批次：定位并直接调用固定底座 Ord/NaturalPrime.lean:497 的 Structure.natural_mul_comm，以及既有乘法结合、正因子严格递增、唯一性和内部 ω 闭包。交叉比较传递性只组合这些已有算术结果，不重建自然数乘法；载体由原生积和分离构造，上一批 weights_proper 直接证明原两图的值属于载体。单位分数比较的原核证书核对逆分母次序，与 Dyadic 消费者合同一致。比较对象是编码全预序，不把编码等号当作分数数值相等；后续已完成所需切割解释和 Base.margin；完整实数域不作为新的前置任务。

Base 数值解释的当前复用结果：原生 NaturalPrime、Arithmetic 的加法／乘法／幂、比较和右余项，已由 ConstructionFraction*、ConstructionRealCuts 和 ConstructionBaseHeightGap 消费到完整 Base.margin。分数密度、主切割、精确成本像上确界、严格高度差及实际两张图都已完成；原生 Separation、PowerSet、Union 与可定义函数图承担集合构造。此前“尚未闭合实数值消费者／margin”的批次说明撤出当前待办；不扩建当前源消费者不需要的完整实数域。

Probe Path／字母复用：factor/terminal 由左消去保证唯一，使用原生可定义函数图构造；类集合使用 Separation，商载体使用 Replacement.exists_functionalImage，投影、动作、target 与 exit 都使用 FunctionConstruction.exists_setFunctionFromTo_of_denote。现成 Representatives 同时表示 D×Letters，不重建积或商库。动作良定义／单射和 target 等变性已验收，过渡映射不要求单射。

Alphabet 的实际消费者：ConstructionProbeAlphabet 直接消费上述动作、target 和 TargetLaws；exit(s)=target(s)*d，锥见证的 target 给整除见证，左消去与源 conical 条件给 head_separation。原 d≠unit 前提保留。存在句子构造全套图和字母表定律并回传现有 ModelTransfer 原核；不是把分离定律留作未证字段。Raw 载体和构造器已接入；下一消费者为原 oldAct/headDiv、Word 正规形及 Probe 扩张。

锥与大小界的实际复用：ConstructionProbeCones 消费已有 letter_eq_iff、letter_transition、动作及 TableLaws，沿源共同阶段计算取得锥交、共同倍数与 initial_profile；对应消费者为 old_cone_intersection/common_multiple_reflection/probe_old_profile、ProbeMargins 和 ProbePresentations。ConstructionProbeCardinality 直接调用已复用的 ExistingCardinalBounds.infinite_product_l 及固定底座 Card/Cofinality/Comparison.lean:103 的 exists_rightInverseInjection_of_surjection_from_ordinal。先给实际代表元积编号，再将商投影延拓到基数，底座最小原像定理给反向单射；空商独立处理。没有重证基数乘法、最小原像定理或引入对象选择。

ForcingSupportSize.small_image 的置换前提不适用于任意商投影；本批用上述现成序数接口解决了实际消费者，而非新增基数后端。Raw 载体和构造器已接入，剩余为原 oldAct/headDiv、Word 正规形、它们的大小界及实际扩张。冻结的 NatPacket、泛滤真值与独立 L 重建路线继续停用。

Raw 的直接复用：ConstructionProbeRaw 调用固定底座 Ord/FiniteSequenceParsing.lean 的 empty_or_decomposition_exists_unique、components_unique 和 empty_sequence_unique，以及已有 exists_append，表示“尾到头的内部有限字母序列＋末尾旧元素”。载体由原生积／幂集／分离和现有 Representatives 构造；old/cons 的存在唯一性、单射、互斥、闭包与穷尽分解进入同一个纯对象句子的原核证书。未重建序列解析或把内部长度变为外部 List。只导入实际所需 ConstructionProbeLetters；两处误用 ZFC 配对唯一性接口已改为现有 KuratowskiZF.code_unique。原 oldAct/headDiv、Word/reduced 及大小界仍待按源实现。底座序列限制带来 6 项此前未消费的原生 Bool 证书，已纳入精确足迹和 Check 复算；不能说可信依赖未扩大。
