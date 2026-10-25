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
