# 现成接口复用与精确边界（2026-10-26 重审）

本表取代重复的逐批进度叙述；旧验收段可从 Git `629b815` 恢复。固定 YesMetaZFC 为 `039c8e132cc19671d73a3933c66b4799d2599dd6`，本轮未更新活动依赖或修改供体源码；另核对了新版 YesMetaZFC 7979336，见下文。源码位置与依赖指纹以 SOURCE_LOCK 为准。

| 已有资产 | 精确入口／本仓实际消费者 | 正确状态和边界 |
|---|---|---|
| 完整 ZF 模式 | YesMetaZFC/SetTheory/Axioms/ZF.lean 的任意参数 separation/collection；ReverseZFReplay、CollectionFromReplacement | 已完成并消费，不能再报为数学缺口 |
| 集合配对、并、插入、积、分离、收集 | KP.exists_pair/exists_union/exists_insert、ZF.exists_cartesianProduct、Collection.collection_exists_d；KuratowskiZF、ForcingNames、ForcingAtomicRecursion、ForcingHS | 已消费。内部 Collection 见证族经 Separation 过滤再合并；不抽取对象选择函数 |
| 内部序数递归 | SetTheory/Ord/Recursion.lean:1297 recursiveSequence_exists、1322 recursionValue_exists、1339 transfiniteRecursion_isClassFunctionOnOrdinals；GodelDefRecursion、ConstructibleHistory | 已消费全部内部序数接口。另一个 WellFounded.Recursion.solve 要求宿主 WellFounded，不能用于任意可能外部不良基的 nativeZF 模型 |
| 集合／名字归纳与递归 | SetInduction.native_induction → ForcingNameInduction/ForcingMapLaws → ForcingPairInduction/ForcingTripleInduction；ForcingNameRecursion | 已消费到名字、映射、原子递归和定律；后两种归纳有实际证明消费者，不是待重建后端 |
| 内部函数空间 | FunctionSpaceConstruction.lean 的 ZF.exists_functionSpace；ForcingLabelPermutations.exists_carrier | 本轮直接消费其全部内部函数图集合，再分离置换；没有重建幂集／积或函数空间。固定源文件哈希纳入 SOURCE_LOCK |
| 条件图构造 | SetTheory/FunctionConstruction.lean 的实际恒等、逆、复合图入口；ForcingConditionGraphs/ForcingConditionAction | 已消费，保留指定图的精确边方程。具体 PPAC 群同态族未实例化 |
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
| Name.HS.smul → forces_symmetry | 字面稳定子、实际 HS 定义、Child 归纳、共轭传输；通用 HS 作用及公式对称性已完成 | 为具体 actionHom 提供代数 Context，不能把 Context 当作已经构造 |
| SupportFilter.inf_mem/isNormalFilter → ProductNames.system | 固定底座函数空间、幂集、分离；新版 Card/Omega/InfiniteBound 五段原证明正文；实际小支撑族与四项正规性 | bot_not_mem 按 ChoiceFailure 消费者处理；具体条件作用仍缺 |
| Diagram.permute/permute_one/permute_mul/permute_inv_permute → ProductForcing.permuteOrderIso → ProductNames.actionHom | 本批 ForcingDiagramAction 直接调用 `ZF.exists_compositionFunction` 和 `IsSetRelation.eq_of_pairMember_iff`；复用已有 Injection/CompositionGraph 公式 | Diagram 序关系、Cohen 分量及 WithTop 后再组成源 actionHom；不能称整体已经迁移 |

本批 Diagram 证书依赖标准三项及七项已有基础句子 FreeClosed 证书。没有扩大此前活动可信基。此前正规滤子批次已消费的 15 项递归和 9 项基数 native Bool 证书仍保留记录及重算，不能改称整个工程仅有标准三项。

## 新版库的强迫合同核对

读查同一固定新版 7979336 的三个入口，源码哈希见 SOURCE_LOCK.companion_candidates.native_internal_forcing_contract_review；本批没有编译这些供体入口，也没有替换底座。

- `Internal.Npair_d / npair_l`：所有条件作权重的配对名字；源 pairName 是指定顶条件的两个边。存在语义用途，但不能原名替换后声称字面名字已对应。本仓已完成源 pairName，故不重做。
- `Internal.Aut_d / aut_bij_l`：内部条件双射及序／排除值保持。它没有给出源 ProductNames 的标签群具体作用；现有本仓条件图已经具备相应基础，继续复用它们。
- `Internal.preserves_zf_l`：对任意内部 ZF 模型，在 `Cond_order_d` 与 `Generic_d` 前提下证明完整泛滤商扩张满足 ZF。不是 HS 限制域的 ZF 定理，也不是对象内部 Con。不能为了套用该结论重开泛滤真值支线。

## 不能重复建设或误报的部分

新版 L 的域是任意 M 内的 `{x : M.Domain // L_d x}`；完整 ZF/ZFC 已有。223 模块依赖差异是版本整合工作量证据，不是 142 项未证明数学；GCH 不增加为本项目义务。BMS 完备性回传方法已在 ModelTransfer 中应用，当前供体存在无关脏改动，本批只读未动。

既有全模式、内部序数递归、Proof/Sat 配套已经存在。ZF/U 特化和全部内部码正确性尚未接通，但不另建通用证明核、编码器或满足关系。其他库接口未定位时写“未定位到精确合同”，不能写“数学不存在”。

`atomic_truth`、决策稠密集、`exists_truth_generic` 仅服务未选的泛滤分支；NatPacket／字节兼容继续冻结。旧的独立 L 重建路线停止扩写。保留具有实际依赖或尚未完成裁剪判断的已验收证明；不以已投入成本作为继续开发理由。
