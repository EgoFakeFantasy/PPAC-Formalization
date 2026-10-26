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
| 新版原生 L 数学 | ../yesmetazfc-analytic-comprehension，7979336；SetTheory/InnerModel/Jensen/ZF/Model.lean:15 l_model_zf_l、Choice.lean:14 l_model_zfc_l、GCH/Model.lean:47 l_model_gch_l | 任意 ZF 模型，完整分离／收集；既有 ZFC 定向构建及三端点 trust=0 验收通过；本轮只回读 ZF/ZFC 正文及确认版本、干净状态。待移植版本、Project 语言、相对化及原核接口；不是待重证的 L 数学。GCH 非当前必需工作 |
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

新版 L 的域是任意 M 内的 `{x : M.Domain // L_d x}`；完整 ZF/ZFC 已有。223 模块依赖差异是版本整合工作量证据，不是 142 项未证明数学；GCH 不增加为本项目义务。BMS 完备性回传方法已在 ModelTransfer 中应用，BMS 供体此前存在无关脏改动；本轮未修改。新版 YesMetaZFC 本轮确认干净。

既有全模式、内部序数递归、Proof/Sat 配套已经存在。ZF/U 特化和全部内部码正确性尚未接通，但不另建通用证明核、编码器或满足关系。其他库接口未定位时写“未定位到精确合同”，不能写“数学不存在”。

`atomic_truth`、决策稠密集、`exists_truth_generic` 仅服务未选的泛滤分支；NatPacket／字节兼容继续冻结。旧的独立 L 重建路线停止扩写。保留具有实际依赖或尚未完成裁剪判断的已验收证明；不以已投入成本作为继续开发理由。


## 现行代数构造复用入口

下表取代逐批叙述；旧正文可从 45512cc 恢复。声明类型、所选供体正文哈希与精确依赖以 SOURCE_LOCK 和 Audit 为准。

| 当前消费者 | 已实际复用的入口 | 边界 |
|---|---|---|
| 全部强迫 ZF 模式 | Collection.collection_exists_d、Replacement.exists_functionalImage、SeparationSyntax；既有 HS、轨道和支撑图 | 完整前端已证；实际最终单子／呈现待实例化 |
| Base.M 和完整 margin | 固定底座 Ord/Natural、Arithmetic、NaturalPrime；新版 Descriptive/Dyadic 的数字与单位分数方法 | 已证，不扩建当前消费者不需要的完整实数域；RealPair 是 Baire 配对，不能代替实数域 |
| Probe Path 和商字母 | 原生 FunctionConstruction、Replacement、Separation；现有 Representatives | factor/terminal、共同阶段商、动作、target/exit 和 Alphabet 已证 |
| 字母大小界 | 已适配 ExistingCardinalBounds.infinite_product_l；原生 Comparison.exists_rightInverseInjection_of_surjection_from_ordinal | 从序数最小原像得单射，不任选商代表元 |
| Raw、Word、quotient、letterAct | 原生 FiniteSequenceParsing 和序列限制；已有函数图构造 | 所有内部有限长度；不是宿主 List；现成基础不重写 |
| Raw.eval、evalHom/liftHom | 原生 recursiveSequenceIn_existsUnique、已存在的内部历史限制 | Word/任意目标单子；目标不增加左消去条件 |
| Word 单子、old 嵌入及 conical | 已有 raw_induction、IsOmega.induction、实际乘法图 | 单个实际 Word 已完成，不能替代最终饱和单子 |
| generator、indexed probe 和呈现 | 已有函数图、字母商判据、old_mul_generator、generator_mul_b、hom_ext | 实际图、exit/transition 关系、presentedHom 存在唯一性、Word 完整保守模拟已证；Path old/probe 方程本批接通，完整扩张待接 |
| Raw.cardinal_le / extension_cardinal_le | 新版 7979336 FiniteSequenceSyntax/Recursion/Numbering/Countable 的四段原证明；已适配 ExistingFiniteSequenceBounds.fseq_bound_l | 全内部有限序列统一编号，无可数选择；实际消费者 OpenAI MonoidBase:215。两个原核证书见 ConstructionProbeWordCardinality |

本批只调整四段有限序列证明的 import 和外围 namespace，逐段比较与供体一致；没有复制 countable-only 特例、序列 join/lift/end 或供体整棵依赖树。固定底座不变，供体未修改。42 项声明及两个原核证书通过完整验收，没有新增可信依赖，实际记录见 STATUS。

映射路径／字母批次：原生 exists_compositionFunction 直接构造 node 像图；既有 exists_factor_table/exists_terminal_table 给目标表，乘法保持证明原 map_factor/map_terminal。实际字母图调用原生函数构造，复用 letter_eq_iff、transition_total/transition_unique；单射反映保留原共同阶段论证，不增加过渡映射单射性。消费者是 ProbePresentations.alphabetSimulation，动作／exit／锥及实际 AlphabetSimulation 已接通；Raw 实际传输与 reduced Word 单射已接通；Word transportHom 和 oldHom 四字段保守性已接通；Word 之间完整保守传输已接通；Path/probe 方程本批接到同一实际 H，完整扩张仍待装配。本批没有新增递归或商后端。

字母模拟批次直接消费已存在的 exists_graph/map_letter/graph_injective、FactorMap/TerminalMap 和 inCone_letter_iff。原 Conservative.factor_eq 用旧因子保持与单射性恢复指定因子；再经共同阶段锥判据证明原 lettersMap_inCone_iff。没有新建序列、递归、满足关系或完备性后端。对象证书只证明原 AlphabetSimulation 的四项相容性，不声称已证明 Conservative 的全部四字段或 Word.transport_conservative。

Raw/Word 传输批次复用 exists_node_map 中的原生函数复合、现有 finite sequence 长度唯一性及 prefixHead/reduced 判据。原 Raw.transport 的字面映射由内部序列逐项复合和末端映射实现；已证 headDiv/reducedness/oldAct 保持。Word.transport 直接调用原生 ZF.exists_restriction 限制实际 Raw 图到既有 WordCarrier，不新建序列或 Word 后端。三个原核证书的依赖分别为 10/16/16 项；后两项包含先前已有并重算的六项序列限制 Bool 证书，没有新增可信依赖。

transportHom/oldHom 保守性批次：直接消费现有 Raw 归纳、Word 求值、乘法图、ConeLaws 和 EmbeddingLaws；没有新增递归、商、锥或完备性后端。两条原核证书各 22 项依赖，来自既有标准三项、七项基础句子与两组六项序列限制证书。oldHom 完整四字段已接通，共享 gate 及 Word-to-Word transport_conservative 后续已接通。

head/Gate 批次：直接使用已有 cases_raw/cons_injective、headDiv_cons_iff、eval_cons_iff、oldAct_mul、old_dvd_iff_headDiv 和 Word 单子律。头部传输使用既有 Raw Value 的构造子方程；共享旧交只组合已经完成的 Conservative.common/intersections，不重复证明旧嵌入保守性。四条原核证书继续使用 BMS 式 ModelTransfer.derives。没有新增 Option 后端、外部长度归纳、序列编码或满足关系；共享 gate 存在性随后直接使用该纯公式索引 raw_induction 完成：变化的头部和目标词均置于归纳公式量词内，old/cons 后缀分别消费共享旧交和递归 gate，最终构造两侧实际 exit(s)*u。该结论已取得原核证书，未新建归纳后端。

Word 完整保守传输批次：因子反映直接使用已有 raw_induction、head_transport_some、letterAct_injective 和共享 gate；整除反映复用已存在的通用 division_reflection。共同上界反映复用共享旧交与共享 gate，同头分支消费已有 eval_letterAct（即源生成元乘法的关系形式）。最终四字段通过 common_below、divides_trans 和因子反映组装，再用已有 exists_transport_hom 构造实际图；三个闭句继续走 ModelTransfer。没有重复旧嵌入保守性、重建生成元或加入对象选择原则。基础单子的 ConditionalJoins 和扩张 Word 的条件并是不同义务；后者现已沿源 cone_join 迁移，当前验收见 STATUS。

本轮复审直接回读新版 7979336 的 l_model_zf_l / l_model_zfc_l：任意内部模型、完整模式数学已有，供体工作树干净，未重跑供体编译或修改版本。原核回传仍调用现成 ModelTransfer.derives。Path simulation 批次只组合现有 transport_old/transport_cons、old/cons 唯一性和实际 LettersMap/GeneratorGraph/ProbeGraph；没有新增函数图、递归、编码或完备性实现。纯闭句在同一个存在量词 H 内同时给出保守性和 old/probe 方程。基础 ConditionalJoins 仍是源前提；扩张 Word 的条件并由当前 ConditionalJoins 模块实际证明。

Word 条件并批次：直接调用 ForcingConditionGraphs.exists_identity，特化既有 exists_simulated_gate_of_exit；没有重写 Gate 归纳。old_intersections 只组合既有 old Conservative 的共同上界反映和锥交保持；新的 Raw 归纳严格对应源 cone_join，使用已有 pure-schema raw_induction，并将另一个词与共同上界置于内部量词。等头分支直接用已有实际 generator 乘法与左消去律；源 conical 和 b≠unit 条件保持。最终端点消去 old 保守嵌入、Gate 和 old intersections 前提；原 Word 载体、单位及乘法图构造已直接复用：exists_extension 和最终纯闭句实际给出 W/unit/J/G 见证，验收见 STATUS。
