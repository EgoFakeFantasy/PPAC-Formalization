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

## 当前必要源消费者

- 原 AtomicForcing.relations/mem_iff/eq_iff 与 atomic_laws → SymmetricNames.atomic：原子递归和基础定律已完成。
- 原 eq_of_dense/mem_of_dense → SymmetricNames.atomic_regular：实质引理已完成，不再重证。
- 原 edge_map_orderIso/atomic_symmetry → SymmetricNames.forces_symmetry/mem_symmetry/eq_symmetry：本批 ForcingAtomicSymmetry 复用已完成名字映射、pair 归纳、精确方程及 actCode；序保持仅要求在内部 P 上。
- 本批 ForcingFormula / ForcingSound 已消费原 ForcingQuotient.Force、ForcingTruth.force_of_dense/forcing_sound，取得固定公式与固定源证明实例的原核证书；实际 HS 定义和通用公式作用对称性实例现已接通；具体 PPAC 系统解释仍待接。

决策稠密集、atomic_truth、exists_truth_generic 属于泛滤求值分支，已从当前必需待办删除；不因同在源文件中就依次全部移植。具体源条件呈现、全秩 HS 与后续代数／模型主链仍须完成。NatPacket 字节兼容冻结。

本批公式层重用原子定律而不假定 AtomicData 字段；rename 的 binder 对应直接调用已有 DefinableMinimaChoice.lift_assignment。沿用 Source.Derives 的原 19 构造器，没有新增推导核。有限前提与名字域守卫仅在既有 Source AST 中合取打包，最终仍用 ModelTransfer.derives 返回原核证明。六构造子 Basic 是锁定源语法的摘录；源码只用于泛滤的 Countable 派生未搬入，不重建满足关系或内部码识别。

本轮 ForcingFormulaSymmetry 继续消费既有 atomic_symmetry、mapping、action_transport、toBasic 和 conjunction_semantics；返回原核的 ModelTransfer.derives 仍直接使用已有 strong_completeness/PureRosserSchedule。没有重建群作用后端、满足关系、检查器或完备性。一般 H 的双向名字见证前提只是原 N ≃ N 所使用的两个存在方向的对象化；实际 HS 的两个条件已由本轮 ForcingHSAction.domain_transport 证明，但保留具体系统须提供的代数 Context。已重新读取上述 LCarrier 两个完整模型定理和 LCarrier 的 ZFSet 子类定义，未把该单个模型套入任意 nativeZF 模型的前提。


本轮 ForcingHS 的内部闭包证明直接调用固定 Collection.collection_exists_d，并用现成 Separation 删除收集见证中的多余元素，再用 KP.exists_union/exists_insert 拼接；没有另造 Replacement 或选择见证函数。定义唯一性调用已验收 ForcingNameInduction.kernel_certificate；check_HS 使用 ForcingCheckName.formula_induction、edge_checkName 和 ForcingCheckNameLaws.action_fixed。稳定子通过既有 actFormula/mapConditions 定义，未把 Symmetric 或 HS 作为假设字段。通用 HS.smul 已由 ForcingHSAction 迁移；具体群／正规滤子仍待实例化。


下一实际源实例已核对：ProductNames.system 使用 Γ = Equiv.Perm I 与 SupportFilter.subgroupFilter μ；ConcreteSystem.S 消费同一系统。现有 ForcingConditionGraphs 的恒等、逆、复合已用于标签集合 I，稳定子共轭已接通；原小支撑滤子的四条正规性现由 ForcingNormalFilter 构造，剩余为 actionHom 及非平凡性，不新建通用群论库。源 IsNormalFilter 的四项是顶、向上闭包、交和共轭闭包；其小支撑滤子构造与基数前提仍按原源码迁移。仅以文件名搜索未发现同名供体，不据此断言其他仓库不存在可用数学。

ForcingHSAction 的稳定子共轭复用 ForcingConditionGraphs.exists_inverse/exists_composition、ForcingConditionAction.name_composition/name_inverse。HS.smul 直接沿原 Child 归纳，消费 ForcingHS.intro_hs/child 和 ForcingMapConditions.edge_mapping；公式对称性直接消费已有 conclusion_models/action_transport。四类证书全部返回 ModelTransfer.derives，未新增核或对象选择原则。NormalImage 只表达原正规滤子的共轭条款，不声称已构造具体小支撑滤子。

标签实例：ForcingLabelPermutations 用底座函数空间与原 Separation 构造全部置换和 Fix J，闭包只调用既有 exists_identity/exists_inverse/exists_composition。ForcingLabelConjugacy 沿 SupportFilter.conjugate_fix 证明两个成员方向，复用现成 Conjugate/Image 公式和 function_unique。集合编码共轭图及稳定子精确像现已由 ForcingConjugationGraph 接通；小支撑基数／正规性现已由 ForcingSupportIntersection / ForcingNormalFilter 接通。

本轮 ForcingConjugationGraph 直接调用 FunctionConstruction.exists_setFunctionFromTo_of_denote、Model/SetTheory/FunctionSemantics.IsSetRelation.eq_of_pairMember_iff 和既有 binary_semantics；未新增函数图后端。Subgroup 的对象公式复用既有 closed，证明实际共轭保持其三种运算闭包，供源 conjugate_mem 使用。

后续支撑界已定位的供体：SetTheory/Card/Aleph/Multiplication.lean:345 `infiniteCardinal_selfMultiplication`。精确前提为 Models ZF、已解释有序对约定、IsOmega ω、IsCardinal ω、IsInfiniteCardinal ω κ，结论 IsCardinalMultiplication κ κ κ。现已连同新版 Card/Omega、Card/InfiniteBound 的五个原证明适配；内部 ω 的基数性也已消去，不重建该数学。

## 本轮复用审查纠错

此前仅检查锁定旧底座与 ZFSet LCarrier 工程，遗漏新版底座的任意模型内部 L。新版定义 `l_model_l` 的域是 `{x : M.Domain // L_d x}`，M 是任意内部 ZF 模型；与旧 LCarrier 的模型范围不同。实际 ZFC 消费完整 Separation/Collection，并由 Jensen 全局良序得 Choice，无额外对象 AC 前提。

ZFC 端点依赖闭包 223 模块，相对固定 039c8e1 缺 142 模块、28 模块不同；不能仅拷贝两个终点或直接改 import。后续先移植所需扩展及语言对应，消费现成定理，停止扩写旧的独立 L 构造路线。现成 GCH 只作资产记录，不加入当前必经路线。原生 ZF 端点审计为标准三项及七项已有 FreeClosed 证书；ZFC/GCH 另含 Choice 句子的 FreeClosed 证书，不能误报为向背景添加 AC。

同一新版库还有内部强迫名字、自动同构及 ZF 保持接口；尚未核对它们与 OpenAI 的 HS 受限强迫完全一致，不能据名称直接替换 SymmetricChoice.forces_ZF，也不将这些已有数学报为不存在。下一次扩写类似基础前必须先核对这些接口。

本轮实际已消费的底座接口：ForcingSupportSize 使用 `exists_setInjectionFromTo_of_denote` + `inverseValue` + `exists_compositionInjection`；ForcingSupportFilter 使用原幂集／分离、实际 Fixing 和共轭像。小支撑族、有限并／置换像大小界和完整四项正规性已构造；具体 actionHom 和非平凡性仍待接。数学背景和源消费者不变。

本轮直接消费新版供体 `omega_skip_l / omega_not_le_finite_l / omega_cardinal_l / infinite_product_l / infinite_union_two_l`；五段正文保持原样，未使用该文件中无消费者的 insert 定理。ForcingSupportIntersection 的消费者是源 inf_mem，ForcingNormalFilter 的消费者是源 ProductNames.system。依赖固定底座的基数算术新增消费 9 项现有 native Bool 证书（IsOrdinalMaximum.mem 六项、omega_selfMultiplication 三项）；重新计算并锁定，不冒充 kernel reduction 或依赖范围不变。

本轮对 L 版本接口的抽查发现 Project/Syntax 的差异只是 DeriveFreeClosed import 改名，Logic/Syntax 的所读差异为排版；不能把“28 个文件不同”解释成 28 项新数学工作。完整扩展移植仍需按实际依赖逐项核对，当前没有整体替换固定底座。
