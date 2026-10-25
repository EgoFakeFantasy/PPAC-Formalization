# 现成接口复用与精确边界（2026-10-26 重审）

本表取代重复的逐批进度叙述；旧验收段可从 Git `629b815` 恢复。固定 YesMetaZFC 为 `039c8e132cc19671d73a3933c66b4799d2599dd6`，本轮未更新依赖或修改其他仓库。源码位置与依赖指纹以 SOURCE_LOCK 为准。

| 已有资产 | 精确入口／本仓实际消费者 | 正确状态和边界 |
|---|---|---|
| 完整 ZF 模式 | YesMetaZFC/SetTheory/Axioms/ZF.lean 的任意参数 separation/collection；ReverseZFReplay、CollectionFromReplacement | 已完成并消费，不能再报为数学缺口 |
| 集合配对、并、插入、积、分离、收集 | KP.exists_pair/exists_union/exists_insert、ZF.exists_cartesianProduct、Collection.collection_exists_d；KuratowskiZF、ForcingNames、ForcingAtomicRecursion、ForcingHS | 已消费。内部 Collection 见证族经 Separation 过滤再合并；不抽取对象选择函数 |
| 内部序数递归 | SetTheory/Ord/Recursion.lean:1297 recursiveSequence_exists、1322 recursionValue_exists、1339 transfiniteRecursion_isClassFunctionOnOrdinals；GodelDefRecursion、ConstructibleHistory | 已消费全部内部序数接口。另一个 WellFounded.Recursion.solve 要求宿主 WellFounded，不能用于任意可能外部不良基的 nativeZF 模型 |
| 集合／名字归纳与递归 | SetInduction.native_induction → ForcingNameInduction/ForcingMapLaws → ForcingPairInduction/ForcingTripleInduction；ForcingNameRecursion | 已消费到名字、映射、原子递归和定律；后两种归纳有实际证明消费者，不是待重建后端 |
| 内部函数空间 | FunctionSpaceConstruction.lean 的 ZF.exists_functionSpace；ForcingLabelPermutations.exists_carrier | 本轮直接消费其全部内部函数图集合，再分离置换；没有重建幂集／积或函数空间。固定源文件哈希纳入 SOURCE_LOCK |
| 条件图构造 | SetTheory/FunctionConstruction.lean 的实际恒等、逆、复合图入口；ForcingConditionGraphs/ForcingConditionAction | 已消费，保留指定图的精确边方程。具体 PPAC 群同态族未实例化 |
| 原核收尾 | BMS SecondOrderCompleteness.derives_m 的 strong_completeness 模式；本仓 ModelTransfer.derives/project_models_iff | 已接入纯成员语言、对应 Type 0 全模型。不是待重做的完备性；不能拿单个 LCarrier 模型冒充其全模型前提 |
| L 的完整模型数学 | lean-constructible-universe-stage4 固定 7f5a7d0；ZFModel.lean:28 lCarrier_models_ZF、StageHistoryGraphSystem.lean:171 lCarrier_models_ZFC | 已完成，包含完整模式。Model.lean:52/96 的 LCarrier 为 ZFSet 子类；到本项目任意 nativeZF 模型的对象解释接口仍未闭合。不能据此宣称其他位置没有实现过该接口 |
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


下一实际源实例已核对：ProductNames.system 使用 Γ = Equiv.Perm I 与 SupportFilter.subgroupFilter μ；ConcreteSystem.S 消费同一系统。现有 ForcingConditionGraphs 的恒等、逆、复合已用于标签集合 I，稳定子共轭已接通；剩余为原 actionHom 与小支撑滤子，不新建通用群论库。源 IsNormalFilter 的四项是顶、向上闭包、交和共轭闭包；其小支撑滤子构造与基数前提仍按原源码迁移。仅以文件名搜索未发现同名供体，不据此断言其他仓库不存在可用数学。

ForcingHSAction 的稳定子共轭复用 ForcingConditionGraphs.exists_inverse/exists_composition、ForcingConditionAction.name_composition/name_inverse。HS.smul 直接沿原 Child 归纳，消费 ForcingHS.intro_hs/child 和 ForcingMapConditions.edge_mapping；公式对称性直接消费已有 conclusion_models/action_transport。四类证书全部返回 ModelTransfer.derives，未新增核或对象选择原则。NormalImage 只表达原正规滤子的共轭条款，不声称已构造具体小支撑滤子。

标签实例：ForcingLabelPermutations 用底座函数空间与原 Separation 构造全部置换和 Fix J，闭包只调用既有 exists_identity/exists_inverse/exists_composition。ForcingLabelConjugacy 沿 SupportFilter.conjugate_fix 证明两个成员方向，复用现成 Conjugate/Image 公式和 function_unique。集合编码共轭图及稳定子精确像现已由 ForcingConjugationGraph 接通；小支撑基数／正规滤子仍待接。

本轮 ForcingConjugationGraph 直接调用 FunctionConstruction.exists_setFunctionFromTo_of_denote、Model/SetTheory/FunctionSemantics.IsSetRelation.eq_of_pairMember_iff 和既有 binary_semantics；未新增函数图后端。Subgroup 的对象公式复用既有 closed，证明实际共轭保持其三种运算闭包，供源 conjugate_mem 使用。

后续支撑界已定位的供体：SetTheory/Card/Aleph/Multiplication.lean:345 `infiniteCardinal_selfMultiplication`。精确前提为 Models ZF、已解释有序对约定、IsOmega ω、IsCardinal ω、IsInfiniteCardinal ω κ，结论 IsCardinalMultiplication κ κ κ。本轮只核对入口，尚未完成支撑并的适配，不把该既有定理报为待重建。
