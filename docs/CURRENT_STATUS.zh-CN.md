# 本地工作进度（2026-11-08）

## 当前迁移：实际 slice_candidate 与内部候选函数族（2026-11-08）

ForcingSliceCandidate.kernel_certificate 是普通 nativeZF 原推导核的 Derives 端点，证明同一内部 L 上的实际候选函数族定理。背景 Choice／全局序由已有 ConstructibleSource／ConstructionRoundSelection 消去；没有新增外层 AC、L、公理模式或名字递归。给定原源父输入（同一 Core、已有共同支撑、实际 Cartesian 名字及两条完整满射），精确迁移 SliceAssembly.slice_candidate:118–156 的两个分支，并保留全部内部条件及任意内部指标。

良序像分支复用完整 wellorderable_target_injection；非良序分支只在一个较强条件下取一个实际 HS 默认成员，复用 subset_image_surjection、两次同系统 nonwellorderable_image_bijection、原逆图和复合。结果是反向单射，不额外要求成为原 f 的截面。六个现有辅助接口仅去掉 private，数学正文保持不变；删除了对这些图运算的重复实现。

实际双名字参数关系的四项 UniformMaximum.Inputs 现在全部证明，包括 force(ex injection)。candidate_family 已实际调用已有 uniform_maximum_dense，构造全内部指标上的 FunctionOn 候选函数族及其一个共同支撑；没有另造参数族图，也没有把候选族当作前提。

本批全量验收以 verification/slice-candidate-acceptance.json 为准，报告产生前仅算局部通过。仍处原第9阶段；下一真正义务是固定源 assemble／presentation_reverse_injection，再接全局反向单射。实际 ACwo、¬AC、ordinal_presentation、切片名字、图满射／互斥／覆盖、空域及参数全域唯一等均已完成，不重做。PP/Main、全部内部／非标准 Proof/Con、原第4 Comparator和终验仍未完成；最终对象 Con 未证明。

## 本批迁移：源子集像满射（2026-11-08）

ForcingSubsetImage.kernel_certificate在普通nativeZF原核中构造SliceGeometry:17–69的实际共同支撑及bounded-default原始HS图，保留所有内部条件上的完整subset_image_surjection。唯一性只消费原函数在其定义域上的mapsTo，不添加全局偏函数唯一性；默认元素仍是源显式给定的单个元素，不同时选择一族默认。图的functionOn／无杂项／mapsTo／onto全部保留。直接复用已有默认关系、TupleStabilizer、relationOf／actual_reuse、关系图满射及函数消去规则，无新Choice、L、收集器或基础设施。

本批验收见verification/subset-image-acceptance.json。当前仍为原阶段9；完整ordinal_presentation、实际ACwo、¬AC、L及全公理模式已完成。余下沿固定OrderedSections及剩余SliceGeometry／SliceAssembly接全局反向单射，不把已完成的子集像满射或现有基础重新列为待从头实现。PP/Main、全部内部／非标准证明码Con、Comparator及终验仍未完成。

## 当前迁移：完整 ordinal_presentation（2026-11-08）

ForcingPresentationCover迁移固定源OrdinalPresentation的presentationPartial_cover与ordinal_presentation。实际全部索引／规范偏映射家族、支撑图式扩张、全内部条件上的稠密覆盖、内部序数重新编号及完整完成图满射现在已连通。输出实际序数、check名、字面Cartesian域及HS满射图；不给定家族、覆盖、枚举、Cartesian域或满射，也没有名字秩截断。重新编号复用已有内部序数满射枚举及原生函数复合，正向值／全部记录提升两条定律实现源序数等价在结论中的作用。

对象端点ForcingPresentationCover.kernel_certificate为原推导核的Derives nativeZF []，目标是上述源定理模式的L相对化句。语义引理中的背景Choice由已经完成的内部L模型及其Choice证明消去，不添加外层AC前提，也不重建L／公理模式。10项声明的trust=0局部检查已通过，完整工程验收以verification/presentation-cover-acceptance.json为准。

当前仍为原阶段9：源ordinal_presentation已完成，下一沿Main.reverse_injection_dense复用已有关系图／统一选择／非良序像双射，迁移固定源OrderedSections、SliceGeometry、SliceAssembly并接全局反向单射；不额外设立未被源码消费者使用的SVC公理包装任务。实际全条件ACwo、¬AC、L及全公理模式均已完成并保留。第10 PP/Main及全部内部／非标准证明码Con、第11终验及原第4 Comparator仍未完成。最终对象Con未证明。

## 前批验收：实际RootProbes及ACwo对象逻辑桥

ForcingRootProbes消费同一Core已有的AllIdeals／最终Row，在实际单元单点理想上直接取得同一探针族，证明原Source RootProbes的乘积与独立右锥定律，并证明探针索引内部不可数。原nativeZF／FirstOrder.Derives端点强化同一个内部L的40集合存在句，保留完整Core、商、非良序像及¬AC强迫结论；没有新建饱和历史或给定探针族前提。探针索引按源K=μ.ord.ToType对应env13，Cohen坐标κ=ω₁对应env14。

ForcingOrdinalChoice迁移原完整nonemptyFamily／choiceForFamily／familyMember逻辑及函数唯一性消费者，并取得原核中的精确等价：全部内部条件上的ACwo强迫，等价于保留全部内部序数、族、选择名量词的DenseChoice合同。完整functionOn子句均保留。这个端点自身是逻辑桥；实际DenseChoice和forces_ACwo现已由ForcingActualOrdinalChoice构造并消去其前提，不再列为待做。

完整本地验收：3206构建任务、37326项声明；全部37297项旧足迹不变，29项新增；9条命令（5条trust=0）均退出0，零警告、无新增公理依赖，2764个当前文本哈希匹配完整验收快照。旧迁移模块源码不变；6个本批临时文件已精确清理，清理后构建退出0。报告：verification/ordinal-choice-acceptance.json。

兼容性修复后连续六轮远端CI完整成功。最新42405610709（1ed6c36）的实际日志确认37478项声明通过、零警告，固定检出／依赖／源码及五项跨平台回归全部通过。后续每批先完成本地全量验收，再统一推送；不叠加尚在运行中的提交。

当前仍为原阶段9。witness_placement、localized_existential、localized_maximum、indexedGraph、ground_family_choice、ground_family_choice_dense及实际forces_ACwo已迁移，源ordinal_presentation现已完成，下一沿Main.reverse_injection_dense接全局切片单射及PP/Main。原第10 PP/Main与全部内部／非标准证明码Con、第11终验及原第4 Comparator保持未完成。最终对象Con未证明。






本分支迁移固定 OpenAI PPAC 源证明到 YesMetaZFC 的原对象推导核，继续采用原计划 1–11 阶段。原第 8 阶段的全局装配门已通过；当前为第 9 阶段，固定源kernelGraph／同值类／imageClassRelation、实际像商图、源复合／逆图及同系统非良序像双射／¬AC强迫、实际RootProbes和ACwo逻辑桥已迁移，最终目标尚未完成。

最终目标：`FirstOrder.Derives nativeZF [] (Con_ZF → Con_U)`，其中 `U = ZF + PP + ACwo + ¬AC`。内部 Con 必须覆盖全部内部证明编码，包括非标准编码。

## 必要的后续工作

1. 第9阶段：固定源非良序像双射:243–276已完成；源ordinal_presentation和实际全条件ACwo已完成；继续在同一系统完成全局商编码单射，¬AC强迫应用已完成。kernel、完整imageClassRelation、实际imageQuotient及像图的完整函数定律均已完成；复用现有关系图构造、完整函数定律、序数及原非良序商双射；RelationCalculus 的逆／复合名字图也已迁移，同系统非良序像双射也已连接完成。
2. 第 10 阶段：接通完整 PP/Main，复用 ZF/U 的既有 Proof/Sat 配套完成全部内部／非标准矛盾码传输及最终 Con。
3. 第 11 阶段：最终对象推导主句、干净检出复现及剩余验收；原第 4 阶段 OpenAI Comparator 仍单列未验收。

复用 YesMetaZFC 与已固定伴随仓库中已有的 L 解释、全体公理模式、递归及 ProofSat 基础。不得把这些已存在的基础重新列为待从头实现。
