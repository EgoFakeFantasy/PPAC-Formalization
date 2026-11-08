# 本地工作进度（2026-11-08）

## 当前验收：全集合反向单射及实际 PP（2026-11-08）

ForcingReverseInjection 逐源迁移固定 Main.reverse_injection_dense:133–148、forces_PP_of_dense:90–121 与 forces_PP:151–152。非空分支复用已完成 ordinal_presentation，实际构造内部序数、check／Cartesian 名字、HS 满射及五名字父支撑，再消费 presentation_reverse_injection；空分支复用原满射 onto 与 empty_domain_injection。保留所有内部条件、集合、全秩 HS 名字与完整 functionOn／无杂项子句。

普通 nativeZF 原核 kernel_certificate 证明同一内部 L 上的合取句：同一 Core 与 p∈P 直接推出实际完整 PP 强迫；另一合取项给出任意 HS 满射的稠密反向单射。PP 外层没有满射／HS 或给定稠密性前提。辅助语义的 Choice 与全局序由既有同一 L 解释消去，不新建基础。

本批完整验收以 verification/reverse-injection-acceptance.json 为准；报告生成前仅为局部通过。验收通过后原第9阶段模型应用链闭合，当前进入原第10阶段：接 forces_target／Main，再复用现有 ZF/U ProofSat 配套完成全部内部及非标准矛盾证明码归约与内部 Con 蕴含。原第4 Comparator 和第11终验仍未完成。最终对象 Con 未证明。以下旧批段落是历史记录，当前状态以本段及原阶段表为准。

CI 修复 bc9367f 已上线：先 lake update、固定三个源码／依赖、仅规范 CRLF→LF 文本哈希。修复后连续11次 Linux 全量成功；最新完成的42444551725实际日志确认37867项声明、零 Lean 警告，固定源码检查及5项跨平台测试均通过。本轮3个固定仓／75源码哈希与5项跨平台回归复跑全部通过；未关闭任何验收门。

## 当前迁移：实际 presentation_reverse_injection（2026-11-08）

ForcingSlicePresentation.kernel_certificate 在普通 nativeZF 原推导核中证明同一内部 L 上的固定 SliceAssembly.presentation_reverse_injection:161–191。保留原 SliceData 父输入（同一 Core、原父支撑、内部序数、实际 Cartesian 名字及两条完整满射），在证明内部实际构造候选 FunctionOn 族及其支撑、取现有 KP／正规滤子／子群交集，再消费完整 assemble，得到较强条件上的实际 HS 反向单射。

新绑定只容纳这些已构造见证。parameter_pullback 从实际 check／B／Ypart／Spart 选择与分离方程严格回传同一原始名字；既有图传输保留同一 Cartesian 名字。不提供候选族或新的共同支撑前提，不另造参数族图、Choice、L、收集器或递归。五项已有上下文／图辅助接口仅公开，证明正文不变。源语义辅助中的 Choice／全局序仍由已经完成的同一内部 L 消去。

本批全量验收以 verification/slice-presentation-acceptance.json 为准，报告产生前仅算局部通过。仍处原第9阶段；下一真实消费者是 Main.reverse_injection_dense 的全集合归约：非空分支复用已完成 ordinal_presentation 与本端点，空分支复用已完成 empty_domain_injection；不重做这些基础。slice_candidate、候选族、assemble、支撑交集及 presentation_reverse_injection 均不再列为待做。随后接 forces_PP／forces_target／Main、全部内部／非标准 Proof/Con、原第4 Comparator与终验；最终对象 Con 未证明。

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
