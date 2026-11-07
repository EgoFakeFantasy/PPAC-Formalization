# 本地工作进度（2026-11-08）

## 当前迁移：OrbitNames 实际偏轨道图（2026-11-08）

ForcingPartialOrbitGraph迁移固定源OrbitNames:254–359，为presentationPartial构造实际偏轨道图。普通nativeZF原推导核中的kernel_certificate实际生成中心、(top,root)激活条件、中心标签、有序对种子和全群收集图；输出HS、全群固定、自应用、全部内部条件上的偏函数唯一性及输入标签在实际标签集中的成员性。原始Graph逐项规定全部集合成员，排除杂项；成员／应用等价保留真实移动激活条件及名字作用。

唯一性直接复用已有标签分离、内部共同下界的图式单射代数及早已完成的name_eq_of_same_diagram；没有假定偏函数唯一性。作用族、激活族、collect／HS／固定性、标签／标签集及有序对均复用已有实现，没有新建这些基础。全部内部条件、无秩上限HS名字及源显式模型／非可数性／编码／支撑前提保留，不增加对象Choice或L前提。

当前仍为原阶段9。辅助completionGraph_surjection、实际全条件ACwo、¬AC及L／全公理模式原核设施已完成。本批实际轨道图尚未组装成PresentationIndex／presentationPartial内部家族；下一需要该家族及实际稠密覆盖，再复用已有内部序数枚举取得ordinal_presentation／SVC，然后接全局反向单射。第10 PP/Main及全部内部／非标准证明码Con、第11终验和原第4 Comparator仍未完成。最终对象Con未证明。验收登记：verification/partial-orbit-graph-acceptance.json。

## 前批验收：实际RootProbes及ACwo对象逻辑桥

ForcingRootProbes消费同一Core已有的AllIdeals／最终Row，在实际单元单点理想上直接取得同一探针族，证明原Source RootProbes的乘积与独立右锥定律，并证明探针索引内部不可数。原nativeZF／FirstOrder.Derives端点强化同一个内部L的40集合存在句，保留完整Core、商、非良序像及¬AC强迫结论；没有新建饱和历史或给定探针族前提。探针索引按源K=μ.ord.ToType对应env13，Cohen坐标κ=ω₁对应env14。

ForcingOrdinalChoice迁移原完整nonemptyFamily／choiceForFamily／familyMember逻辑及函数唯一性消费者，并取得原核中的精确等价：全部内部条件上的ACwo强迫，等价于保留全部内部序数、族、选择名量词的DenseChoice合同。完整functionOn子句均保留。这个端点自身是逻辑桥；实际DenseChoice和forces_ACwo现已由ForcingActualOrdinalChoice构造并消去其前提，不再列为待做。

完整本地验收：3206构建任务、37326项声明；全部37297项旧足迹不变，29项新增；9条命令（5条trust=0）均退出0，零警告、无新增公理依赖，2764个当前文本哈希匹配完整验收快照。旧迁移模块源码不变；6个本批临时文件已精确清理，清理后构建退出0。报告：verification/ordinal-choice-acceptance.json。

兼容性修复后连续五轮远端CI完整成功；最新已完成的42399254602（10e8c6b）的实际日志确认37442项声明通过、零警告，固定检出／依赖／源码和五项跨平台回归全部通过。已验收的实际ACwo及默认关系统一推送至1ed6c36，其远端42405610709仍在编译，辅助完成图及实际偏轨道图先保留本地，不叠加推送。此后新增工作先完成本地全量验收，再统一推送；不叠加尚在运行中的提交。

当前仍为原阶段9。witness_placement、localized_existential、localized_maximum、indexedGraph、ground_family_choice、ground_family_choice_dense及实际forces_ACwo已迁移，下一沿源SVC／全局反向单射接PP/Main；源SVC／ordinal_presentation及全局切片单射应用也未完成。原第10 PP/Main与全部内部／非标准证明码Con、第11终验及原第4 Comparator保持未完成。最终对象Con未证明。






本分支迁移固定 OpenAI PPAC 源证明到 YesMetaZFC 的原对象推导核，继续采用原计划 1–11 阶段。原第 8 阶段的全局装配门已通过；当前为第 9 阶段，固定源kernelGraph／同值类／imageClassRelation、实际像商图、源复合／逆图及同系统非良序像双射／¬AC强迫、实际RootProbes和ACwo逻辑桥已迁移，最终目标尚未完成。

最终目标：`FirstOrder.Derives nativeZF [] (Con_ZF → Con_U)`，其中 `U = ZF + PP + ACwo + ¬AC`。内部 Con 必须覆盖全部内部证明编码，包括非标准编码。

## 必要的后续工作

1. 第9阶段：固定源非良序像双射:243–276已完成；继续在同一系统完成SVC、ACwo和全局商编码单射；¬AC强迫应用已完成。kernel、完整imageClassRelation、实际imageQuotient及像图的完整函数定律均已完成；复用现有关系图构造、完整函数定律、序数及原非良序商双射；RelationCalculus 的逆／复合名字图也已迁移，同系统非良序像双射也已连接完成。
2. 第 10 阶段：接通完整 PP/Main，复用 ZF/U 的既有 Proof/Sat 配套完成全部内部／非标准矛盾码传输及最终 Con。
3. 第 11 阶段：最终对象推导主句、干净检出复现及剩余验收；原第 4 阶段 OpenAI Comparator 仍单列未验收。

复用 YesMetaZFC 与已固定伴随仓库中已有的 L 解释、全体公理模式、递归及 ProofSat 基础。不得把这些已存在的基础重新列为待从头实现。
