# 原 1–11 阶段迁移流程（2026-11-08）

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






| 阶段 | 原任务与输入 | 已有实际成果 | 真正还需要完成／验收门 |
|---|---|---|---|
| 1 | 语言桥接 | SourceSyntax、SourceStatements、Translation、Contract；全八构造器、首末 binder 及原核连线已验收 | 已完成，保留；不重做 |
| 2 | 句法与源推导传输 | 重命名、替换、有限支撑、19 规则及反向编译，原核 Derives 证书 | 已完成外部证书迁移；内部任意码归约归阶段 10，不回滚本项 |
| 3 | 全理论对应 | 完整 Separation/Replacement ↔ 原 Separation/Collection，全部固定公理、两种 AC；ZF/U 双向回放 | 已完成；不得把完整模式再报成未证明 |
| 4 | 原 Lean 4.34.1 外部基线 | 固定源 78 份副本哈希全部匹配；原 Main 完整构建 8998 任务通过；五个关键端点以 --trust=0 审计通过，仅标准三项依赖 | 完整 Comparator 仍未运行，缺 Linux/landrun；本仓 CheckStep4 不是此验收。原 4.34.1 环境与目标 4.33.1 保持隔离 |
| 5 | 内部名字、图、元组、递归 | 对象配对／图／ω／序列／内部递归、Def 与历史接口已验收；原 Child 归纳、IsName、evaluate、mapConditions 及作用律已验收；checkName、pairName、unionName 的精确构造、求值及条件作用均已验收 | 本基础名字包不再列为待做；实际统一条件／群作用、HS 实例及强迫公式解释也已接通。第 8 的具体单子已实际构造；剩余消费者为 9–10 的模型应用与全局目标装配；不重造现成基础或重启字节兼容 |
| 6 | 背景、解释、universe | 供体完整 L/ZFC 已在固定旧版复用；原生与源语言逐公理／全模式、Choice、全局序及非空原核证书齐备。ConstructibleSource 逐点域对应、源 binder 对应、解释背景和非空前提实际消去，既有 InterpretedZF 已被真实消费 | 原 f28b033 第 6 行固定背景／universe、逐实例 Derives、不加不可达的验收门已完成；不再列作待做。全部内部／非标准 Proof/Con 归 10，不重证 L 或增加 GCH |
| 7 | 源强迫前端 | 原子／公式／固定证明保真、实际作用／正规滤子、全秩 HS、七条固定公理与完整 Separation／Replacement 已验收；已接通原 forces_ZF，逐源公理／模式有原核证书 | 前端合同已闭合，保留原单子／呈现／正规滤子前提；第 8 的原核存在句现已提供实际具体构造；第 9 消费这些父输入。全部内部公式／证明码归约仍属 10；不能把此逐实例证书说成最终内部 Con |
| 8 | 源代数／构造核心 | 同一 Base/T、完整实际饱和历史／转移／最终行、理想／基数、纤维／粘合、标签／传输、完整选择器／轨道／记录族和 Assigned 图已验收；具体商双射及完整 nonwellorderable_quotient_bijection 已验收；ForcingConcreteSystem 的无参数原核存在句实际构造全部 37 原始条件／40 内部集合，并在同一见证上消费全称商结论 | 本阶段所列全局装配门已完成；第 9 阶段消费同一具体系统，不重建原基础 |
| 9 | 源模型应用 | 同一实际Core、ACwo、¬AC、ordinal_presentation、完整切片／候选族／assemble及presentation_reverse_injection均已接通；全集合reverse_injection_dense及实际forces_PP有普通nativeZF原核L相对化端点 | 本阶段模型应用链完成；PP前没有给定稠密性、满射或HS名字前提；保留全部内部量词 |
| 10 | 原 Main 全局装配与对象内部化 | reverse_injection_dense→forces_PP已接通；最终内部Con规格固定，专用内部检查器尚未闭合 | 接forces_target／Main；复用既有ZF/U ProofSat，在ZF内证明全部内部及非标准矛盾证明码归约与最终Con蕴含 |
| 11 | 终验与发布评审 | 现有审计工具可复用；最终验收未开始 | 核对源到目标对应、命题量词、依赖及原核主句；发布另按用户授权，不把辅助构建通过当最终通过 |

## Agent 执行入口

| 顺序 | 固定源消费者 | 复用输入 | 验收门 |
|---|---|---|---|
| 8 已完成 | ConcreteSystem.Vertex.permute/Arrow.move/Common.move；QuotientTransport.ReindexIso.gluedEquiv_toGlued:252–293 | 原图置换、完整顶点/箭头/Common、实际纤维限制图、实际整个分量商与 toGlued 交换律均已消费 | 两个普通 nativeZF 原核端点；全量验收见本批报告。未宣称整个 RootGroup 的单位/复合作用律已迁移 |
| 8 已完成 | QuotientTransport.eligibleSystemTransport:309–337 | 已有逐图 assemble_app、Data 唯一性和原生函数构造器；两侧已有对象/限制族 | ForcingEligibleReindex.construction_kernel_certificate 同时构造全 app 函数并证明 Apps/Natural；不再列作待做 |
| 8 已完成 | QuotientTransport.rebaseGlued/componentEquiv:353–421 | 现有 Common 传递性、同一商集/投影、全分量传输及自然性 | ForcingComponentRebase.construction_kernel_certificate 将目标换回原根，保留同一双射图；原组件稳定条件显式保留 |
| 8 已完成 | component_selector_dense → OrbitAssignments → assignmentGraph_bijection → quotient_bijection_above → nonwellorderable_quotient_bijection → 同一具体系统全局实例 | 同一实际塔／hRec／hMatrix／最终行、全部内部参数／商／记录及图构造器已复用 | ForcingConcreteSystem.kernel_certificate 无系统输入地存在量化全部内部见证，并全称消费源商双射；全量验收见 concrete-system-acceptance.json。下一活动行是 9 |
| 9 已完成 | 源模型应用链 | 全集合反向单射及实际PP的同一系统原核端点已接通 | 不重做已完成的L、公理模式、呈现、支撑、切片或稠密反向单射 |
| 10 当前 | PP／Main 和内部矛盾码归约 | 源反向单射链；底座 ObjectProofNode/ReducedProofPresentation/PureProvability/Sat | ZF/U 全模式专用公理检查、全部内部/非标准证明码的正确性及原核内部 Con 蕴含 |
| 11 | 最终交付 | scripts/verify.py、源锁/足迹/原核端点 | 最终主句、完整理论/语言/背景核查及干净检出复现；当前本地验收不替代终验 |
| 4 独立未验项 | 原 Comparator | 隔离原 Lean 4.34.1 的 Main 与五端点已通过 | Linux/landrun；本仓 CheckStep4 不是 Comparator |

源码与精确依赖由 SOURCE_LOCK、THEOREM_COVERAGE 保留。新辅助引理必须有当前源主线消费者；不恢复 Packet/reader、leastCode 或 classFiber_dense_lower 旁支，不重复完整 L、公理模式、递归、Proof/Sat、函数或商后端。无实际调用的 localName_of_raw 和顶点 quotient/zigzag API 不作为前置。发布按用户已经明确授权的范围执行。

历史分批验收及已被后续完成的旧待办保留在 Git `6a0a3d0`；当前待办只以上表和页首执行入口为准。
