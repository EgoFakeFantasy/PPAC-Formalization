# 原 1–11 阶段迁移流程（2026-11-08）

## 本批验收（2026-11-08）：原阶段9的源复合／逆名字图

固定 RelationCalculus:200–359 已迁移至 ForcingMapCalculus。两个 nativeZF／FirstOrder.Derives 原核存在句分别实际构造对应源元组的稳定子 S 和原始 HS 图 J，保留子群／滤子、精确 tupleFixed、原始收集器及同一支撑。复合图在任意内部条件下保留两份完整原 mapsTo／surjection／injection 输入并证明对应结论；逆图在完整源双射输入下证明完整满射／单射。Total/One/Onto/Injective、移动／同余／正则及应用定律均已消去，不作为输入。

复用现成关系图、稳定子、强迫对称／同余及函数定理；将已有完整函数消去公开为四项别名，原有证明正文逐字节保留。这里迁移的是源 HS 名字图，不以地面置换图或序数最小值逆图代替。下一项仍为 UniformImages.nonwellorderable_image_bijection:243–276 的同一系统连接；序数和完整非良序商结论已有，不重新证明。

完整本地验收：3202 构建任务、37265 项声明；全部37224项旧足迹不变，41项新增；9条命令（5条trust=0）均退出0，零警告、无新增公理依赖，且本批未依赖对象 Choice 证书；2760个规范文本哈希已复核。报告：verification/map-calculus-acceptance.json。

远端兼容修复 bc9367f 的完整 Linux CI 已成功：37209 项声明、零警告，依赖／源码回归及完整原核检查均通过。已上传上一批像商图 7352330，其 CI 正在完整构建，固定检出和源码检查已通过。本批先本地保存，避免叠加触发。远端运行与当前本地批次分别记录。

仍在原阶段9。非良序像双射及 SVC、ACwo、全局商编码单射、¬AC 模型应用尚未全部闭合；第10 PP/Main／全部内部与非标准证明码Con、第11终验及原第4 Comparator仍未完成。最终对象Con未证明。



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
| 9 | 源模型应用 | 第 8 的同一实际 Core／Outcome、通用强迫／对称／HS 后端及 kernelGraph／同值应用／实际同值类、imageClassRelation及实际像商图及源复合／逆图定律原核证书已验收 | 在同一系统接 SVC、ACwo、全局商编码单射、¬AC，沿 UniformImages 等真实依赖保留全部量词；复用已有模式数学 |
| 10 | 原 Main 全局装配与对象内部化 | 原 Main 证明链及最终对象 Con 合同已固定；专用内部检查器尚未闭合 | 接原 reverse_injection_dense→forces_PP→forces_target；复用底座证明图实例化 ZF/U，再在 ZF 内证明全部内部矛盾证明码的归约与最终 Con 蕴含 |
| 11 | 终验与发布评审 | 现有审计工具可复用；最终验收未开始 | 核对源到目标对应、命题量词、依赖及原核主句；发布另按用户授权，不把辅助构建通过当最终通过 |

## Agent 执行入口

| 顺序 | 固定源消费者 | 复用输入 | 验收门 |
|---|---|---|---|
| 8 已完成 | ConcreteSystem.Vertex.permute/Arrow.move/Common.move；QuotientTransport.ReindexIso.gluedEquiv_toGlued:252–293 | 原图置换、完整顶点/箭头/Common、实际纤维限制图、实际整个分量商与 toGlued 交换律均已消费 | 两个普通 nativeZF 原核端点；全量验收见本批报告。未宣称整个 RootGroup 的单位/复合作用律已迁移 |
| 8 已完成 | QuotientTransport.eligibleSystemTransport:309–337 | 已有逐图 assemble_app、Data 唯一性和原生函数构造器；两侧已有对象/限制族 | ForcingEligibleReindex.construction_kernel_certificate 同时构造全 app 函数并证明 Apps/Natural；不再列作待做 |
| 8 已完成 | QuotientTransport.rebaseGlued/componentEquiv:353–421 | 现有 Common 传递性、同一商集/投影、全分量传输及自然性 | ForcingComponentRebase.construction_kernel_certificate 将目标换回原根，保留同一双射图；原组件稳定条件显式保留 |
| 8 已完成 | component_selector_dense → OrbitAssignments → assignmentGraph_bijection → quotient_bijection_above → nonwellorderable_quotient_bijection → 同一具体系统全局实例 | 同一实际塔／hRec／hMatrix／最终行、全部内部参数／商／记录及图构造器已复用 | ForcingConcreteSystem.kernel_certificate 无系统输入地存在量化全部内部见证，并全称消费源商双射；全量验收见 concrete-system-acceptance.json。下一活动行是 9 |
| 9 当前 | UniformImages → Models／具体 ProductNames | 同一具体系统、全秩 HS／正规滤子／强迫前端；kernelGraph／同值类／imageClassRelation、像商图及源复合／逆图已完成，下一非良序像双射 | SVC、ACwo、全局商编码单射、¬AC，保留源全部量词 |
| 10 | PP／Main 和内部矛盾码归约 | 源反向单射链；底座 ObjectProofNode/ReducedProofPresentation/PureProvability/Sat | ZF/U 全模式专用公理检查、全部内部/非标准证明码的正确性及原核内部 Con 蕴含 |
| 11 | 最终交付 | scripts/verify.py、源锁/足迹/原核端点 | 最终主句、完整理论/语言/背景核查及干净检出复现；当前本地验收不替代终验 |
| 4 独立未验项 | 原 Comparator | 隔离原 Lean 4.34.1 的 Main 与五端点已通过 | Linux/landrun；本仓 CheckStep4 不是 Comparator |

源码与精确依赖由 SOURCE_LOCK、THEOREM_COVERAGE 保留。新辅助引理必须有当前源主线消费者；不恢复 Packet/reader、leastCode 或 classFiber_dense_lower 旁支，不重复完整 L、公理模式、递归、Proof/Sat、函数或商后端。无实际调用的 localName_of_raw 和顶点 quotient/zigzag API 不作为前置。发布仍须独立授权。

历史分批验收及已被后续完成的旧待办保留在 Git `6a0a3d0`；当前待办只以上表和页首执行入口为准。
