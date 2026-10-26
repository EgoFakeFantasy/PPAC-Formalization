# 原 1–11 阶段迁移流程（2026-10-26 重审）

阶段编号恢复为最初提交 `f28b0334a740108057adf18a24dc11abd866efbe` 的表。阶段 0 是来源审查前置；下表不再用四项验收或历史 S3/STEP4 批次重新编号。迁移对象始终为固定 OpenAI PPAC 证明，底座为固定 YesMetaZFC 原推导核。

**实际位置：连续完整验收到原 1–3 阶段。4 部分验收；5 基础包已验收；6 接口未闭合；7 仅条件式前端合同已验收，整阶段不能打勾；当前主开发在 8 的原 Probe 路径／扩张迁移，9–11 未完成。不是“前七阶段全过”，也不是收尾。**

| 阶段 | 原任务与输入 | 已有实际成果 | 真正还需要完成／验收门 |
|---|---|---|---|
| 1 | 语言桥接 | SourceSyntax、SourceStatements、Translation、Contract；全八构造器、首末 binder 及原核连线已验收 | 已完成，保留；不重做 |
| 2 | 句法与源推导传输 | 重命名、替换、有限支撑、19 规则及反向编译，原核 Derives 证书 | 已完成外部证书迁移；内部任意码归约归阶段 10，不回滚本项 |
| 3 | 全理论对应 | 完整 Separation/Replacement ↔ 原 Separation/Collection，全部固定公理、两种 AC；ZF/U 双向回放 | 已完成；不得把完整模式再报成未证明 |
| 4 | 原 Lean 4.34.1 外部基线 | 固定源 78 份副本哈希全部匹配；原 Main 完整构建 8998 任务通过；五个关键端点以 --trust=0 审计通过，仅标准三项依赖 | 完整 Comparator 仍未运行，缺 Linux/landrun；本仓 CheckStep4 不是此验收。原 4.34.1 环境与目标 4.33.1 保持隔离 |
| 5 | 内部名字、图、元组、递归 | 对象配对／图／ω／序列／内部递归、Def 与历史接口已验收；原 Child 归纳、IsName、evaluate、mapConditions 及作用律已验收；checkName、pairName、unionName 的精确构造、求值及条件作用均已验收 | 本基础名字包不再列为待做；实际统一条件／群作用、HS 实例及强迫公式解释也已接通。真正剩余消费者为 8–10 的最终具体单子及模型装配；不重造现成基础或重启字节兼容 |
| 6 | 背景、解释、universe | Relativization、ModelTransfer、L 原语法及递归桥；InterpretedZF 已消费全模式回放 | 新版 YesMetaZFC 的任意 ZF 模型内部 L→ZF/ZFC 已定位并验收端点（GCH 不增加为本项目义务）；补其与固定旧版、当前对象语言及原核相对化的接口。停止重证 L 全模式；不把模型定理等同于最终内部 Con |
| 7 | 源强迫前端 | 原子／公式／固定证明保真、实际作用／正规滤子、全秩 HS、七条固定公理与完整 Separation／Replacement 已验收；已接通原 forces_ZF，逐源公理／模式有原核证书 | 前端合同已闭合，保留原单子／呈现／正规滤子前提；第 8 阶段提供具体构造。全部内部公式／证明码归约仍属 10；不能把此逐实例证书说成最终内部 Con |
| 8 | 源代数／构造核心 | Base 与初始 margin；实际 Path／字母／Alphabet／Word 单子、old 嵌入、generator／indexed probe、呈现唯一性、大小界；mapped Path、AlphabetSimulation、实际 transportHom、oldHom 与 Word 完整保守性、共享 Gate。Path old/probe 方程与保守性已接到同一实际映射；实际 Word 载体／乘法／单位及左消去、conical、条件并已统一构造；初始 probe 全 profile 已验收；同一扩张的 old gates 和全部旧 profile 保持已验收；实际模拟的任意内部目标单子 pushout 已验收；letterFloor 实际图及上下界已验收；两种条件式 cost 界及实际和切割已验收；实际初始 Base 的 PointBound 和完整原 margin 已接通；一般加法图和 maximum 已验收；本批正整数除法及实际 /4 图已取得原核证书，验收见 STATUS | Probe 的 margin 与完整装配接口、Merger 扩张、margin 延拓、Placement、ConservativeHull 和最终饱和单子。已证单个 Word 单子不替代最终构造 |
| 9 | 源模型应用 | Models 27 文件已锁定，尚未完成目标端迁移 | 接同一系统的 SVC、ACwo、商单射、非选择见证；不得只证局部／定秩替代物 |
| 10 | 原 Main 全局装配与对象内部化 | 原 Main 证明链及最终对象 Con 合同已固定；专用内部检查器尚未闭合 | 接原 reverse_injection_dense→forces_PP→forces_target；复用底座证明图实例化 ZF/U，再在 ZF 内证明全部内部矛盾证明码的归约与最终 Con 蕴含 |
| 11 | 终验与发布评审 | 现有审计工具可复用；最终验收未开始 | 核对源到目标对应、命题量词、依赖及原核主句；发布另按用户授权，不把辅助构建通过当最终通过 |

阶段 0 已纠正既有资产误分类；本轮重新核对 75 份主链文件哈希全部匹配；原隔离验收另含 3 份入口文件。哈希匹配只证明来源未变，不是这些文件均已迁移。现有 L 完成范围及实际待接接口见 REUSE_CONTRACTS；主数学链见 MATH_REDUCTION_ROUTE。

每个后续改动必须注明：原源文件／定理，目标完整类型，已复用入口，精确背景差异，当前消费者，实际命令和退出码。不能仅给一个名称相似的新辅助定理算迁移完成。

执行顺序：第 4 阶段的原 Main／端点审计已完成，完整 Comparator 保留为独立未验项；第 5–6 阶段只处理进入源强迫链所需的接口，再按源依赖推进 7–10。现有完整模式、识别器、满足关系、完备性不重复建设。若还没找到某个已声称存在的接口，标“未定位到精确合同”，不能直接标“数学未证明”。

背景：纯 ℒ，nativeZF 含全 Separation/Collection，U = ZF+PP+ACwo+¬AC；终点为 `Derives nativeZF [] (Con_ZF → Con_U)`。不添加对象 AC、不可达或新推导核。

一次仅一个 Lean/Lake 构建；正式证明改动运行 scripts/verify.py，检查依赖及禁用缺口。文档改动不触发重复全量编译。保留其他仓库脏改动和已退役反射状态。不用文件数、辅助布尔门或构建任务数估计完成比例。

## 当前直接消费者

固定 ProbeWords 的 Raw.eval_oldAct / eval_injective → Word.eval_letterAct → mul_assoc / mul_one → LeftCancelMonoid 已接通。源构造器归纳由纯 lengthSchema 经已有 Separation 与 IsOmega.induction 实现；不要求外部标准长度。当前证书构造实际 Word、old 单位、W×W 输入载体与乘法表，未假定单子律。

当前已接 ProbePresentations.Path.simulation_conservative:606、simulation_old:614 和 simulation_probe:619：ConstructionProbeSimulation 构造同一个 H，证明实际 WordGraph、乘法／单位保持、四字段 Conservative 以及 old/probe 方程。直接消费者是 ConservativeCells.Probe.simulation:201、simulation_inclusion:205、simulation_generator:208。已有 Path 字母／generator／probe 图合同保留，不能声称完整 Probe Object 已装配。

已沿原 ProbeGates.cone_join → Path.extension_hasConditionalJoins 接通扩张 Word 条件并，供 ConservativeCells.Probe.extension:181 的 joins 字段使用。共享 Gate 已特化到原生恒等图，不重写 Gate 归纳。初始 probe_full_profile／probe_join_profile 已沿固定源证明接通，实际消费者为 PersistentProfiles.Path.probeProfile；复用 ExitGates、old 嵌入、generator 和已有图构造器。PersistentProfiles 的 probe HasOldGates／profile 保持现已接通：同一个实际扩张对所有旧 profile 成立。Construction/MergerPushouts.lean:333 的 Path.simulation_pushout → ConservativeCells.Probe.pushout:209 已接通，直接复用现成 existsUnique_presentedHom、presentedHom_ext 和 simulation_old/probe；保留具体呈现和映射前提。普遍性质的目标保持任意内部单子，不增加左消去限制。下一条必要依赖为 ProbeMargins.extensionHeightCost:573 / extension_old_cost_supremum:584 → MonoidBase.ProbeData.extension.margin:185 / inclusion.supremum:196。letterFloor 实际图及上下界已验收；inside/outside cost 界与实际和切割已接通，实际初始 Base 的 PointBound 适配已完成，一般切割加法和 maximum 已构造，本批正整数除法与实际 /4 图也已接通。分数／主切割差已有；下一步是一般切割差值、/4 与四倍和的连接及相应严格／相消／结合性质，再接 letter intervals 和实际 Word height/cost；初始 Base 完整 margin 已有，后继 margin 仍未完成。Merger 专用 gates／保持与完整装配仍待迁移。后续 Probe/Merger、margin、Placement 和 ConservativeHull 仍按源依赖接入。源声明到目标证书的完整索引集中在 THEOREM_COVERAGE，不在每份流程里重复逐批清单。

evalHom／liftHom 已直接复用现有内部递归和函数图，目标 N 保持原任意单子；基础 lift 不要求源 conical／b≠unit，附加 generator 取值才使用这两个源条件。

第 6 阶段已有 L 的接口、第 9 阶段模型应用、第 10 阶段全部内部码与最终 Con 仍未完成。源函数图、序列解析、ω 归纳、递归、完整模式、Proof/Sat、完备性均复用既有配套。实际验收统一见 STATUS，不以构建数估算剩余工期。

清理边界：135 个无其他证明消费者的 Packet/ObjectPacket 模块已按精确传递 import 闭包退役（RETIRED_PACKET.json）；另外 291 个仍有依赖的模块保留。该清理不推动阶段编号，也不降低最终 Con 及全部内部码验收门。
