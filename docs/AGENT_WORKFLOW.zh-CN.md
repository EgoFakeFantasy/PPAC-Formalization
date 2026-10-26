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
| 6 | 背景、解释、universe | Relativization、ModelTransfer、L 原语法及递归桥；本轮 InterpretedZF 消费已证全模式回放 | 新版 YesMetaZFC 的任意 ZF 模型内部 L→ZF/ZFC 已定位并验收端点（GCH 不增加为本项目义务）；补其与固定旧版、当前对象语言及原核相对化的接口。停止重证 L 全模式；不把模型定理等同于最终内部 Con |
| 7 | 源强迫前端 | 原子／公式／固定证明保真、实际作用／正规滤子、全秩 HS、七条固定公理与完整 Separation／Replacement 已验收；已接通原 forces_ZF，逐源公理／模式有原核证书 | 前端合同已闭合，保留原单子／呈现／正规滤子前提；第 8 阶段提供具体构造。全部内部公式／证明码归约仍属 10；不能把此逐实例证书说成最终内部 Con |
| 8 | 源代数／构造核心 | 原 Base.M 的内部 ω 加法表、单子／conical、非单位生成元和条件并已验；原 n+1/n+3 权重图、切割次序／上确界、正性单位界已有；实际权重图的存在及所有严格索引对的完整 Base.margin 原核证书已完成 | 初始 Base 数学数据已齐；原 Probe Path.factor/terminal 的实际内部函数图及自反、复合、零点、终端兼容律已有原核证书。原 transition/DirectedSystem、实际直极限商载体／投影和 letter_eq_iff 现已接入原核。商上实际动作图、恒等／复合／单射和 target 图及等变性现已接通。exit 图、等变性、dvd_target_of_inCone、head_separation 和实际 Alphabet 已取得原核存在证书；有限阶段锥判据、锥交、共同倍数、初始 profile 及实际字母基数界现已取得原核证书；Raw 内部载体和 old/cons 全案例已取得原核证书；原 oldAct/headDiv、实际 reduced/Word、唯一 quotient 图和 letterAct 七项定律现已取得原核证书；Raw.eval 总性／唯一性、闭包及 old/cons 方程也已回传原核；求值作用律／单射及实际 Word 左消去单子也已回传原核；下一步接 oldHom／整除／conical／generator、呈现与大小界、实际 Probe/Merger 扩张、条件并、保守嵌入与 margin 延拓，再接 Placement/ConservativeHull 和最终饱和单子；初始单子不替代最终构造 |
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

下一源链为 oldHom／old_mul_eq_old_iff／old_dvd_old_iff／old_dvd_iff_headDiv → exit_ne_one／letterAct_ne_one／IsConical → generator 及关系 → evalHom／liftHom 与呈现。已核对实际消费者：ConservativeExtensions.lean:86、ProbeGates.lean:623、ProbePresentations 的保守与生成元映射链。随后按原依赖接大小界、Probe/Merger 实际扩张、条件并、保守嵌入／margin、Placement 和 ConservativeHull。不是仅按源文件相邻位置增加工作；无用支线不恢复。

第 6 阶段已有 L 的接口、第 9 阶段模型应用、第 10 阶段全部内部码与最终 Con 仍未完成。源函数图、序列解析、ω 归纳、递归、完整模式、Proof/Sat、完备性均复用既有配套。实际验收统一见 STATUS，不以构建数估算剩余工期。
