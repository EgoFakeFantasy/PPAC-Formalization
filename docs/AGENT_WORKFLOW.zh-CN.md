# 原 1–11 阶段迁移流程（2026-10-26 重审）

阶段编号恢复为最初提交 `f28b0334a740108057adf18a24dc11abd866efbe` 的表。阶段 0 是来源审查前置；下表不再用四项验收或历史 S3/STEP4 批次重新编号。迁移对象始终为固定 OpenAI PPAC 证明，底座为固定 YesMetaZFC 原推导核。

**实际位置：1–3 已验收；4 原 Main／端点审计已通过、Comparator 未验收；5–6 部分完成。7–10 主数学链没有完成迁移，不能称为收尾。**

| 阶段 | 原任务与输入 | 已有实际成果 | 真正还需要完成／验收门 |
|---|---|---|---|
| 1 | 语言桥接 | SourceSyntax、SourceStatements、Translation、Contract；全八构造器、首末 binder 及原核连线已验收 | 已完成，保留；不重做 |
| 2 | 句法与源推导传输 | 重命名、替换、有限支撑、19 规则及反向编译，原核 Derives 证书 | 已完成外部证书迁移；内部任意码归约归阶段 10，不回滚本项 |
| 3 | 全理论对应 | 完整 Separation/Replacement ↔ 原 Separation/Collection，全部固定公理、两种 AC；ZF/U 双向回放 | 已完成；不得把完整模式再报成未证明 |
| 4 | 原 Lean 4.34.1 外部基线 | 固定源 78 份副本哈希全部匹配；原 Main 完整构建 8998 任务通过；五个关键端点以 --trust=0 审计通过，仅标准三项依赖 | 完整 Comparator 仍未运行，缺 Linux/landrun；本仓 CheckStep4 不是此验收。原 4.34.1 环境与目标 4.33.1 保持隔离 |
| 5 | 内部名字、图、元组、递归 | 对象配对／图／ω／序列／内部递归、Def 与历史接口已验收；原 Child 归纳、IsName、evaluate、mapConditions 及作用律已验收；checkName、pairName、unionName 的精确构造、求值及条件作用均已验收 | 本基础名字包不再列为待做；继续向阶段 7 接实际条件／群／赋值呈现、具体系统中的 HS 作用实例与强迫公式解释。完整阶段的消费者对接尚未验收；不重造现成基础或重启字节兼容 |
| 6 | 背景、解释、universe | Relativization、ModelTransfer、L 原语法及递归桥；本轮 InterpretedZF 消费已证全模式回放 | 新版 YesMetaZFC 的任意 ZF 模型内部 L→ZF/ZFC/GCH 已定位并验收端点；补其与固定旧版、当前对象语言及原核相对化的接口。停止重证 L 全模式；不把模型定理等同于最终内部 Con |
| 7 | 源强迫前端 | 已固定 Forcing 16 文件，源 atomic/regular/forces_ZF 等证明可复用；左／右／交换归纳已验收；内部条件码上的原子递归及精确方程已验收；基础原子定律和作用对称性已验收；完整公式强迫及 19 规则固定证明保真已验收；公式作用对称性通用迁移已验收；HS 字面定义、展开、唯一性及空/check 闭包已验收；通用 HS.smul 和实际 HS 域公式对称性已验收；标签置换载体、逐点稳定子闭包及逐点共轭已验收；共轭集合图、精确稳定子像与子群像闭包已验收；小支撑族、有限并基数界、交闭包及四项正规性已构造；目标端主链未完成 | 整张 Diagram 的标签作用构造及恒等／复合／逆律已定向通过；接其序关系、Cohen 分量和 WithTop 后形成实际 poset/群作用，消费已构造正规滤子、pair/union 闭包、将已证 HS 作用与公式对称性实例化到具体系统、全部解释公理；固定证明实例的 forcing_sound 已完成，内部任意码归约仍归阶段 10；保留全秩和完整模式 |
| 8 | 源代数／构造核心 | Algebra 13、Construction 13 文件已锁定，尚未完成目标端迁移 | 沿原 Monoid/Placement/ConservativeHull 实际构造及不变量迁移；不得以字段假设核心结论 |
| 9 | 源模型应用 | Models 27 文件已锁定，尚未完成目标端迁移 | 接同一系统的 SVC、ACwo、商单射、非选择见证；不得只证局部／定秩替代物 |
| 10 | 原 Main 全局装配与对象内部化 | 原 Main 证明链及最终对象 Con 合同已固定；专用内部检查器尚未闭合 | 接原 reverse_injection_dense→forces_PP→forces_target；复用底座证明图实例化 ZF/U，再在 ZF 内证明全部内部矛盾证明码的归约与最终 Con 蕴含 |
| 11 | 终验与发布评审 | 现有审计工具可复用；最终验收未开始 | 核对源到目标对应、命题量词、依赖及原核主句；发布另按用户授权，不把辅助构建通过当最终通过 |

阶段 0 已纠正既有资产误分类；本轮重新核对 75 份主链文件哈希全部匹配；原隔离验收另含 3 份入口文件。哈希匹配只证明来源未变，不是这些文件均已迁移。现有 L 完成范围及实际待接接口见 REUSE_CONTRACTS；主数学链见 MATH_REDUCTION_ROUTE。

每个后续改动必须注明：原源文件／定理，目标完整类型，已复用入口，精确背景差异，当前消费者，实际命令和退出码。不能仅给一个名称相似的新辅助定理算迁移完成。

执行顺序：第 4 阶段的原 Main／端点审计已完成，完整 Comparator 保留为独立未验项；第 5–6 阶段只处理进入源强迫链所需的接口，再按源依赖推进 7–10。现有完整模式、识别器、满足关系、完备性不重复建设。若还没找到某个已声称存在的接口，标“未定位到精确合同”，不能直接标“数学未证明”。

背景：纯 ℒ，nativeZF 含全 Separation/Collection，U = ZF+PP+ACwo+¬AC；终点为 `Derives nativeZF [] (Con_ZF → Con_U)`。不添加对象 AC、不可达或新推导核。

一次仅一个 Lean/Lake 构建；正式证明改动运行 scripts/verify.py，检查依赖及禁用缺口。文档改动不触发重复全量编译。保留其他仓库脏改动和已退役反射状态。不用文件数、辅助布尔门或构建任务数估计完成比例。



## 本批执行边界

沿原 `Diagrams.Diagram.permute → ProductForcing.permuteOrderIso → ProductNames.actionHom`，新增 ForcingDiagramAction：直接复用底座 `ZF.exists_compositionFunction`、关系外延和既有图公式，构造任意内部 D→I 单射的标签作用，返回四个原核证书（存在、恒等、复合、逆作用）。没有建立新的函数图或群论库。

本批定向构建、trust=0 预审计及完整 9 命令验收通过；精确结果见 STATUS 和 verification/commands.json。Diagram 的序关系、Cohen 分量和 WithTop 作用尚未接通，不能标成 actionHom 已完成；当前仍为阶段 7。

新版库内部强迫的复用审查：`preserves_zf_l` 要求 Generic_d，结论是全部名字的泛滤商扩张；`Npair_d` 以全部条件为权重。它们不是源 HS 对称模型或源固定顶条件 pairName 的直接替代。已记录精确接口，复用其适配的基础构造，不引入本路线已排除的泛滤支线。
