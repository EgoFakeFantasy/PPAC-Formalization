# 原 1–11 阶段迁移流程（2026-10-26 重审）

阶段编号恢复为最初提交 `f28b0334a740108057adf18a24dc11abd866efbe` 的表。阶段 0 是来源审查前置；下表不再用四项验收或历史 S3/STEP4 批次重新编号。迁移对象始终为固定 OpenAI PPAC 证明，底座为固定 YesMetaZFC 原推导核。

**实际位置：连续完整验收到原 1–3 阶段。4 部分验收；5 基础包已验收；6 接口未闭合；7 仅条件式前端合同已验收，整阶段不能打勾；当前主开发在 8 的初始 Base 数值解释，9–11 未完成。不是“前七阶段全过”，也不是收尾。**

| 阶段 | 原任务与输入 | 已有实际成果 | 真正还需要完成／验收门 |
|---|---|---|---|
| 1 | 语言桥接 | SourceSyntax、SourceStatements、Translation、Contract；全八构造器、首末 binder 及原核连线已验收 | 已完成，保留；不重做 |
| 2 | 句法与源推导传输 | 重命名、替换、有限支撑、19 规则及反向编译，原核 Derives 证书 | 已完成外部证书迁移；内部任意码归约归阶段 10，不回滚本项 |
| 3 | 全理论对应 | 完整 Separation/Replacement ↔ 原 Separation/Collection，全部固定公理、两种 AC；ZF/U 双向回放 | 已完成；不得把完整模式再报成未证明 |
| 4 | 原 Lean 4.34.1 外部基线 | 固定源 78 份副本哈希全部匹配；原 Main 完整构建 8998 任务通过；五个关键端点以 --trust=0 审计通过，仅标准三项依赖 | 完整 Comparator 仍未运行，缺 Linux/landrun；本仓 CheckStep4 不是此验收。原 4.34.1 环境与目标 4.33.1 保持隔离 |
| 5 | 内部名字、图、元组、递归 | 对象配对／图／ω／序列／内部递归、Def 与历史接口已验收；原 Child 归纳、IsName、evaluate、mapConditions 及作用律已验收；checkName、pairName、unionName 的精确构造、求值及条件作用均已验收 | 本基础名字包不再列为待做；实际统一条件／群作用、HS 实例及强迫公式解释也已接通。真正剩余消费者为 8–10 的最终具体单子及模型装配；不重造现成基础或重启字节兼容 |
| 6 | 背景、解释、universe | Relativization、ModelTransfer、L 原语法及递归桥；本轮 InterpretedZF 消费已证全模式回放 | 新版 YesMetaZFC 的任意 ZF 模型内部 L→ZF/ZFC 已定位并验收端点（GCH 不增加为本项目义务）；补其与固定旧版、当前对象语言及原核相对化的接口。停止重证 L 全模式；不把模型定理等同于最终内部 Con |
| 7 | 源强迫前端 | 原子／公式／固定证明保真、实际作用／正规滤子、全秩 HS、七条固定公理与完整 Separation／Replacement 已验收；本批接通原 forces_ZF，逐源公理／模式有原核证书 | 前端合同已闭合，保留原单子／呈现／正规滤子前提；第 8 阶段提供具体构造。全部内部公式／证明码归约仍属 10；不能把此逐实例证书说成最终内部 Con |
| 8 | 源代数／构造核心 | Algebra 13、Construction 13 文件已锁定；原 Base.M 的内部 ω 加法表、左消去／conical、非单位生成元、le_iff 与条件并已验收；height/cost 的精确自然数分数图与正性界已验收；分数载体、交叉乘积全预序及单位分数反序已验收；分数稠密性已验收；内部切割载体、有界族上确界、精确 height/cost 切割值及正性／单位上界已有；分数加法、主切割加法及实际权重值已有原核证书；有序主切割的非负差及严格正差已有；本批完成原遗漏成本的精确非空像集、上确界及 supremum≤cost(x) 原核证书 | 原 Base.margin 剩 cost(x)<height(y)-height(x) 的严格估计，再与现有上确界界组合；不把完整实数域库扩建列为 Base 的前置。扩张所需任意切割运算按源消费者逐项适配，再接 Placement/ConservativeHull 与不变量。初始自然数单子不能替代最终饱和单子 |
| 9 | 源模型应用 | Models 27 文件已锁定，尚未完成目标端迁移 | 接同一系统的 SVC、ACwo、商单射、非选择见证；不得只证局部／定秩替代物 |
| 10 | 原 Main 全局装配与对象内部化 | 原 Main 证明链及最终对象 Con 合同已固定；专用内部检查器尚未闭合 | 接原 reverse_injection_dense→forces_PP→forces_target；复用底座证明图实例化 ZF/U，再在 ZF 内证明全部内部矛盾证明码的归约与最终 Con 蕴含 |
| 11 | 终验与发布评审 | 现有审计工具可复用；最终验收未开始 | 核对源到目标对应、命题量词、依赖及原核主句；发布另按用户授权，不把辅助构建通过当最终通过 |

阶段 0 已纠正既有资产误分类；本轮重新核对 75 份主链文件哈希全部匹配；原隔离验收另含 3 份入口文件。哈希匹配只证明来源未变，不是这些文件均已迁移。现有 L 完成范围及实际待接接口见 REUSE_CONTRACTS；主数学链见 MATH_REDUCTION_ROUTE。

每个后续改动必须注明：原源文件／定理，目标完整类型，已复用入口，精确背景差异，当前消费者，实际命令和退出码。不能仅给一个名称相似的新辅助定理算迁移完成。

执行顺序：第 4 阶段的原 Main／端点审计已完成，完整 Comparator 保留为独立未验项；第 5–6 阶段只处理进入源强迫链所需的接口，再按源依赖推进 7–10。现有完整模式、识别器、满足关系、完备性不重复建设。若还没找到某个已声称存在的接口，标“未定位到精确合同”，不能直接标“数学未证明”。

背景：纯 ℒ，nativeZF 含全 Separation/Collection，U = ZF+PP+ACwo+¬AC；终点为 `Derives nativeZF [] (Con_ZF → Con_U)`。不添加对象 AC、不可达或新推导核。

一次仅一个 Lean/Lake 构建；正式证明改动运行 scripts/verify.py，检查依赖及禁用缺口。文档改动不触发重复全量编译。保留其他仓库脏改动和已退役反射状态。不用文件数、辅助布尔门或构建任务数估计完成比例。

## 当前直接消费者

固定 `SymmetricChoice.lean` 的 `WitnessIndex/chosenWitness → replacementBound → bounded_local_witness → image_in_bound → replacementImage → forces_replacement → forces_ZF` 已迁移。唯一需要对象化适配的宿主选择步骤，改由底座 Collection 给出覆盖所有有效索引的 HS 见证集；精确证明了源 bounded_local_witness 消费者合同，未构造或假定对象选择函数。随后保留源全群轨道、单值性、相等替换、稠密性及 Separation 像集证明。

正在原阶段 8 的 Algebra/Construction。本批直接复用固定底座序数加法和函数图，构造原 Base.M 的完整内部 ω 加法表，证明左消去／conical、非单位生成元、le_iff 与两元素上确界，并给出原核证书。原 height/cost 的自然数分数图及严格正性界已验收；内部载体、交叉乘积全预序与单位分数次序已接通，本批已接分数等值的主切割、切割次序完备性及实际 height/cost 切割值图和 0<值<1；主切割加法及有序主切割的非负差现已接入。Base.margin 第二源子目标已完成：遗漏因子的 cost(d)≤cost(x)，其精确像集在 x<y 时非空，并已构造上确界≤cost(x)。下一步为原第一子目标 cost(x)<height(y)-height(x)，然后接 UniformMargin.supremum_lt 的严格传递。任意切割运算仅按后续原扩张的实际需求适配；不预先扩建完整实数域库。之后迁移扩张、塔与 conservative hull；初始自然数单子不能替代原最终构造。先核查现成精确合同，缺少已接适配不等于缺少已有数学。

阶段 6 的已有 L 接口适配、9 的模型应用、10 的全部内部码与最终 Con 均未因 forces_ZF 完成。完整验收数据统一见 STATUS，不以构建数量估计剩余工期。
