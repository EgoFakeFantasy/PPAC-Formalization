# 原 1–11 阶段迁移流程（2026-10-28）

沿用最初f28b0334a740108057adf18a24dc11abd866efbe的阶段编号。当前仍在 **8**；完整实际塔、覆盖、Probe/Merger/同根图精确CopyRel、任意理想单位首项内部ω共尾路径/ideal probes、complement probes及内部基数端点均已验收。下一项为ConcreteSystem实际μ/K及Placement/Hull，再进入9–11；最终内部Con未完成。

| 阶段 | 原任务与输入 | 已有实际成果 | 真正还需要完成／验收门 |
|---|---|---|---|
| 1 | 语言桥接 | SourceSyntax、SourceStatements、Translation、Contract；全八构造器、首末 binder 及原核连线已验收 | 已完成，保留；不重做 |
| 2 | 句法与源推导传输 | 重命名、替换、有限支撑、19 规则及反向编译，原核 Derives 证书 | 已完成外部证书迁移；内部任意码归约归阶段 10，不回滚本项 |
| 3 | 全理论对应 | 完整 Separation/Replacement ↔ 原 Separation/Collection，全部固定公理、两种 AC；ZF/U 双向回放 | 已完成；不得把完整模式再报成未证明 |
| 4 | 原 Lean 4.34.1 外部基线 | 固定源 78 份副本哈希全部匹配；原 Main 完整构建 8998 任务通过；五个关键端点以 --trust=0 审计通过，仅标准三项依赖 | 完整 Comparator 仍未运行，缺 Linux/landrun；本仓 CheckStep4 不是此验收。原 4.34.1 环境与目标 4.33.1 保持隔离 |
| 5 | 内部名字、图、元组、递归 | 对象配对／图／ω／序列／内部递归、Def 与历史接口已验收；原 Child 归纳、IsName、evaluate、mapConditions 及作用律已验收；checkName、pairName、unionName 的精确构造、求值及条件作用均已验收 | 本基础名字包不再列为待做；实际统一条件／群作用、HS 实例及强迫公式解释也已接通。真正剩余消费者为 8–10 的最终具体单子及模型装配；不重造现成基础或重启字节兼容 |
| 6 | 背景、解释、universe | 供体完整 L/ZFC 已在固定旧版复用；原生与源语言逐公理／全模式、Choice、全局序及非空原核证书齐备。ConstructibleSource 逐点域对应、源 binder 对应、解释背景和非空前提实际消去，既有 InterpretedZF 已被真实消费 | 原 f28b033 第 6 行固定背景／universe、逐实例 Derives、不加不可达的验收门已完成；不再列作待做。全部内部／非标准 Proof/Con 归 10，不重证 L 或增加 GCH |
| 7 | 源强迫前端 | 原子／公式／固定证明保真、实际作用／正规滤子、全秩 HS、七条固定公理与完整 Separation／Replacement 已验收；已接通原 forces_ZF，逐源公理／模式有原核证书 | 前端合同已闭合，保留原单子／呈现／正规滤子前提；第 8 阶段提供具体构造。全部内部公式／证明码归约仍属 10；不能把此逐实例证书说成最终内部 Con |
| 8 | 源代数／构造核心 | 完整Base/Probe/Merger、保守加权极限、实际内部塔及全不变量/大小/转移、内部ω₁+1与可数族覆盖；最终Probe/有限Merger/同根图精确CopyRel；任意内部理想的单位首项ω共尾路径和ideal probes；补集Probe与原\|K\|=μ的完整内部基数端点，均有原核对象证书 | ConcreteSystem实际μ/K及Placement/Hull；不重做已完成的理想/补集/基数/塔/底座 |
| 9 | 源模型应用 | Models 27 文件已锁定，尚未完成目标端迁移 | 接同一系统的 SVC、ACwo、商单射、非选择见证；不得只证局部／定秩替代物 |
| 10 | 原 Main 全局装配与对象内部化 | 原 Main 证明链及最终对象 Con 合同已固定；专用内部检查器尚未闭合 | 接原 reverse_injection_dense→forces_PP→forces_target；复用底座证明图实例化 ZF/U，再在 ZF 内证明全部内部矛盾证明码的归约与最终 Con 蕴含 |
| 11 | 终验与发布评审 | 现有审计工具可复用；最终验收未开始 | 核对源到目标对应、命题量词、依赖及原核主句；发布另按用户授权，不把辅助构建通过当最终通过 |

RoundOrdinal.countable_bounded:496 和 SAME 实际塔的 Saturation.countable_stage:580 均已有原核对象证书：ConstructionSaturationBoundedness.countable_kernel_certificate / ConstructionSaturationCover.construction_kernel_certificate。后者内部构造出生索引函数、共同阶段及实际提升，并证明 fromStage∘lift=input。原μ/base/K父输入保留，同一L Choice/order消去。

## Agent 执行入口

| 当前顺序 | 原源消费者 | 必须消费的现成实现 | 实际验收门 |
|---|---|---|---|
| 8 的下一项 | Models/ConcreteSystem.μ、μ_countable_power/regular、K/T及实际Placement/Hull | 现成原生基数算术/后继正则性、Base、本批IdealTower及既有全秩强迫前端 | 实际连续统后继参数和源全部大小/饱和/支撑合同，实例化到同一具体系统；不新增GCH/不可达 |
| 9 | Models／具体 ProductNames | 上一步同一具体系统及已有全秩 HS／正规滤子／强迫前端 | SVC、ACwo、商单射、¬AC；保持源全部量词 |
| 10 | PP／Main 及内部矛盾码归约 | 源满射反向单射链；底座 ObjectProofNode／ReducedProofPresentation／PureProvability／Sat | ZF/U 专用全模式公理检查，全部内部／非标准证明码的正确性，原核内部 Con 蕴含 |
| 11 | 最终交付 | scripts/verify.py、源锁／足迹／端点核查 | 最终主句、完整理论／语言／背景一致，禁止缺口审计与实际构建通过 |
| 4 的独立未验项 | 原 Comparator | 隔离原 Lean 4.34.1 基线 | Linux/landrun；不能用本仓 CheckStep4 替代 |

对象语言为纯等词／成员 ℒ；背景 nativeZF 含全部 Separation/Collection；U = ZF+PP+ACwo+¬AC。终点是原 FirstOrder.Derives nativeZF [] (Con_ZF → Con_U)，Con 量化全部内部证明码。同一内部 L 的 Choice/order 已由现成证书消去，不向普通 ZF 增加 Choice 或不可达。

本批实际构造有界完整父背景下的内部多轮塔，保留同一实际 CompleteRound.Built；forall17 total_kernel_certificate 证明全部集合历史总唯一，forall16 construction_kernel_certificate 同时返回实际 Recursive、Valid/AllSmall、全部12表／21合同／时间恒等及精确全塔相邻 inclusion 方程。均为同一现成内部 L 相对化的原 nativeZF 核证书，Choice/order 已实际消去；不用宿主 WellFounded 或给定有效塔。

任意内部有限optional start table、最终RootSystem/精确CopyRel、任意理想的单位首项内部ω共尾路径/ideal probes、补集Probe及完整内部target/complement基数端点均已由同一实际塔完成。后续只接ConcreteSystem μ/K及实际Placement/Hull，不再迁移这些已完成部分。

最新验收verification/ideal-probes-acceptance.json：55项新声明，2885构建／31554审计；此前31499项足迹不变，9命令／5次trust=0全通过，零警告，无新增公理依赖。供体8项必要声明正文精确复用；全部内部ω/任意理想/全部最终除子保留。

每个证明改动先写原源声明、完整目标类型和真实消费者，查底座／同伴精确接口后复用；没定位到接口不能写成数学不存在。一次一个 Lean/Lake，LEAN_NUM_THREADS=1；正式证明改动运行 scripts/verify.py。不以模块数／构建数估算完成比例；不因文档改动重复编译。NatPacket/reader 已按获批清单退役，不恢复该支线或退役反射；保留其他项目改动。不新建通用证明核、编码器、满足关系、递归或类别后端。
