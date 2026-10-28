# 原 1–11 阶段迁移流程（2026-10-28）

沿用最初 f28b0334a740108057adf18a24dc11abd866efbe 的阶段编号。当前仍在 **8**。完整 Base/T、实际 μ/K、内部塔与饱和、Diagram/Product descent、countable conservative hull、全部顶点/箭头/整分量共尾链已完成。本批已迁移实际 LocalQuotients.support_descent 所需 EquivariantMixing 的精确名字、成员值、相容相等、Product 固定性/HS；支撑下降和实际商/限制本身仍待接，再消费到实际纤维粘合与 CellTowers，随后进入 9–11。最终内部 Con 未完成。

| 阶段 | 原任务与输入 | 已有实际成果 | 真正还需要完成／验收门 |
|---|---|---|---|
| 1 | 语言桥接 | SourceSyntax、SourceStatements、Translation、Contract；全八构造器、首末 binder 及原核连线已验收 | 已完成，保留；不重做 |
| 2 | 句法与源推导传输 | 重命名、替换、有限支撑、19 规则及反向编译，原核 Derives 证书 | 已完成外部证书迁移；内部任意码归约归阶段 10，不回滚本项 |
| 3 | 全理论对应 | 完整 Separation/Replacement ↔ 原 Separation/Collection，全部固定公理、两种 AC；ZF/U 双向回放 | 已完成；不得把完整模式再报成未证明 |
| 4 | 原 Lean 4.34.1 外部基线 | 固定源 78 份副本哈希全部匹配；原 Main 完整构建 8998 任务通过；五个关键端点以 --trust=0 审计通过，仅标准三项依赖 | 完整 Comparator 仍未运行，缺 Linux/landrun；本仓 CheckStep4 不是此验收。原 4.34.1 环境与目标 4.33.1 保持隔离 |
| 5 | 内部名字、图、元组、递归 | 对象配对／图／ω／序列／内部递归、Def 与历史接口已验收；原 Child 归纳、IsName、evaluate、mapConditions 及作用律已验收；checkName、pairName、unionName 的精确构造、求值及条件作用均已验收 | 本基础名字包不再列为待做；实际统一条件／群作用、HS 实例及强迫公式解释也已接通。真正剩余消费者为 8–10 的最终具体单子及模型装配；不重造现成基础或重启字节兼容 |
| 6 | 背景、解释、universe | 供体完整 L/ZFC 已在固定旧版复用；原生与源语言逐公理／全模式、Choice、全局序及非空原核证书齐备。ConstructibleSource 逐点域对应、源 binder 对应、解释背景和非空前提实际消去，既有 InterpretedZF 已被真实消费 | 原 f28b033 第 6 行固定背景／universe、逐实例 Derives、不加不可达的验收门已完成；不再列作待做。全部内部／非标准 Proof/Con 归 10，不重证 L 或增加 GCH |
| 7 | 源强迫前端 | 原子／公式／固定证明保真、实际作用／正规滤子、全秩 HS、七条固定公理与完整 Separation／Replacement 已验收；已接通原 forces_ZF，逐源公理／模式有原核证书 | 前端合同已闭合，保留原单子／呈现／正规滤子前提；第 8 阶段提供具体构造。全部内部公式／证明码归约仍属 10；不能把此逐实例证书说成最终内部 Con |
| 8 | 源代数／构造核心 | 完整Base/Probe/Merger、内部塔/覆盖/精确转移、全部理想/补集/基数端点、实际μ/K；同一完整乘法图上Base→ObjectFields已装配，所有几何父前提消去；同一实际最终T行及全部ObjectFields/饱和/基数性质均有原核对象证书 | 实际 CellTowers／纤维粘合消费者；Placement、Product descent、countable conservative hull 已完成；顶点/箭头/整个 Common 分量共尾链本批接入，不重做 Base/T 或底座 |
| 9 | 源模型应用 | Models 27 文件已锁定，尚未完成目标端迁移 | 接同一系统的 SVC、ACwo、商单射、非选择见证；不得只证局部／定秩替代物 |
| 10 | 原 Main 全局装配与对象内部化 | 原 Main 证明链及最终对象 Con 合同已固定；专用内部检查器尚未闭合 | 接原 reverse_injection_dense→forces_PP→forces_target；复用底座证明图实例化 ZF/U，再在 ZF 内证明全部内部矛盾证明码的归约与最终 Con 蕴含 |
| 11 | 终验与发布评审 | 现有审计工具可复用；最终验收未开始 | 核对源到目标对应、命题量词、依赖及原核主句；发布另按用户授权，不把辅助构建通过当最终通过 |

RoundOrdinal.countable_bounded:496 和 SAME 实际塔的 Saturation.countable_stage:580 均已有原核对象证书：ConstructionSaturationBoundedness.countable_kernel_certificate / ConstructionSaturationCover.construction_kernel_certificate。后者内部构造出生索引函数、共同阶段及实际提升，并证明 fromStage∘lift=input。原μ/base/K父输入保留，同一L Choice/order消去。

## Agent 执行入口

| 当前顺序 | 原源消费者 | 必须消费的现成实现 | 实际验收门 |
|---|---|---|---|
| 8 的下一项 | LocalQuotients.active_equal/support_descent/实际商和限制 → eligibleSystem → ComponentGluing 实际 Fiber/arrowMap/粘合；CellTowers 原消费者 | 已完成 EquivariantMixing 四条原核证书、Product descent、整个分量共尾链、既有函数/商；实际 CompleteRound.Built/塔嵌入/来源、countable hull | 保留同一系统、全部纤维和全内部索引；Component quotient 和 Common.iff_zigzag 均无真实调用，不新增这两个前置；不重建塔或基础 |
| 9 | Models／具体 ProductNames | 上一步同一具体系统及已有全秩 HS／正规滤子／强迫前端 | SVC、ACwo、商单射、¬AC；保持源全部量词 |
| 10 | PP／Main 及内部矛盾码归约 | 源满射反向单射链；底座 ObjectProofNode／ReducedProofPresentation／PureProvability／Sat | ZF/U 专用全模式公理检查，全部内部／非标准证明码的正确性，原核内部 Con 蕴含 |
| 11 | 最终交付 | scripts/verify.py、源锁／足迹／端点核查 | 最终主句、完整理论／语言／背景一致，禁止缺口审计、实际构建和干净检出源码锁复现通过（当前本地通过不替代检出复现） |
| 4 的独立未验项 | 原 Comparator | 隔离原 Lean 4.34.1 基线 | Linux/landrun；不能用本仓 CheckStep4 替代 |

对象语言为纯等词／成员 ℒ；背景 nativeZF 含全部 Separation/Collection；U = ZF+PP+ACwo+¬AC。终点是原 FirstOrder.Derives nativeZF [] (Con_ZF → Con_U)，Con 量化全部内部证明码。同一内部 L 的 Choice/order 已由现成证书消去，不向普通 ZF 增加 Choice 或不可达。

已有验收已构造有界完整父背景下的内部多轮塔，保留同一实际 CompleteRound.Built；forall17 total_kernel_certificate 证明全部集合历史总唯一，forall16 construction_kernel_certificate 同时返回实际 Recursive、Valid/AllSmall、全部12表／21合同／时间恒等及精确全塔相邻 inclusion 方程。均为同一现成内部 L 相对化的原 nativeZF 核证书，Choice/order 已实际消去；不用宿主 WellFounded 或给定有效塔。

任意内部有限处方/精确CopyRel、任意理想共尾路径/Probe、补集/基数端点、实际μ/K及无几何前提的Base/T均已完成。同一实际最终行已取出；Placement/Hull 亦已完成；只接实际 CellTowers/纤维粘合消费者，不重新证明这些数学。

此前 CountableHull 批次的 113 项声明及两条同一 L 原核端点正式验收通过：2905 项构建、32089 项声明审计，9 条命令／5 次 trust=0 全退出 0、零警告；此前 31976 项足迹不变，无新增公理依赖。75 份固定源与 2460 份当前指纹匹配，底座／供体干净。见 verification/countable-conservative-hull-acceptance.json。 仍在原第 8 阶段，实际消费者及第 9–11／最终 Con 未完成。

每个证明改动先写原源声明、完整目标类型和真实消费者，查底座／同伴精确接口后复用；没定位到接口不能写成数学不存在。一次一个 Lean/Lake，LEAN_NUM_THREADS=1；正式证明改动运行 scripts/verify.py。不以模块数／构建数估算完成比例；不因文档改动重复编译。NatPacket/reader 已按获批清单退役，不恢复该支线或退役反射；保留其他项目改动。不新建通用证明核、编码器、满足关系、递归或类别后端。

此前分量共尾批次正式验收通过：2909 项构建、32174 项声明审计；新增 85 项及三条原核端点，旧 32089 项足迹不变。9 条命令／5 次 trust=0 全退出 0、零警告、无新增公理依赖。75 份固定源与 2464 份当前指纹匹配，底座／供体干净；358 个获批退役模块仍全部不存在。见 verification/component-cofinal-acceptance.json。

三个端点分别是普通 nativeZF 的 geometrySentence、全部 Vertex carrier 存在性，以及同一 L 的 forall18 整个 Common 分量共尾链。后者保留现成 ObjectFields/高度成本父背景，不声称已完成实际纤维粘合或最终 Con。

本批全量验收通过：2912 项构建、32233 项声明审计；59 项新增声明和四条普通 nativeZF 原核端点，原有 32174 项足迹不变。9 条命令（含 5 次 trust=0）全部退出 0，零警告、无新增公理依赖。75 份固定源和 2467 份当前指纹匹配，底座/供体干净。验收为当前本地工作树，历史 CRLF/LF 检出复现项仍保留；见 verification/equivariant-mixing-acceptance.json。源 family permutation/coherence 前提保留；混合名字的 HS/固定性与实际 Product 保序均非假定结论。不得据此把 LocalQuotients 或实际纤维粘合标成完成。
