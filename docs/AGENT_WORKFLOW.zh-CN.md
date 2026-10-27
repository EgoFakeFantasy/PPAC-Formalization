# 原 1–11 阶段迁移流程（2026-10-28）

沿用最初 f28b0334a740108057adf18a24dc11abd866efbe 的阶段编号。当前仍在 **8**；完整单轮及实际唯一整轮后继／全旧腿更新／Valid 和 AllSmall 追加保持已通过验收，统一外层全历史算子／原生递归／完整Valid和AllSmall／全表及精确相邻转移也已验收，下一消费者为具体ω₁+1参数实例化与可数覆盖／SaturatedMonoids。9–11 和最终内部 Con 未完成。

| 阶段 | 原任务与输入 | 已有实际成果 | 真正还需要完成／验收门 |
|---|---|---|---|
| 1 | 语言桥接 | SourceSyntax、SourceStatements、Translation、Contract；全八构造器、首末 binder 及原核连线已验收 | 已完成，保留；不重做 |
| 2 | 句法与源推导传输 | 重命名、替换、有限支撑、19 规则及反向编译，原核 Derives 证书 | 已完成外部证书迁移；内部任意码归约归阶段 10，不回滚本项 |
| 3 | 全理论对应 | 完整 Separation/Replacement ↔ 原 Separation/Collection，全部固定公理、两种 AC；ZF/U 双向回放 | 已完成；不得把完整模式再报成未证明 |
| 4 | 原 Lean 4.34.1 外部基线 | 固定源 78 份副本哈希全部匹配；原 Main 完整构建 8998 任务通过；五个关键端点以 --trust=0 审计通过，仅标准三项依赖 | 完整 Comparator 仍未运行，缺 Linux/landrun；本仓 CheckStep4 不是此验收。原 4.34.1 环境与目标 4.33.1 保持隔离 |
| 5 | 内部名字、图、元组、递归 | 对象配对／图／ω／序列／内部递归、Def 与历史接口已验收；原 Child 归纳、IsName、evaluate、mapConditions 及作用律已验收；checkName、pairName、unionName 的精确构造、求值及条件作用均已验收 | 本基础名字包不再列为待做；实际统一条件／群作用、HS 实例及强迫公式解释也已接通。真正剩余消费者为 8–10 的最终具体单子及模型装配；不重造现成基础或重启字节兼容 |
| 6 | 背景、解释、universe | 供体完整 L/ZFC 已在固定旧版复用；原生与源语言逐公理／全模式、Choice、全局序及非空原核证书齐备。ConstructibleSource 逐点域对应、源 binder 对应、解释背景和非空前提实际消去，既有 InterpretedZF 已被真实消费 | 原 f28b033 第 6 行固定背景／universe、逐实例 Derives、不加不可达的验收门已完成；不再列作待做。全部内部／非标准 Proof/Con 归 10，不重证 L 或增加 GCH |
| 7 | 源强迫前端 | 原子／公式／固定证明保真、实际作用／正规滤子、全秩 HS、七条固定公理与完整 Separation／Replacement 已验收；已接通原 forces_ZF，逐源公理／模式有原核证书 | 前端合同已闭合，保留原单子／呈现／正规滤子前提；第 8 阶段提供具体构造。全部内部公式／证明码归约仍属 10；不能把此逐实例证书说成最终内部 Con |
| 8 | 源代数／构造核心 | 完整 Base、加权 Probe/Merger、保守加权极限及通用性质；实际选中后继、完整有效递归塔、所有内部阶段大小界；实际执行／根／切片 Probe 家族及精确锥；现已从原父输入构造完整 CompleteRound 的请求、调度、last target/inclusion、K 家族和所有 Merger；现已保留实际完整 trace，构造唯一整轮后继、更新所有旧腿／base 并保持完整 Valid/AllSmall；现已实际构造有界背景下的完整内部多轮塔、全部阶段界／字段／21合同／全塔精确相邻图 | 当前只剩原 CompleteRounds.Saturation 具体ω₁+1及基数参数实例化／可数覆盖／多轮实际系统／最终饱和性及其实际 Placement/Hull 消费者；不重做单轮、L、模式、序数或递归基础 |
| 9 | 源模型应用 | Models 27 文件已锁定，尚未完成目标端迁移 | 接同一系统的 SVC、ACwo、商单射、非选择见证；不得只证局部／定秩替代物 |
| 10 | 原 Main 全局装配与对象内部化 | 原 Main 证明链及最终对象 Con 合同已固定；专用内部检查器尚未闭合 | 接原 reverse_injection_dense→forces_PP→forces_target；复用底座证明图实例化 ZF/U，再在 ZF 内证明全部内部矛盾证明码的归约与最终 Con 蕴含 |
| 11 | 终验与发布评审 | 现有审计工具可复用；最终验收未开始 | 核对源到目标对应、命题量词、依赖及原核主句；发布另按用户授权，不把辅助构建通过当最终通过 |

## Agent 执行入口

| 当前顺序 | 原源消费者 | 必须消费的现成实现 | 实际验收门 |
|---|---|---|---|
| 8 的下一项 | 具体ω₁+1／基数参数实例化、countable_stage → SaturatedMonoids | 已完成 ConstructionSaturationIterationValidity.exists_tower/map_succ_selected；ExistingSmallUnion.union_bound_l 已适配；供体 OrdinalImage/hartogs_regular_l／原生共尾有界 | 同一内部多轮塔、阶段同态／profile／大小界、所有内部可数数据的适当阶段覆盖、全部 Probe/Merger 饱和性及原核证书 |
| 9 | Models／具体 ProductNames | 上一步同一具体系统及已有全秩 HS／正规滤子／强迫前端 | SVC、ACwo、商单射、¬AC；保持源全部量词 |
| 10 | PP／Main 及内部矛盾码归约 | 源满射反向单射链；底座 ObjectProofNode／ReducedProofPresentation／PureProvability／Sat | ZF/U 专用全模式公理检查，全部内部／非标准证明码的正确性，原核内部 Con 蕴含 |
| 11 | 最终交付 | scripts/verify.py、源锁／足迹／端点核查 | 最终主句、完整理论／语言／背景一致，禁止缺口审计与实际构建通过 |
| 4 的独立未验项 | 原 Comparator | 隔离原 Lean 4.34.1 基线 | Linux/landrun；不能用本仓 CheckStep4 替代 |

对象语言为纯等词／成员 ℒ；背景 nativeZF 含全部 Separation/Collection；U = ZF+PP+ACwo+¬AC。终点是原 FirstOrder.Derives nativeZF [] (Con_ZF → Con_U)，Con 量化全部内部证明码。同一内部 L 的 Choice/order 已由现成证书消去，不向普通 ZF 增加 Choice 或不可达。

本批实际构造有界完整父背景下的内部多轮塔，保留同一实际 CompleteRound.Built；forall17 total_kernel_certificate 证明全部集合历史总唯一，forall16 construction_kernel_certificate 同时返回实际 Recursive、Valid/AllSmall、全部12表／21合同／时间恒等及精确全塔相邻 inclusion 方程。均为同一现成内部 L 相对化的原 nativeZF 核证书，Choice/order 已实际消去；不用宿主 WellFounded 或给定有效塔。

下一输入实例化为原具体ω₁+1／基数参数；然后证明可数适当阶段覆盖与最终饱和性。union_bound_l 所需配套已有，不能重复复制整 CountableUnion；OrdinalImage 与 hartogs_regular_l 只适配必要源闭包。

验收 verification/saturation-iteration-acceptance.json：49新声明、25受影响旧声明；2865构建／31301声明；旧31252足迹不变；9命令／5次trust=0全通过、零警告、无新增公理依赖；2429当前指纹／75源哈希匹配。

每个证明改动先写原源声明、完整目标类型和真实消费者，查底座／同伴精确接口后复用；没定位到接口不能写成数学不存在。一次一个 Lean/Lake，LEAN_NUM_THREADS=1；正式证明改动运行 scripts/verify.py。不以模块数／构建数估算完成比例；不因文档改动重复编译。NatPacket/reader 已按获批清单退役，不恢复该支线或退役反射；保留其他项目改动。不新建通用证明核、编码器、满足关系、递归或类别后端。
