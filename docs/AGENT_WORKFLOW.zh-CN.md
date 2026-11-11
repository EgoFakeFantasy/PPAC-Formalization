# 原 1–11 阶段迁移流程（2026-11-11）

当前为原第10阶段。最终目标是普通 nativeZF 原推导核中的对象句
`Con_ZF → Con_(ZF+PP+ACwo+¬AC)`；Con覆盖全部内部及非标准证明码。
本流程不新增阶段；历史批次及旧状态由Git和逐批验收报告保留。

负式与存在式的原构造码已推出 `ForcingSourceMono.atSource`。两支调用原编译总性和 `ForcingCodeUnary.unary`，并从同一 `ForcingGlobalWeakening` 输入生成弱化布局和两份覆写记录。预序行保留其空绑定表，父式在任意内部作用域生成绑定列，两者共用原来的自由底表。源条件的两份替换判断仍是输入。见[源构造分支验收](../verification/forcing-modal-source-induction-acceptance.json)。

| 阶段 | 原任务与输入 | 已有实际成果 | 真正还需要完成／验收门 |
|---|---|---|---|
| 1 | 语言桥接 | SourceSyntax、SourceStatements、Translation、Contract；全八构造器、首末 binder 及原核连线已验收 | 已完成，保留；不重做 |
| 2 | 句法与源推导传输 | 重命名、替换、有限支撑、19 规则及反向编译，原核 Derives 证书 | 已完成外部证书迁移；内部任意码归约归阶段 10，不回滚本项 |
| 3 | 全理论对应 | 完整 Separation/Replacement ↔ 原 Separation/Collection，全部固定公理、两种 AC；ZF/U 双向回放 | 已完成；不得把完整模式再报成未证明 |
| 4 | 原 Lean 4.34.1 外部基线 | 固定源 78 份副本哈希全部匹配；原 Main 完整构建 8998 任务通过；五个关键端点以 --trust=0 审计通过，仅标准三项依赖 | 已完成：42492087042／128788060157的官方Comparator实际接受，78输入不变、默认核通过，仅标准三项；真实Linux/landrun守卫也通过。原4.34.1与目标4.33.1继续隔离；见verification/original-comparator-acceptance.json |
| 5 | 内部名字、图、元组、递归 | 对象配对／图／ω／序列／内部递归、Def 与历史接口已验收；原 Child 归纳、IsName、evaluate、mapConditions 及作用律已验收；checkName、pairName、unionName 的精确构造、求值及条件作用均已验收 | 本基础名字包不再列为待做；实际统一条件／群作用、HS 实例及强迫公式解释也已接通。第 8 的具体单子已实际构造；剩余消费者为 9–10 的模型应用与全局目标装配；不重造现成基础或重启字节兼容 |
| 6 | 背景、解释、universe | 供体完整 L/ZFC 已在固定旧版复用；原生与源语言逐公理／全模式、Choice、全局序及非空原核证书齐备。ConstructibleSource 逐点域对应、源 binder 对应、解释背景和非空前提实际消去，既有 InterpretedZF 已被真实消费 | 原 f28b033 第 6 行固定背景／universe、逐实例 Derives、不加不可达的验收门已完成；不再列作待做。全部内部／非标准 Proof/Con 归 10，不重证 L 或增加 GCH |
| 7 | 源强迫前端 | 原子／公式／固定证明保真、实际作用／正规滤子、全秩 HS、七条固定公理与完整 Separation／Replacement 已验收；已接通原 forces_ZF，逐源公理／模式有原核证书 | 前端合同已闭合，保留原单子／呈现／正规滤子前提；第 8 的原核存在句现已提供实际具体构造；第 9 消费这些父输入。全部内部公式／证明码归约仍属 10；不能把此逐实例证书说成最终内部 Con |
| 8 | 源代数／构造核心 | 同一 Base/T、完整实际饱和历史／转移／最终行、理想／基数、纤维／粘合、标签／传输、完整选择器／轨道／记录族和 Assigned 图已验收；具体商双射及完整 nonwellorderable_quotient_bijection 已验收；ForcingConcreteSystem 的无参数原核存在句实际构造全部 37 原始条件／40 内部集合，并在同一见证上消费全称商结论 | 本阶段所列全局装配门已完成；第 9 阶段消费同一具体系统，不重建原基础 |
| 9 | 源模型应用 | 同一实际Core、ACwo、¬AC、ordinal_presentation、完整切片／候选族／assemble及presentation_reverse_injection均已接通；全集合reverse_injection_dense及实际forces_PP有普通nativeZF原核L相对化端点 | 本阶段模型应用链完成；PP前没有给定稠密性、满射或HS名字前提；保留全部内部量词 |
| 10 | 原 Main 全局装配与对象内部化 | 原公理模式码、固定 nativeZF 推导的六规则回放和全内部公式码单调性已验收。原子稠密性证书和任意内部码的密度编译查询已通过整仓验收。原合取、假常元归纳步已用实际编译记录和运行记录在 nativeZF 原核重放，真常元已接入同一对象归纳谓词。成员与相等的实际见证体已取得原子模板的直接查询。 | 对齐成员、相等的完整密度前提码并调用现有原子稠密性证书，接完原否定与存在量化分支，闭合全内部码的原 dense。继而完成 neg／imp、实际强迫 MP、全部内部 ZF/U 公理与六规则 Proof、reduction 及最终 Con |
| 11 | 终验与发布评审 | 现有审计工具可复用；最终验收未开始 | 核对源到目标对应、命题量词、依赖及原核主句；发布另按用户授权，不把辅助构建通过当最终通过 |

## 当前 agent 执行入口

`ForcingSourceMono.atomic_kernel_certificate` 从实际原子编译记录和同一预序行生成所需替换。两个条件覆写的项像在对象层比较，四层蕴含在原 `oldCtx 3` 下消去。见[验收报告](../verification/forcing-atomic-source-induction-acceptance.json)。

| 已有输入 | 当前消费者 | 真正的验收门 |
|---|---|---|
| 原完整raw模式码流水线及准确原生模式句quotation，已有原核双条件 | ZF/U统一内部公理正确性／强迫 | 覆盖任意内部／非标准正文和参数；原完整标准quotation、三个矩阵、模板、整个闭包及存在／类型／唯一性均已完成，不重做 |
| 现有六节点、27逻辑模式、语法操作、证明树和Proof/Sat配套 | 全内部及非标准证明码归约 | 不限外部标准码；不另建通用核、编码器或满足关系 |
| 全部源数学应用和上述内部传输 | 最终对象Con蕴含 | `FirstOrder.Derives nativeZF []`的原核闭句；最终主句仍未证明 |
| 原4.34.1 Main、五端点与官方Comparator均已通过 | 原第11最终源对应复核 | 原第4已完成，不再列作缺口；当前最终对象Con仍未证明 |

统一内部／非标准ZF/U公理正确性与全内部Proof/Con沿上述依赖推进。原Project翻译／重命名交换、三个实际编译矩阵及原正文到完整模式句的标准quotation链已经接通。后续复用ObjectProofNode、ReducedProofPresentation、PureProvability/PureSourceLocalTests和同一原强迫解释。

## 工程执行约定

- 权威当前状态见 STATUS，最新报告为 `verification/forcing-atomic-density-rebound-acceptance.json`。
- 对象语言、背景和内部Con规格见OBJECT_TARGET；不得把外部模式索引误当统一内部真值断言。
- 固定源和供体哈希见SOURCE_LOCK；原4.34.1与目标4.33.1隔离。Lean/Lake串行。
- 每批先将本批新增文件纳入暂存差异检查（git diff --cached --check），冻结源码后完成跨平台检查及九条完整验收命令，保留五条trust=0门；再统一提交；等待上一批远端CI终态成功并读实际日志后才推送下一批。本地完整通过不冒充Linux干净环境通过。
- 不重启退役Packet／reader或反射实现，不重造L、全公理模式、通用算术、递归、Proof/Sat；不以行数、构建或审计数量代替最终证明。

全内部码归纳可沿用 `ForcingCodeTotal` 的 `BoundedInduction` 装配。归一化逻辑分支消费 `ForcingLogicalCode` 的实际记录，已有负式、存在式和合取证明继续作为消费者。后续沿原 `ForcingTruth` 的依赖顺序推进。
