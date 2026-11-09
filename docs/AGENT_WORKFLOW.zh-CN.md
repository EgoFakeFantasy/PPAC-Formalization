# 原 1–11 阶段迁移流程（2026-11-08）

当前为原第10阶段。最终目标是普通 nativeZF 原推导核中的对象句
`Con_ZF → Con_(ZF+PP+ACwo+¬AC)`；Con覆盖全部内部及非标准证明码。
本流程不新增阶段；历史批次及旧状态由Git和逐批验收报告保留。

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
| 10 | 原 Main 全局装配与对象内部化 | 原目标理论、全模式码流水线、标准quotation、axiom Node/Root基例、完整公式归纳、负实例正规化、原局部证明解除及mode3／forall均保留；原preorder实际开口、三native／五IMP／内部证明行、共同R源与两路径全内部相消已验收。ForcingPreorderLeaves／LeafTarget已从同一原rawData／targetData／instancesProved保留6＋10＋5个见证及内部证明，内部生成原三张prefix表与十一条实际查询；24个见证均在对象量词内。relation_from_data自行恢复空表类型、条件自然性与关系叶查询。ForcingPreorderMember内部生成树码子字段及原载体槽字段，证明实际raw member叶与原guard编译／开口／实例化结果同码。两个新增普通nativeZF原核闭句证书及44项新增公共声明的trust=0预审通过；本批九项完整验收／五项trust=0均退出0，39328项声明、零警告。全部39284项旧足迹不变，无新增公理；清理后四个受影响源码的trust=0也全部退出0。没有给定叶查询、载体值、期望码等式或guard真值，运行码与目标作用域允许内部非标准值。 ForcingPreorderGuardTables已接通原free-condition实际替换后的两类guard：用对象numeral不等证明载体槽保留，并在对象量词内生成载体值；实际relation compiler／native InstantiateTop到原R(P0,P2)叶的同码证明内部消去4个compiler、5个共同源、4个实参表和1个singleton森林见证。没有给定共同源／像表／森林／码等式答案，原空表类型和条件项类型从同一原记录恢复。两个普通nativeZF原核证书及10项trust=0预审通过；该后续批次九项完整验收／五项trust=0全部退出0，39338项声明、零警告；39328项旧足迹与2861份旧证明源码不变，无新增公理。整段负／存在compiler与后续Proof／Con仍未完成。 ForcingPreorderNegative直接消费原完整否定compiler、实际body开口和native InstantiateTop；5＋4＋6＋6个原见证在对象量词内消去。实际两层guard查询经既有GuardTables识别为同一H0／H5，原逻辑字段替换后调用既有内部证明规则解除两个前件。既有Curry生产器实际消费同一局部证明，将整个G0前件移入蕴含并保留Extra；同一原falsum和实际剩余IMP码留在对象EX内。parent是Ctx下的内部条件证明，未假定Ctx／guard／preorder真值，其类型由实际native实例恢复。普通nativeZF原核闭句证书及9项trust=0预审通过；本批九项完整验收／五项trust=0均退出0，39347项声明、零警告；39338项旧足迹及2862份旧证明源码不变，无新增公理。规范源上下文布局／fresh全称化、完整存在分支及后续内部Proof／Con尚未完成。 reduction→goal封闭门已有，reduction及goal未证明 | 完整存在分支的实际记录消费、规范源上下文布局与fresh全称化、原force_mono／force_of_dense／exists_force_neg／forceFormula_imp联合内部归纳、规范化强迫MP、全部内部ZF/U公理与六规则Proof、精确reduction及最终Con |
| 11 | 终验与发布评审 | 现有审计工具可复用；最终验收未开始 | 核对源到目标对应、命题量词、依赖及原核主句；发布另按用户授权，不把辅助构建通过当最终通过 |

## 当前 agent 执行入口

| 已有输入 | 当前消费者 | 真正的验收门 |
|---|---|---|
| 原完整raw模式码流水线及准确原生模式句quotation，已有原核双条件 | ZF/U统一内部公理正确性／强迫 | 覆盖任意内部／非标准正文和参数；原完整标准quotation、三个矩阵、模板、整个闭包及存在／类型／唯一性均已完成，不重做 |
| 现有六节点、27逻辑模式、语法操作、证明树和Proof/Sat配套 | 全内部及非标准证明码归约 | 不限外部标准码；不另建通用核、编码器或满足关系 |
| 全部源数学应用和上述内部传输 | 最终对象Con蕴含 | `FirstOrder.Derives nativeZF []`的原核闭句；最终主句仍未证明 |
| 原4.34.1 Main、五端点与官方Comparator均已通过 | 原第11最终源对应复核 | 原第4已完成，不再列作缺口；当前最终对象Con仍未证明 |

当前只推进统一内部／非标准ZF/U公理正确性与全内部Proof/Con。原Project翻译／重命名交换、三个实际编译矩阵及原正文到完整模式句的标准quotation链本批均已接通。复用现成ObjectProofNode、ReducedProofPresentation、PureProvability/PureSourceLocalTests和同一原强迫解释；不重建L、数学公理模式、满足关系或证明核。

## 工程执行约定

- 权威当前状态见STATUS；最新本批报告为`verification/forcing-preorder-negative-acceptance.json`。
- 对象语言、背景和内部Con规格见OBJECT_TARGET；不得把外部模式索引误当统一内部真值断言。
- 固定源和供体哈希见SOURCE_LOCK；原4.34.1与目标4.33.1隔离。Lean/Lake串行。
- 每批先完成源码／跨平台检查及九条完整验收命令，保留五条trust=0门；再统一提交；等待上一批远端CI终态成功并读实际日志后才推送下一批。本地完整通过不冒充Linux干净环境通过。
- 不重启退役Packet／reader或反射实现，不重造L、全公理模式、通用算术、递归、Proof/Sat；不以行数、构建或审计数量代替最终证明。

当前下一原消费者：完整存在分支已有ForcingExistCode／ExistGuardsCode／ExistChildCode生产器，继续公开其必要实际记录接口并接入原同一预序守卫证明；不重新实现这些compiler。规范源上下文布局及fresh全称化复用既有InternalProofCurry、InternalProofUniversal和mode3生产器。随后关闭原联合mono／dense／MP内部归纳、全部内部公理／六规则Proof、reduction及最终Con。历史批次仅以Git和不可改写验收回执为据，不以旧批次的待办描述覆盖当前阶段表。
