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
| 10 | 原 Main 全局装配与对象内部化 | 原目标理论／全模式码与quotation、axiom Node/Root基例、全部内部公式归纳及实际重绑定相消已验收。原三native／五IMP行、共同R、两路径项／公式相消及完整负compiler guard解除／G0柯里化已接通。本批完整存在compiler实际8＋7记录与两层4＋4查询已消费，复用原head类型、guard证明及Curry，保留准确目标IMP字段和typed尾部局部／curried内部证明；原child同一12见证下全部四类项动作及八重对象全称封装现已原核验收，规范child同一内层条件覆盖后的完整公式独立性及9个内部存在见证／8重对象全称现也已验收，原实际child／两次opening到canonical及跨条件child整公式同码也已完成，39409项声明零警告，见已验收回执；原内层R(r,q)完整guard的跨条件开口比较本批已局部通过原核闭句及12项预审，九项完整验收／五项trust=0均通过，39421项声明零警告；旧39409足迹和2867份旧证明不变，2901项密封输入重算，见verification/forcing-exist-order-opening-acceptance.json。原实际成员guard比较和域H源端本批已通过两个原核闭句／31预审，九项完整验收／五项trust=0全部通过，39452项声明零警告；39421项旧足迹及2868份旧证明保持，2903项密封输入重算，见verification/forcing-exist-member-domain-source-acceptance.json。既有mode3／forall继续复用；reduction→goal封闭门已有，reduction／goal未证明 | 存在尾部跨条件不变性、规范源上下文布局与fresh全称化、原force_mono／force_of_dense／exists_force_neg／forceFormula_imp联合内部归纳、规范化强迫MP、全部内部ZF/U公理与六规则Proof、精确reduction及最终Con |
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

- 权威当前状态见STATUS；最新本批报告为`verification/forcing-exist-member-domain-source-acceptance.json`。
- 对象语言、背景和内部Con规格见OBJECT_TARGET；不得把外部模式索引误当统一内部真值断言。
- 固定源和供体哈希见SOURCE_LOCK；原4.34.1与目标4.33.1隔离。Lean/Lake串行。
- 每批先将本批新增文件纳入暂存差异检查（git diff --cached --check），冻结源码后完成跨平台检查及九条完整验收命令，保留五条trust=0门；再统一提交；等待上一批远端CI终态成功并读实际日志后才推送下一批。本地完整通过不冒充Linux干净环境通过。
- 不重启退役Packet／reader或反射实现，不重造L、全公理模式、通用算术、递归、Proof/Sat；不以行数、构建或审计数量代替最终证明。

当前下一原消费者：完整存在compiler及同一预序外层守卫消费已接通；原raw child／两次实际opening到canonical及跨条件child整公式同码现由ForcingExistChildOpening完成，不再列作缺口；下一步直接消费已有完整原存在compiler／实际EX输出和ForcingPreorderExistential记录，消费已完成ForcingExistMemberOpening.compare、ForcingExistOrderOpening.guard_compare与child比较；从ForcingExistDomainSource的同一H源查询连接原规范参数表和全内部公式相消，关闭实际域guard比较并组装两层EX，关闭整个raw尾部跨条件不变性；直接复用新验收的ForcingExistChildOpening.compare，不重证项图或完整公式归纳；不重新实现这些compiler。规范源上下文布局及fresh全称化复用既有InternalProofCurry、InternalProofUniversal和mode3生产器。随后关闭原联合mono／dense／MP内部归纳、全部内部公理／六规则Proof、reduction及最终Con。历史批次仅以Git和不可改写验收回执为据，不以旧批次的待办描述覆盖当前阶段表。
