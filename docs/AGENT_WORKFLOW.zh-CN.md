# 原 1–11 阶段迁移流程（2026-11-08）

当前为原第10阶段。最终目标是普通 nativeZF 原推导核中的对象句
`Con_ZF → Con_(ZF+PP+ACwo+¬AC)`；Con覆盖全部内部及非标准证明码。
本流程不新增阶段；历史批次及旧状态由Git和逐批验收报告保留。

| 阶段 | 原任务与输入 | 已有实际成果 | 真正还需要完成／验收门 |
|---|---|---|---|
| 1 | 语言桥接 | SourceSyntax、SourceStatements、Translation、Contract；全八构造器、首末 binder 及原核连线已验收 | 已完成，保留；不重做 |
| 2 | 句法与源推导传输 | 重命名、替换、有限支撑、19 规则及反向编译，原核 Derives 证书 | 已完成外部证书迁移；内部任意码归约归阶段 10，不回滚本项 |
| 3 | 全理论对应 | 完整 Separation/Replacement ↔ 原 Separation/Collection，全部固定公理、两种 AC；ZF/U 双向回放 | 已完成；不得把完整模式再报成未证明 |
| 4 | 原 Lean 4.34.1 外部基线 | 固定源 78 份副本哈希全部匹配；原 Main 完整构建 8998 任务通过；五个关键端点以 --trust=0 审计通过，仅标准三项依赖 | 完整Comparator尚未取得接受结果；固定官方工具已通过原4.34.1兼容编译，真实Linux/landrun隔离CI已准备；本仓 CheckStep4 不是此验收。原 4.34.1 环境与目标 4.33.1 保持隔离 |
| 5 | 内部名字、图、元组、递归 | 对象配对／图／ω／序列／内部递归、Def 与历史接口已验收；原 Child 归纳、IsName、evaluate、mapConditions 及作用律已验收；checkName、pairName、unionName 的精确构造、求值及条件作用均已验收 | 本基础名字包不再列为待做；实际统一条件／群作用、HS 实例及强迫公式解释也已接通。第 8 的具体单子已实际构造；剩余消费者为 9–10 的模型应用与全局目标装配；不重造现成基础或重启字节兼容 |
| 6 | 背景、解释、universe | 供体完整 L/ZFC 已在固定旧版复用；原生与源语言逐公理／全模式、Choice、全局序及非空原核证书齐备。ConstructibleSource 逐点域对应、源 binder 对应、解释背景和非空前提实际消去，既有 InterpretedZF 已被真实消费 | 原 f28b033 第 6 行固定背景／universe、逐实例 Derives、不加不可达的验收门已完成；不再列作待做。全部内部／非标准 Proof/Con 归 10，不重证 L 或增加 GCH |
| 7 | 源强迫前端 | 原子／公式／固定证明保真、实际作用／正规滤子、全秩 HS、七条固定公理与完整 Separation／Replacement 已验收；已接通原 forces_ZF，逐源公理／模式有原核证书 | 前端合同已闭合，保留原单子／呈现／正规滤子前提；第 8 的原核存在句现已提供实际具体构造；第 9 消费这些父输入。全部内部公式／证明码归约仍属 10；不能把此逐实例证书说成最终内部 Con |
| 8 | 源代数／构造核心 | 同一 Base/T、完整实际饱和历史／转移／最终行、理想／基数、纤维／粘合、标签／传输、完整选择器／轨道／记录族和 Assigned 图已验收；具体商双射及完整 nonwellorderable_quotient_bijection 已验收；ForcingConcreteSystem 的无参数原核存在句实际构造全部 37 原始条件／40 内部集合，并在同一见证上消费全称商结论 | 本阶段所列全局装配门已完成；第 9 阶段消费同一具体系统，不重建原基础 |
| 9 | 源模型应用 | 同一实际Core、ACwo、¬AC、ordinal_presentation、完整切片／候选族／assemble及presentation_reverse_injection均已接通；全集合reverse_injection_dense及实际forces_PP有普通nativeZF原核L相对化端点 | 本阶段模型应用链完成；PP前没有给定稠密性、满射或HS名字前提；保留全部内部量词 |
| 10 | 原 Main 全局装配与对象内部化 | 同一实际系统的源目标理论及reverse_injection_dense→forces_PP→forces_target已接通；原公理行和完整模式流水线的存在、闭类型、独立见证唯一性已证明；实际ZF/U完整公理表的统一闭类型现由原六规则theoryShape有界查询消费；本批原正文→实际编译／三个原重命名矩阵→原模板→整个闭包→准确原生Separation/Collection句的quotation对象双条件已全部接通，五个普通nativeZF原核端点通过。正文／次数仍为外部模式索引，原始有效输入guard保留；同一实际内部Con及精确reduction现已组装，原核reduction→goal逻辑封闭门已验收；实际完整公理查询到同一理论原node/root证明的内部生产基例已构造 | 统一内部／非标准ZF/U公理正确性／强迫、全部内部六规则Proof及矛盾码归约、最终内部Con蕴含。标准quotation模式不替代此门 |
| 11 | 终验与发布评审 | 现有审计工具可复用；最终验收未开始 | 核对源到目标对应、命题量词、依赖及原核主句；发布另按用户授权，不把辅助构建通过当最终通过 |

## 当前 agent 执行入口

| 已有输入 | 当前消费者 | 真正的验收门 |
|---|---|---|
| 原完整raw模式码流水线及准确原生模式句quotation，已有原核双条件 | ZF/U统一内部公理正确性／强迫 | 覆盖任意内部／非标准正文和参数；原完整标准quotation、三个矩阵、模板、整个闭包及存在／类型／唯一性均已完成，不重做 |
| 现有六节点、27逻辑模式、语法操作、证明树和Proof/Sat配套 | 全内部及非标准证明码归约 | 不限外部标准码；不另建通用核、编码器或满足关系 |
| 全部源数学应用和上述内部传输 | 最终对象Con蕴含 | `FirstOrder.Derives nativeZF []`的原核闭句；最终主句仍未证明 |
| 原4.34.1 Main构建与五端点审计已通过 | 原Comparator／原第11最终复现 | Comparator仍单列未验收；本仓CheckStep4不是Comparator |

当前只推进统一内部／非标准ZF/U公理正确性与全内部Proof/Con。原Project翻译／重命名交换、三个实际编译矩阵及原正文到完整模式句的标准quotation链本批均已接通。复用现成ObjectProofNode、ReducedProofPresentation、PureProvability/PureSourceLocalTests和同一原强迫解释；不重建L、数学公理模式、满足关系或证明核。

## 工程执行约定

- 权威当前状态见STATUS；最新本批报告为`verification/internal-axiom-proof-acceptance.json`。
- 对象语言、背景和内部Con规格见OBJECT_TARGET；不得把外部模式索引误当统一内部真值断言。
- 固定源和供体哈希见SOURCE_LOCK；原4.34.1与目标4.33.1隔离。Lean/Lake串行。
- 每批先完成源码／跨平台检查及九条完整验收命令，保留五条trust=0门；再统一提交；等待上一批远端CI终态成功并读实际日志后才推送下一批。本地完整通过不冒充Linux干净环境通过。
- 不重启退役Packet／reader或反射实现，不重造L、全公理模式、通用算术、递归、Proof/Sat；不以行数、构建或审计数量代替最终证明。

原第10当前执行点：ForcingAtomicCode已构造原子分支的全部内部编码见证和准确类型，输入绑定范围可内部非标准、源自由范围为零、R为固定外部模板。下一消费者为原完整强迫解释的递归公式代码编译，不得把此分支当作全公式／全部Proof或Con已完成；继续复用现有内部递归、原11构造子与混合替换，不能另建通用语法核。

原子分支现在还提供独立实际见证下的对象单值性及带类型唯一输出，满足后续集合值递归的该项确定性要求；原总性输入范围不变。继续原第10的全公式／内部Proof归约，不新增阶段或语法后端。

原第10新消费者：ForcingAtomCode直接解析实际四种原子公式码，取得准确类型及独立见证下的唯一输出；真常量的原toBasic规范化有单列原核证书。下一门仍是逻辑／binder递归及全部内部Proof归约，不把原子入口当作全公式解释。

CI故障先定位再修复：42483548594主线成功，Comparator尚未开始就被ABI要求拦截。修复后的快速Linux守卫预检先于长构建。上一轮失败时，先读日志并修复，经本地完整验收后只推送包含修复的合并批次；不得重跑同一未修复错误或连续推送其他批次。正常批次继续等待上一轮成功终态和实际日志。

原第10当前新增操作：ForcingConditionRebind在普通nativeZF内为任意内部合法公式码／范围构造准确的条件变量重绑定，全部实际head／表／编码列表／替换见证均在对象EX内消去，结果有类型且不依赖执行见证。它对应原Force否定／存在分支；下一消费者仍为逻辑／binder完整递归，不是最终Con。验收见verification/forcing-condition-rebind-acceptance.json。

原第10的字面守卫代码：ForcingGuardCode已构造q∈P／R(q,p)模板的内部带类型唯一输出，允许内部非标准绑定范围和候选；自由范围为固定R参数数目加P/p的对象numeral。bound_guards_total在同一对象EX内构造bvar0和两个守卫，negative_inputs_kernel_certificate实际消费ForcingConditionRebind的子码重绑定。旧原子证明正文不变，仅新增八个直接调用旧证明的复用端口。守卫模块本身不提供外层公式；否定分支的完整码构造现由ForcingNegCode接通。存在分支与全递归、统一公理强迫及Proof/Con归约仍未完成。验收见verification/forcing-guard-code-acceptance.json。

原第10的完整否定码分支：ForcingNegCode实际构造子码重绑定、同一新条件的两守卫、falsum、三次imp和forall，取得普通nativeZF原核带类型唯一输出及独立执行唯一性。子码与绑定范围可内部非标准；R和参数数目为固定外部模式，条件free槽严格为对象numeral(n+1)。本项不再列为待做；原始全构造递归、存在分支、统一内部公理强迫及全部Proof/Con归约仍未完成。验收见verification/forcing-neg-code-acceptance.json。

原第10存在分支的守卫复用：ForcingExistGuardsCode用已有守卫编译器构造域谓词H(x)，原AST等式证明它是关系模板的特例；用逆序关系守卫加实际重绑定构造方向准确的R(r0,q1)，取得内部带类型唯一输出。没有第二套模板后端。新名字head也在对象EX内构造。仍需存在子码在两个条件和新名字下的binder重排、完整外层exists码及全递归／Proof／Con归约；不再把H模板或内部守卫方向列作缺口。验收见verification/forcing-exist-guards-code-acceptance.json。
