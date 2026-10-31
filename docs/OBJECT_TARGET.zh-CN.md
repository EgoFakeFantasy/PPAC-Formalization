# 对象层最终目标与内部 Con 规格

2026-10-26：仅保留固定合同；旧的重复辅助进度存于 Git `7dbb1c1` 的本路径。当前阶段只见 AGENT_WORKFLOW，不能从旧“S3／STEP4”报告名推断原 1–11 阶段。

## 原理论、目标理论与最终句子
S = 原ZF（Collection呈现）；U = S + PP + ACwo + ¬AC。
PP、ACwo、AC是第一步翻译的内部集合图公式。源否定为imp到falsum，其像notAC保持不变。
最终交付应为 Derives nativeZF [] (Con_S → Con_U)，其中Con_S、Con_U是纯ℒ闭句。
这里的“→”是对象Formula.imp，不是Lean函数类型。
原生原核的一致性传输只是中间命题，不代替这条对象推导。

## 内部Con的固定数学定义
Con_T := ¬∃p (p∈ω ∧ Proof_T(p,code(⊥)))。
ω是最小归纳集：先定义Ind(w)为w含空集且对x↦x∪{x}封闭，
Omega(w) := Ind(w) ∧ ∀v(Ind(v)→w⊆v)；纯语言中以唯一w存在量词消去ω记号。
Proof_T是原Hilbert核的有限证明树检查关系，不是“存在Lean证明”或模型满足关系。

编码统一采用现有Quine树数值编码约定：
leaf/tag/fields按SyntaxEncode的AST树形；node(tag,fields)是后继后的Gödel配数，
fields使用同一structural_list_code。纯成员签名的函数符号表为空，关系表只有membership。
保留bound/free上下文长度、bvar/fvar位置及全部原生Formula构造子。
禁止仅按外部有限深度识别公式，禁止忽略量词下的上下文变化。

Proof_T(p,c)的展开规格：
存在由内部自然数索引的有限节点序列和根节点，所有引用索引严格小于当前索引；
每节点记录free上下文、完整结论AST和规则证书；根结论是closed的c。
节点只能是原核六种：logical_axiom、theory_axiom、modus_ponens、
forall_generalization、free_strengthening、free_substitution。
logical_axiom严格核验原27类模式；theory_axiom核验Ax_T(c)；
其余规则精确核验作用域、替换、全称化、结论和前驱对应。
Ax_S允许七个固定公理及任意参数、任意正文的原生Separation/Collection实例；
Ax_U(c) := Ax_S(c)∨c=code(PP)∨c=code(ACwo)∨c=code(notAC)。
所有检查通过算术/有限序列的ZF可定义关系展开成有限纯成员公式，不增加新谓词公理。
Proof_T不限制外部标准证明码；内部非标准ω、语法与序列也在量化范围内。

## 已锁定与尚待实现的边界
本文件锁定背景、内部公式的数学定义、编码约定和检查规则。
现有ZFC专用ReducedProofPresentation/PureProvability不等于上述ZF/U检查器，不能直接套用。
ZF/U专用检查器完整纯AST、任意内部码上的正确性以及主句Derives尚未实现，
归入后续对象算术化关卡；不能把此规格文档或参数化公式当作该关卡通过。
步骤2的职责是rename/instantiate及19条源规则到原核的证书传输；
其外部归纳证明必须返回真正的原核Derives证书。
之后还要将代码转换器表示到nativeZF内，证明内部Check关系的传输；
只对外部标准证书成立不足以证明Con_S→Con_U。



## 当前已证与未证

已证：语言及全部源规则传输、完整 ZF 呈现互导、AC 等价、通用域相对化，以及已列明的内部构造。完整公理模式在底座和本仓均已存在。
已完成的背景解释：同一任意原生 ZF 模型内部的 L/ZFC 已复用到固定底座；ConstructibleGround 和 ConstructibleSource 已取得全部原生／源公理与模式、Choice 及域非空的 L 相对化原核证书。既有 InterpretedZF 的背景和非空前提已被实际消去，原第 6 阶段验收门已经通过；不再把版本、源域或 L 全模式解释列作缺口。

已完成：完整 CompleteRound 从原父输入构造，包含全部请求／有界调度／内部塔、同一 last target/inclusion、K 索引 Probe 单射／profile／全新右因子精确公共锥、所有 Merger 全 RootSystem；forall15 原核证书相对化到同一现成内部 L，Choice/order 已实际消去。

本批又已完成实际整轮构造 trace 的保留、唯一选中整轮后继、全旧腿／base 更新、精确当前 inclusion 以及完整 Valid/AllSmall 追加保持；forall15/18 同一内部 L 相对化原核证书已验收。

本批又已完成有界原父背景下的实际完整内部多轮塔、全部内部阶段Valid/AllSmall、全12表／21合同及全塔精确相邻转移；forall17/16同一内部L相对化原核证书已验收。

源 ChainBound 的精确内部乘积界、具体 Cohen 反链界及 CodeCardinals 上界的同一 L 相对化原核证书均已完成；CodeCardinals 下界及完整 OrdinalCount 实例尚未闭合。源可数分支树的内部集合值求值和实际叶／节点算子实例化均已有普通 nativeZF 原核证书；所有内部 ω 子值图被完整使用，通用 Local/Total/Single 已被证明。完整内部树载体／叶码及任意内部 ω 树族的实际拼接封闭性现已取得普通 nativeZF 原核证书；同一全部树码的基数界现已由源 ω≤μ、μ^ω=μ、|A|≤μ 条件取得普通 nativeZF 原核证书；实际树求值装配和保留全部内部子节点索引的拼接求值方程现已取得普通 nativeZF 原核证书。根值范围界及源 choose 子树的内部装配现已闭合：ForcingCountableHull.hull_kernel_certificate 在普通 nativeZF 原核中证明完整源 CountableHull.exists_closed，最终闭句只保留源基数／运算／base 条件。实际 Cohen 条件的 code／decode／compatibleChoice 已取得普通 nativeZF 或同一内部 L 相对化原核证书，整个内部函数族及 decode(code(p))=p 均已落实；flip／任意 Option 值域限制／hcode／hbgraph／hbits／hbp 现已完成；实际内部 flip 函数图、限制图与相容性恢复已取得普通 nativeZF 原核证书。源 Bool×内部ω 运算现已构造并接到同一组实际 code／decode／选择／flip 函数；完整 CountableHull 已实际消费，hin、pack 和整个 antichain_cardinal_le 已闭合。ForcingCohenAntichain.bound_kernel_certificate 在普通 nativeZF 原核中证明同一内部 L 相对化的完整反链界，只保留源无限固定幂、实际条件载体和反链前提。CodeCardinals 上界现由 ForcingCodeCardinals 接通；下界及实际 OrdinalCount 仍未完成。

真正未闭合：第8的实际 OrdinalCount 前提及完整选择器消费者、CodeCardinals 下界及实际模型消费者（CodeLinks、固定序数表、真实 Preliminary 四条基本定律、强迫相等 iff 标签相等、精确稳定性、下降、尾群协变及保留 OrdinalCount 前提的稠密总性与满射性、LocalName/LocalQuotient/限制、Fiber/整分量粘合、eligibleSystemTransport 全族与自然性、Placement/Hull、EquivariantMixing、active_equal 和 support_descent 均已有原核证书），第9同一系统的模型应用，第10全秩PP/Main、ZF/U专用内部Proof/Con、全部内部/非标准矛盾码传输和最终原核闭句。内部ω₁+1、countable_stage、完整实际塔、最终Probe/Merger、同根图RootSystem/乘积相等iffCopyRel均已完成；最新验收见STATUS。complement_probes本批已接同一实际塔并通过全量验收，取得forall15同一L相对化的原核对象证书。本批又已完成target_cardinal/complement_cardinal的原核证书，原|K|=μ条件和完整内部双射图均保留。任意理想的单位首项内部ω共尾路径和最终ideal probes现也已有同一实际塔的forall15原核对象证书，不假设理想可数。实际P(ω)连续统后继μ及K:=μ已进入同一IdealTower，forall1/13原核对象证书已验收，这些Base几何合同现已由ConstructionConcreteBase实际消去，取得forall1完整Base/T和同一实际最终行全性质的原核对象证书。已有外部标准证书变换不替代内部码证明。

本轮已接通实际 Cohen ChainBound 及连续统实例，并构造完整条件载体和字面 LocalRecord 乘积载体的大小界；四项同一内部 L 相对化原核证书见 ForcingCohenCounting/ForcingCohenChainBound。它们完成 CodeCardinals 的 hcc/hrec 辅助条件，现已由 ForcingCodeCardinals 的实际 total/single 消费，取得上界原核证书；下界、实际 OrdinalCount 和最终内部 Con 仍未完成。

LocalRecord 条件层已补齐：实际内部拉回及同记录条件置换有普通 nativeZF 原核证书，保留精确标签／层／位。它不替代 LocalWitness 名字层等式、表示密度、CodeCardinals/OrdinalCount 或最终内部 Con。

LocalWitness 同记录相等现已接通名字层：实际根置换／条件传输／名字对称性／支持反射产生原根强迫等式，并由现成 equality_law 得出实际局部商值相等。Covariant 是源 hC 的对象公式前提；具体 labelClass 实例及完整表示密度现已接入，见下段。两个原核端点使用同一既有 L 消去 Choice，不等于完整 CodeCardinals/OrdinalCount 或内部 Con。

实际 LocalRecords 分离类名字、标签类与 separate_move／relationClass_move／labelClass_move 已完成；具体名字族总性、唯一性、协变，以及实例化到该族的同记录相等均已有原核证书。完整 classRepresentationSet_denseBelow 已完成：同一个加强图覆盖实际支撑及指定标签，并使原名字与实际标签类强迫相等。这些内容不再列为待证明。

CodeCardinals 的实际成员记录见证现已接通：ForcingCodeRecordWitness.member_kernel_certificate 在普通 nativeZF 原核中证明同一内部 L 相对化的完整见证句子。实际选中码、同一秩图、根名字、加强条件和字面记录 (m,(x,pb)) 全部保留；既有链接稳定性与表示稠密性被直接消费。同一记录关系的 single／ChainBound 组合及实际上界现已完成，见 verification/code-cardinals-acceptance.json；下界、实际 OrdinalCount、第 9–11 阶段及最终内部 Con 仍未完成。

本批已构造完整局部名字集的内部序数双射和同一个 HS／固定列表，并给出任意内部名字／条件的成员刻画；OutsideLocal 全称量化实际加强条件，普通 nativeZF 原核证明实际商限制无原像，同一内部 L 相对化原核证明精确交集下的不相等。probeDenseSet_dense/hits 同样已取得原核证书。这些原核端点不能替代尚未完成的对称解释内部 localList_wellorderable、CodeCardinals 下界或最终内部 Con。当前全量验收状态见 STATUS 及 verification/probe-local-list-acceptance.json。

实际 classFromLocal_profile 现已在 ForcingClassProfile.construction_kernel_certificate 中接通：原名字的目标商类在结论内构造，Obj 成员性、同名投影及完整可用性一起返回；不要求原探针图位于资格锥内。源的实际 System、Data、几何及局部列表仍作为具体装配接口，Choice 由同一既有 L 消去。该端点不替代 CodeCardinals 下界、完整 OrdinalCount 或最终内部 Con。

源 outsideClass_copies 现由 ForcingOutsideCopies.source_kernel_certificate 接通：在具体构造既定无限基数预算下，实际构造内部乘子族的子图族及一个内部 (条件,规范化名字) 记录函数。每个副本保留支撑、原根的字面限制、完整 isClass 和全部加强条件下的 OutsideLocal。原核闭句在同一个既有 L 中消去 Choice，未预设目标副本族或其排除性质。它不替代完整下界／OrdinalCount、localList_wellorderable／outside_localList 或最终 Con；全量验收以 STATUS 和 verification/outside-copies-acceptance.json 为准。

源主线纠偏：已撤回 classFiberEmbedding → classFiber_dense_lower → ordinalType_lower_count 的错误调用链。前两者进入独立的 QuotientActions.classFiber_dense_exact 分支，不是最终 ordinalType 下界的必要前置；e071a55 新增的独立纤维嵌入模块和其专用入口已退役，既有 profile/Outside 证明保留。恢复及精确清单见 verification/class-fiber-nonmain-review.json。

ForcingProbeRowHits.source_kernel_certificate 直接迁移 CodeCardinals.ordinalType_lower_count 的 hdisj/hits:196–218：实际投影既有 Outside 副本的条件坐标，证明根外支撑不交，再证明全部内部行与全部扩张根的条件均有共同加强的副本命中。原核对象句子存在量化实际条件函数，保留逐点图双条件；Choice 在同一既有 L 中消去。未假定泛滤存在或命中集合族，也不引入该旁支。下界关系 stable/total/single 及最终基数计数的具体接线、OrdinalCount 和内部 Con 仍未完成；现成对应后端不重做。本批验收见 STATUS 和 verification/probe-row-hits-acceptance.json。

## 2026-10-30 主线实际副本的稳定工作码

`ForcingProbeStable.source_kernel_certificate` 的结论在原生纯成员语言中闭合，位于同一现成内部 L。它量化所有内部加强条件，实际构造一个持久链码，且每项名字在原根强迫等于原 Copy 记录中的同一名字；稳定 profile 从实际副本和已有 profile/主滤子接口推出，不作为假设传入。背景仍为普通 nativeZF；无新增对象 Choice 公理。源对应是 `CodeCardinals.ordinalType_lower_count` 的 hel/stable 和 total 的工作码产生步骤。全量验收通过：3030 构建、34358 项声明，9 条命令／5 次 trust=0 均退出 0；全部旧足迹不变、零警告、无新增公理依赖。见 verification/probe-stable-acceptance.json。该端点不是完整下界、OrdinalCount 或最终内部 Con。

## 2026-10-30 主线 total 的实际秩见证

`ForcingProbeTotal.source_kernel_certificate` 在普通 nativeZF 中证明同一内部 L 的对象句：从实际 Outside 副本和原类型强迫等式，产生加强条件、选中码、同一图中的秩名字、内部 β∈θ 及 check-name 强迫等式，并保持与同一副本名字的 Links。既有 dense_selected 仅开放可见性，原证明正文不变；没有重建选择或秩后端。该证书是行命中之后的 total 见证生产者；全部行关系装配、single、最终基数计数和内部 Con 仍未完成。全量验收通过：3031 构建、34363 项声明，9 条命令／5 次 trust=0 均退出 0；全部旧足迹不变、零警告、无新增公理依赖。见 verification/probe-total-acceptance.json。

## 2026-10-30 主线 single 的实际副本排除

`ForcingProbeSingle.source_kernel_certificate` 是普通 nativeZF 原核中的对象闭句，沿同一内部 L 量化全部内部见证条件及可能共同加强。结论为同秩独立副本的见证条件无共同加强。秩判别、Links/Same、公共根交集和实际 Outside 排除均实际接通；不存在把选中码／原名字相等或不相容当作未消去假设的替代。源对应 `ordinalType_lower_count.single:254–283`。全行关系及最终基数计数和内部 Con 仍未完成。全量验收通过：3032 构建、34367 项声明，9 条命令／5 次 trust=0 均退出 0；全部旧足迹不变、零警告、无新增公理依赖。见 verification/probe-single-acceptance.json。

## 实际计数与密集总性/满射性的对象证书（2026-10-30）

ForcingProbeRows、ForcingConcreteOrdinalCount 与 ForcingIdealProbeCount 已将同一内部行关系、上下界和实际探针/副本接通。本批 ForcingConcreteGermDensity.source_kernel_certificate 再消去密集总性/满射性的抽象计数前提，并实际构造同一 selection 的秩和一张内部序数表；rank 家族固定性、selection 固定性及根群包含由现有尾群协变与收集定理推出。

对象结论覆盖全部加强 delta 的内部条件、全部共同顶点/标签，以及全部具有 Works/Links 的内部名字见证。证书仍在普通 nativeZF 中相对于同一现成内部 L，不增加对象 Choice 或外部标准性前提。旧 Preliminary 语义和对象 AST 已用 trust=0 下的 rfl 检查定义等同。

同一终行/AllIdeals、rank/selection 方程、尾群/全局固定名字界、局部列表/枚举/标签/参数及初始 outside-class 见证仍是明确源输入。分量 germ/selector、赋值图和具体商双射消费者、PP/Main、全部内部/非标准证明码的最终 Con 尚未完成。最新验收状态见 STATUS；密集性对象证书不是最终主句。

## 链对齐的对象证书（2026-10-30）

ForcingGermAlignments.source_kernel_certificate 的背景是 nativeZF，语言是原纯成员语言，推导关系是原 FirstOrder.Derives。最终闭句存在量化实际内部链索引图，并覆盖所有内部自然数上的对齐存在/有界性、共同推进及两条精确乘法方程、相同对齐的尾固定等价关系。完整语法与语义对应逐项由 Lean 检查，没有抽取宿主层序列、外部有限路径或标准自然数。

这里的 monoid/joins、ω/zero、完整顶点载体、实际余终链和分量稳定置换是固定源本段的输入。现成原生集合函数、顶点/箭头、置换复合被直接复用。此证书供后续 countable_quotient_of_cells 消费；不把它记为已证明可数重排、有限 gate 下降、countable_germs 或完整选择器。最终内部 Con 仍未完成；上方较早批次中的“未完成”只表示当时状态，当前范围以 STATUS 为准。

## Cell 下降门的对象证书（2026-10-30）

ConstructionCellDescent 的 probe_kernel_certificate、merger_kernel_certificate 和 attachment_kernel_certificate 均在 nativeZF 原核中证明纯成员语言闭句。前两者从实际字/乘法/旧包含图产生 gate 规则；第三者消费该规则、同一保守嵌入、复合包含图及实际像，将规则传输到终单子，保持任意终单子右因子的量词范围。

Probe 的旧输入消耗通过现成纯公式 Raw 归纳及实际求值方程证明，覆盖全部内部字长。此批尚未产生具体塔的内部有限替换路径，也未证明可数重排、完整 germ 选择器或最终内部 Con；这些源消费者仍按 STATUS 中原阶段顺序推进。

## 内部有限下降的对象证书（2026-10-30）

ConstructionFiniteDescent.source_kernel_certificate 的语言、背景和推导关系仍为纯成员语言、nativeZF 和原 FirstOrder.Derives。结论存在量化真正的内部有限序列；每个相邻项都是固定源 Replaces，保持同一右因子的两条乘法方程。路径逆向存储只是内部序列追加的表示方式，方向在 Path 公式中显式规定。

对象 At 公式的分离实例供应反例集，既有内部序数归纳完成零/后继/极限三分证明。因此此结论不局限于外部标准自然数或外部良基模型。全部塔/索引/对齐输入均保留为明示前提；本批不宣称已经构造实际重排塔或完成可数商。后续只沿源 countable_quotient_of_cells 所消费的端点推进，不扩建未被使用的路径理论。

## 推送重排定理的对象证书（2026-10-30）

ConstructionPushoutPasting 的四个原核端点分别覆盖 flip、paste、cancel_left 和 of_id。它们复用现有纯成员语言的同态、图复合、交换方块及完整单子推送定义；量化所有内部目标单子、同态和候选普遍映射，保留存在性与唯一性。复合映射由已有原生集合函数构造器实际产生。

背景仍为 nativeZF，推导关系为原 FirstOrder.Derives。结论是固定源普遍性质的传输规则；现有方块、同态、复合图或恒等图作为明确前提保留。源 future_cut/future_omitted_square 确实消费这些规则；实际选中子构造、呈现像识别、定向并方块及可数重排塔仍须继续构造，不将本批误报为 countable_germs 或最终内部 Con。

## 推送比较与换元的对象证书（2026-10-30）

ConstructionPushoutIdentification.comparison_kernel_certificate 在普通 nativeZF 的原 FirstOrder.Derives 中证明一个纯成员闭句：对于同一 span 的两份完整推送，实际存在两张同态图，它们互逆并分别与两侧基底映射交换。两张比较图是结论中的对象存在量词，不是宿主选择函数或输入假设。

apex_kernel_certificate 与 left_kernel_certificate 迁移完整普遍性质；内部目标单子及候选映射仍全称量化，换元使用的内部同态、逆图和边界等式则作为明确前提保留。复用既有 ModelTransfer 对同一原生语言及模型范围的原核转移；没有增加对象层 AC 或不可达假设。

这些端点是固定源 CellCuts 呈现识别的必要消费者接口。实际 cell 原像、所选后继像的满射性以及后续可数重排仍须接通；本批不是最终内部 Con 证明。

## 两类 cell 原像的对象证书（2026-10-30）

ConstructionCellPreimage.probe_kernel_certificate 与 merger_kernel_certificate 在普通 nativeZF 的原 FirstOrder.Derives 中证明实际对象存在量词结论。Probe 返回参数原像、整条内部路径及精确映回关系；Merger 返回规范起点表、其完整 Valid 性质和恢复原表的 Graph 等式。索引仍在对象域内，结论不局限于外部标准有限情形。

原像族使用原生值域／逆双射和集合函数复合构造。已有 ConstructionSaturationProbeStage.reflect_path 与 ConstructionMergerPrescriptionMap.valid_of_map 原样复用；参数在保守同态像内的条件沿用源前提，不作为已经证明的依赖闭合结论。后续仍须通过实际呈现生成性与有限旧系数建立该前提，并完成选中后继的像满射及推送识别。不能将两类原像已构造误报为可数重排或最终内部 Con 已完成。

## Merger 呈现验收补记（2026-10-30）

ConstructionMergerEvaluation 与 ConstructionMergerPresentedLift 将固定源 MergerPushouts 的字求值、实际 Copies 商解释和旧系数／根的唯一提升迁入纯成员闭句。最终输出为原核 nativeZF 中的对象存在唯一性；证明使用现有公式归纳，量词遍历全部内部字和目标单子，不加入外部标准性或目标消去律。实际呈现合同是显式输入，不能把本闭句当作已完成 mergerSimulation_pushout，更不能当作最终 Con_S → Con_U。验收见 verification/merger-presentation-acceptance.json；当前仍为原阶段 8。

## Merger 实际推送验收补记（2026-10-30）

ConstructionMergerPushout.source_kernel_certificate 内部存在量化并构造映射处方、两侧实际 Merger 与模拟图共 24 个输出，证明全内部目标单子的 IsPushout 和原 mergerSimulation_snoc 方程。输入为源的基单子、有效处方、保守基映射及条件交；没有预设两侧呈现或推送。它不声称输出模拟图的四项 Conservative 条件已验收，也不替代最终 Con 闭句；下一消费者的这部分合同仍需核对并接入。全量验收见 verification/merger-pushout-acceptance.json。

## Merger Copies 保守传输输入（2026-10-30）

ConstructionMergerCopiesMap.source_kernel_certificate 在原 nativeZF 推导核中，由同一两侧实际呈现和源保守基映射构造 Copies 图，证明精确代表元方程、单射、右作用相容、任意目标右因子留在旧像，以及每个目标共同上界之下的旧共同下界。两侧呈现复用 ConstructionMergerPushout 的已验收生产者；本句不预设 Copies 图，也不限制外部标准字长。

这些性质对应固定源 Word.transport_conservative 的 Copies 输入。它们尚不构成整个字模拟的 Conservative 证明；字因子传输、字共同下界及与实际 mergerSimulation 的接合仍须完成。最终对象 Con 未完成。实际验收见 verification/merger-copies-map-acceptance.json。

## 实际 Merger 字模拟保守性的原核证书（2026-10-30）

ConstructionMergerWordTransport.source_kernel_certificate 复用完整 MergerPushout 的 24 个内部存在输出，并新增四项 Conservative 结论：单射、目标右因子留在旧像、所有旧交的保持、共同倍数反射。因子按内部结果字归纳；共同下界按任意内部目标字归纳，调用已验收的 Copies 因子与共同下界。raw_eq_simulation 证明该 Raw 图等于此前实际构造的 mergerSimulation，故不是另一个兼容映射的替代结论。

与上一批对象句子的差异已核对为只增加实际模拟的 Conservative 合取项；原对象量词、基理论和完整推送性质保持。该源缺口现已关闭，不能继续列为待做。ConservativeCells 生成性／有限旧系数现已由后续批次完成；实际依赖图、所选后继、可数重排及第 9–11 阶段仍须推进；最终内部 Con 尚未完成。实际全量验收见 verification/merger-word-transport-acceptance.json。

## 两类生成性与实际普通闭包的原核证书（2026-10-30）

ConstructionCellGeneration 的 merger_kernel_certificate／probe_kernel_certificate 在同一实际呈现前提下，证明任意内部普通子单子若包含全部旧像及全部新生成元像，就等于整个扩张；并证明每个内部元素属于这两族像生成的闭包。证明直接消费原呈现提升和唯一性，未添加对象选择公理，也没有把子单子加强成保守包。

closure_kernel_certificate 由原生 Separation 构造实际内部最小子单子，闭包成员公式量化全部内部子单子。源 Cell.finite_coefficients 已由后续 ConstructionCellCoefficients 完成；其有限旧系数不能等同于给整个可数新生成元族加有限支撑。实现复用了下层原生 ZF 接口，没有调用要求 ZFC 的 PureSequenceConcatenation 封装。实际全量验收见 verification/cell-generation-acceptance.json；最终内部 Con 未完成。

## 两类 cell 有限旧系数的原核证书（2026-10-30）

ConstructionCellCoefficients.merger_kernel_certificate／probe_kernel_certificate 已证明固定源 Cell.finite_coefficients 的对象版本：对同一实际扩张中的每个内部 x，存在同一内部旧系数集合 S 与内部自然数 n，使 S⊆D、S 可单射到 n、S 有内部有限满射枚举，并且 x 属于 old(S) 和全部新生成元像生成的实际闭包。后者复用上一批已构造的原生 Separation 闭包。

源闭包归纳的空集、单点、并集分支均已实现；有限并用底座 ZF 序数加法和函数图构造，有限界用已固定供体的最小原像证明。没有外部标准长度限制、宿主 Finset 或额外对象 Choice 前提。CellTowers.Attachment.finite_coefficients 的同一系数传输已由后续 ConstructionAttachmentCoefficients 完成；实际 dependencies/selected_word/restrict_selected 尚待接合，不等同于本批 cell 本身结论未完成。实际全量验收见 verification/cell-coefficients-acceptance.json；最终内部 Con 未完成。

## Attachment 同一系数传输与局部保留闭包（2026-10-31）

ConstructionAttachmentCoefficients 的 merger/probe 原核证书以实际呈现、实际同态 F、旧元素固定性及具名目标 R 的精确值域为前提，结论保留同一个 R，构造实际复合旧包含图／完整生成元图，并给出 R 中每个内部元素的有限旧系数。证明在同态原像子单子上应用已有闭包性质，使用同一个 S；原生值域唯一性将构造结果识别到输入 R。背景仍为 nativeZF，不添加 Choice。

retained_kernel_certificate 在显式给定本次 S 的旧像被保留的前提下，构造 retained ∩ D 并传输闭包成员性。它没有构造 tower 的支撑选择或 dependencies 图，也没有消去依赖闭合前提，不能称作整个 selected_word 或 restrict_selected 已完成。单 attachment 的内部支撑／依赖图已由后续 ConstructionAttachmentDependencies 构造；全 tower 汇总仍需保持每阶段同一 cell，继续复用已有 L／全局序和内部函数构造。三个端点和全仓验收见 verification/attachment-coefficients-acceptance.json；最终内部 Con 未完成。

## 单 Attachment 可数依赖图与实际保留词消费（2026-10-31）

ConstructionAttachmentDependencies.construction_kernel_certificate 是原 nativeZF 中的 L 相对化对象句：在同一个实际 ImageResult/R/旧包含图/完整生成元图上产生内部支撑函数 C 和精确依赖图 deps。选定支撑取已有全局序下的最小见证，调用 ConstructionRoundSelection.least_denote；实际函数图调用原生 Replacement/函数构造，L 背景由现成解释消去。

selected_kernel_certificate 直接在 nativeZF 中从这个 deps 的依赖闭合推出参数及全部生成元被保留，并构造 retained ∩ D 上的闭包证明。此前局部证书中的额外支撑保留前提已在本批实际消去。countable_kernel_certificate 直接在 nativeZF 中证明每个内部依赖行可数，沿用源参数集／生成元索引可数条件；有限旧支撑与完整生成元族不混淆。

严格边界：这是一个固定 attachment 的图，旧元素的空局部行不能替代全 tower 中由 newIndex 选择的早期依赖。全 tower 的 BlockTowers.flatten/Saturation.cells、统一 stepCell/首次出现索引仍待接合；实际参数集计数已由后续 ConstructionCellParameters 完成；restrict_selected、重排和最终内部 Con 均未完成。全量验收见 verification/attachment-dependencies-acceptance.json。

## 实际参数集及内部可数依赖图（2026-10-31）

ConstructionCellParameters.probe_kernel_certificate／merger_kernel_certificate 在原 nativeZF 中证明 L 相对化对象句：从实际呈现、同态、旧元素固定性及给定 R 的精确值域，存在精确参数集、复合旧包含／生成元图、有限支撑函数与 deps，满足同一个 R 上的 ImageResult 和 Dependencies ω R deps。参数集可数性和索引可数性已实际证明，调用者无需另给。

Merger 参数恰为实际 start 的两坐标；补默认单位只用于构造计数上界，随后 Separation 保证精确参数集。证明覆盖全部内部 n∈ω，未要求外部标准性。Probe 使用完整内部路径值域与三个指定参数。计数复用 ExistingOrdinalImage、ExistingCardinalBounds 和原生 ZF 函数／分离接口，背景解释复用已完成的 L。

本句仍为单个实际 attachment；首次出现索引、全 tower 汇总、restrict_selected、重排和最终 Con 未完成。实际验收见 verification/cell-parameters-acceptance.json。
