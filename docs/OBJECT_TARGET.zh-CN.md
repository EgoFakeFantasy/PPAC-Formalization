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

源 ChainBound 的精确内部乘积界及同一 L 相对化原核证书已完成；具体 Cohen 反链界及 CodeCardinals 实例尚未据此闭合。源可数分支树的内部集合值求值和实际叶／节点算子实例化均已有普通 nativeZF 原核证书；所有内部 ω 子值图被完整使用，通用 Local/Total/Single 已被证明。完整内部树载体／叶码及任意内部 ω 树族的实际拼接封闭性现已取得普通 nativeZF 原核证书；同一全部树码的基数界现已由源 ω≤μ、μ^ω=μ、|A|≤μ 条件取得普通 nativeZF 原核证书；实际树求值装配和保留全部内部子节点索引的拼接求值方程现已取得普通 nativeZF 原核证书。根值范围界及源 choose 子树的内部装配现已闭合：ForcingCountableHull.hull_kernel_certificate 在普通 nativeZF 原核中证明完整源 CountableHull.exists_closed，最终闭句只保留源基数／运算／base 条件。实际 Cohen 条件的 code／decode／compatibleChoice 已取得普通 nativeZF 或同一内部 L 相对化原核证书，整个内部函数族及 decode(code(p))=p 均已落实；flip／任意 Option 值域限制／hcode／hbgraph／hbits／hbp 现已完成；实际内部 flip 函数图、限制图与相容性恢复已取得普通 nativeZF 原核证书。源 Bool×内部ω 运算现已构造并接到同一组实际 code／decode／选择／flip 函数；完整 CountableHull 已实际消费，hin、pack 和整个 antichain_cardinal_le 已闭合。ForcingCohenAntichain.bound_kernel_certificate 在普通 nativeZF 原核中证明同一内部 L 相对化的完整反链界，只保留源无限固定幂、实际条件载体和反链前提。CodeCardinals 上／下界及实际 OrdinalCount 仍未完成。

真正未闭合：第8的实际 OrdinalCount 前提及完整选择器消费者、CodeCardinals 及实际模型消费者（CodeLinks、固定序数表、真实 Preliminary 四条基本定律、强迫相等 iff 标签相等、精确稳定性、下降、尾群协变及保留 OrdinalCount 前提的稠密总性与满射性、LocalName/LocalQuotient/限制、Fiber/整分量粘合、eligibleSystemTransport 全族与自然性、Placement/Hull、EquivariantMixing、active_equal 和 support_descent 均已有原核证书），第9同一系统的模型应用，第10全秩PP/Main、ZF/U专用内部Proof/Con、全部内部/非标准矛盾码传输和最终原核闭句。内部ω₁+1、countable_stage、完整实际塔、最终Probe/Merger、同根图RootSystem/乘积相等iffCopyRel均已完成；最新验收见STATUS。complement_probes本批已接同一实际塔并通过全量验收，取得forall15同一L相对化的原核对象证书。本批又已完成target_cardinal/complement_cardinal的原核证书，原|K|=μ条件和完整内部双射图均保留。任意理想的单位首项内部ω共尾路径和最终ideal probes现也已有同一实际塔的forall15原核对象证书，不假设理想可数。实际P(ω)连续统后继μ及K:=μ已进入同一IdealTower，forall1/13原核对象证书已验收，这些Base几何合同现已由ConstructionConcreteBase实际消去，取得forall1完整Base/T和同一实际最终行全性质的原核对象证书。已有外部标准证书变换不替代内部码证明。

本轮已接通实际 Cohen ChainBound 及连续统实例，并构造完整条件载体和字面 LocalRecord 乘积载体的大小界；四项同一内部 L 相对化原核证书见 ForcingCohenCounting/ForcingCohenChainBound。它们完成 CodeCardinals 的 hcc/hrec 辅助条件，不等于已证明实际表示关系 total/single、OrdinalCount 或最终内部 Con。

LocalRecord 条件层已补齐：实际内部拉回及同记录条件置换有普通 nativeZF 原核证书，保留精确标签／层／位。它不替代 LocalWitness 名字层等式、表示密度、CodeCardinals/OrdinalCount 或最终内部 Con。

LocalWitness 同记录相等现已接通名字层：实际根置换／条件传输／名字对称性／支持反射产生原根强迫等式，并由现成 equality_law 得出实际局部商值相等。Covariant 是源 hC 的对象公式前提；具体 labelClass 实例及表示密度仍需接入。两个原核端点使用同一既有 L 消去 Choice，不等于完整 CodeCardinals/OrdinalCount 或内部 Con。

本批 ForcingRelationClass：固定 LocalRecords 的实际分离类名字及局部标签类已接通，四个普通 nativeZF 原核端点保留全部内部条件／名字量词；具体局部类的支持、界和每处 isClass 均实际证明。未将强迫资格等同于最终 PP／Con；精确移动协变、classRepresentationSet_denseBelow、完整 CodeCardinals／OrdinalCount 及原第 9–11 阶段仍未完成。验收见 verification/relation-class-acceptance.json。

本批 ForcingRelationClassMove 已证明精确 separate_move／relationClass_move／labelClass_move，取得具体名字族总性／唯一性／协变的普通 nativeZF 原核证书；同记录局部商相等已实例化到此族，原抽象协变前提由实际标签数据及 E 支撑消去，Choice 经同一内部 L 消去。表示稠密性、完整 CodeCardinals／OrdinalCount 和最终内部 Con 仍未完成。验收见 verification/relation-class-move-acceptance.json。

ForcingLabelDensity 已在普通 nativeZF 中证明实际标签类稠密见证。本批 ForcingClassRepresentation.density_kernel_certificate 又接通固定源完整 classRepresentationSet_denseBelow：任意加强 Cohen 条件下，都存在同一加强图覆盖实际支撑及指定标签，并使原名字与实际标签类强迫相等。构造复用已完成的补集基数、单射扩张、支撑和单点界；完整对象句子相对化到同一现成内部 L，Choice 在其中消去。下一直接消费者是 CodeCardinals.ordinalType_cardinal_le.total／single；完整基数界、OrdinalCount 和最终内部 Con 仍未完成。验收见 verification/diagram-coverage-acceptance.json。
