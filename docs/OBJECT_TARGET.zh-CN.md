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

真正未闭合：第 8 阶段的完整轮次请求实现／重复 probe 独立性及多轮饱和性（实际单轮有效内部递归塔／时间恒等／全塔 fromBase 自然性／精确 map_succ 原请求 inclusion 方程／完整原请求基数界、同一索引／规范序数／last 大小界、全部内部阶段界及选中实际 generator／当前 inclusion 强新鲜性已完成），第 9 阶段同一系统的模型应用，第 10 阶段 ZF/U 专用内部 Proof/Con、全部内部／非标准矛盾码传输和最终闭句。已有全部外部标准证书变换不替代这些内部码证明。
