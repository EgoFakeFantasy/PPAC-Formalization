# 对象层最终目标与内部 Con 规格

2026-11-08：本文件只保存对象目标及编码合同。当前状态见STATUS，原1–11阶段见AGENT_WORKFLOW；旧批进度保留在Git及验收报告，不从旧“S3／STEP4”文件名推断当前阶段。

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

## 固定验收边界

- 最终验收必须给出上述同一纯语言、普通nativeZF和全部内部证明码下的原核闭句；外部标准证书迁移、逐实例模式证明、模型语义、AST和编译均不能替代。
- 原ReducedProofPresentation／PureProvability的ZFC支撑背景和签名必须明确适配到ZF/U，不得直接把它们当成本目标的专用检查器。
- 完整公理码测试须覆盖七固定公理与任意参数／正文的Separation／Collection，以及目标三句；六规则及二十七逻辑模式的作用域、替换和前驱必须保持原规格。
- 已有成果和真正未闭合项只在STATUS和原阶段表维护；完整数学公理模式、L解释或既有递归不能因某个消费者未接通而重新列作待证。
