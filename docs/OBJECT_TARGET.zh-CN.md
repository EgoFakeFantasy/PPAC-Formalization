# 对象层最终目标与内部Con规格
本工程背景 B 固定为原 YesMetaZFC 的 SetTheory.ZF 经 Project.fo_theory 的纯语言像。
不加AC、不加不可达、不假定Con(B)。对象签名是单排序纯等词/成员语言ℒ；
推导关系固定原 FirstOrder.Derives，最终要求产生真实 HilbertDerivation 证书。

## 原理论、目标理论与最终句子
S = 原ZF（Collection呈现）；U = S + PP + ACwo + ¬AC。
PP、ACwo、AC是第一步翻译的内部集合图公式。源否定为imp到falsum，其像notAC保持不变。
最终交付应为 Derives B [] (Con_S → Con_U)，其中Con_S、Con_U是纯ℒ闭句。
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
之后还要将代码转换器表示到B内，证明内部Check关系的传输；
只对外部标准证书成立不足以证明Con_S→Con_U。


## 内部化前置进度及编码核对
4a已经实现实际有限序列：完整functionOn、值域限制、每点实际有界唯一值、实际唯一追加与精确前缀，
并在对象ω归纳内证明所有内部长度的实际序列存在。任意纯公式行测试有追加和前缀保持模式的原核证书。
这些是Proof关系所需前置，不是本规格的ProofZF/U AST或内部Con已经实现。

源码核对的数值约定以ProofT/IntrinsicQuotationEvaluation.treeValue/forestValue及SyntaxEncode为准：
forestValue([])=pair(0,0)+1=1；treeValue(node(tag,children))=pair(tag,forestValue(children))+1。
故保留全部原生构造的falsum是leaf(0)，其树数值是2。
ProofCode中普通自然数序列的空码0、NatPacket字节传输码及旧QuineEncoding.quote_hilbert均不是此树数值格式。
后续纯签名编码需保留无函数符号、membership编号0及原生11构造，不能直接拿扩展签名的符号表代替。
这些核对尚未取得内部算术化的对象正确性证书；4b–4f仍须实际实现。


内部递推进度：对任意参数总单值关系，原ZF核已证明实际自然前驱算子的总单值性、真实递归图存在唯一，
以及每个内部自然索引的实际唯一末值；原后继关系的具体义务也已实际消去。
这些模式的公式p是外部有限语法索引，每个实例含全部内部对象量词；不能据此声称任意内部公式码的检查正确性已经证明。
基本加乘已完成：全部内部自然索引有实际唯一自然数和/积、ω闭包、零点、双向后继方程，以及对象ω归纳的左零律。
两个实际零见证通过原Extensionality在对象核内对齐；原nativeZF有十个完整闭句证书，不残留未证递推假设。
加法已有双向左后继律、交换、双向结合、两侧抵消、两加数不降界、正加数严格成员界及和值为零刻画。
这些九个额外完整闭句均有原nativeZF推导；顺序界为真实对象相等/成员关系。
乘法现有两侧分配双向式、左参数后继双向式、交换/结合和两侧单位律；内部单位由Empty(z)及Succ(e,z)指定。
三项/四项加法重排及六个乘法代数闭句均有源ZF及原nativeZF推导；ZFContext仅封装原ZF公理包含关系。
加乘关系的半环律及自然次序差分、加乘单调/正乘数反射、基本因子与平方界均已完成。
差值存在与唯一性限制在内部ω；所有比较和中间值仍是对象量词。
原配数专门界、实际Gödel配数/结构码及其内部正确性尚未完成；全ω二元运算图未单独交付。
ProofZF/U AST和最终内部Con的完成状态没有改变。
详见STEP4_BASIC_ARITHMETIC_ACCEPTANCE.zh-CN.md。


2026-10-22核对固定底座InternalPairingRules的原配数分支：a∈b时为b*b+a，其余为(a*a+a)+b。
接下来的纯ℒ配数关系须实际构造中间自然值并证明总单值、分量界、单射及解码；本规格核对不计入实现。
该底座文件的ZFC模型语义证明不作为当前ZF原核证书的替代。


2026-10-22原配数对象推导更新：GodelPairSyntax保留上述严格分支和原多项式顺序，
平方与各次加法均存在量化实际对象中间值。ObjectGodelPair提供七个完整闭句的源ZF及原nativeZF证书：
全内部自然输入上的实际唯一自然编码值、编码值ω闭包、输出唯一性、双分量弱界、完整输入单射性，
以及低支[b²,(b+1)²)和高支[a²,(a+1)²)的平方区间。
区间中的平方与后继仍由对象量词关系指定；不固定宿主max、sqrt或Nat.pair。
全内部编码上的逆解码总性尚未证明，结构列表/树值正确性、专用ProofZF/U和最终Con主句仍未完成。
详细公式、实际验收和下一关见STEP4_GODEL_PAIR_ACCEPTANCE.zh-CN.md。
