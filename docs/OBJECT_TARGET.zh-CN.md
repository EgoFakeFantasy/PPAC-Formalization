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


2026-10-22全内部解码对象推导更新：GodelUnpairSyntax.witness(w,p,a,b)明确为
(a∈w∧b∈w)∧Pair(w,a,b,p)，preimage是实际存在两个分量。
在编码p上作对象ω归纳：空码有实际零分量；两支内部推进和两处边界跳转均返回原配数关系证书。
故每个内部p∈w均实际可解码。exactAt为∀c∀d(witness(w,p,c,d)↔(c=a∧d=b))，
fiber实际取得a,b并给出此双向刻画，boundedFiber另外给出a≤p和b≤p。
六个完整闭句均有源ZF及原nativeZF实际推导。没有外部标准ω、宿主平方根或语义模型假设。
原配数与逆解码已经完成；原结构列表/树码、专用ProofZF/U与最终Con主句仍未完成。
详见STEP4_GODEL_UNPAIR_ACCEPTANCE.zh-CN.md。


2026-10-22原始结构节点对象推导更新：StructuralNodeSyntax.raw(w,tag,payload,n)为
∃q(Pair(w,tag,payload,q)∧Succ(n,q))，严格保留原raw_node的后继配数约定。
实际全内部自然输入有唯一正自然编码值，且tag∈n和payload∈n。
内部自然码n有raw_node分解当且仅当¬Empty(n)；每个正码实际取得自然标签和载荷，
任意候选对满足解码关系当且仅当它们等于实际分量，并有两个严格成员子码界。
九个完整闭句均有源ZF及原nativeZF实际推导。原始数值节点分解尚不检查有效标签或字段，
Nil/Cons、有效列表/树、专用ProofZF/U与最终Con仍未完成。
详见STEP4_STRUCTURAL_NODE_ACCEPTANCE.zh-CN.md。


2026-10-22原Nil/Cons构造器对象推导更新：Nil(w,n)为∃z(Empty(z)∧Raw(w,z,z,n))。
Cons(w,h,t,n)为∃z∃e(Empty(z)∧Succ(e,z)∧∃q(Pair(w,h,t,q)∧Raw(w,e,q,n)))。
实际零/单位见证全部在对象层取得并消去，原内外配数参数次序保持不变。
原Nil恰为实际内部单位且有实际唯一纤维；所有内部自然head/tail有实际唯一Cons值，
两个输入严格属于该值，Cons输入单射且与Nil互斥。互斥句不额外要求head/tail自然。
实际Empty(z)、Succ(e,z)、Succ(two,e)下，Nil(w,e)和Raw(w,z,e,two)均有原核证书，
固定原空字段列数值1及零叶封装数值2的对象关系；完整语法quotation及矛盾句码正确性仍待接入。
本批九个完整闭句均有源ZF及原nativeZF实际推导。
这些是构造器数值层结果，不预设tail已是有效列表；全内部列表/树递归有效性、专用ProofZF/U和Con仍未完成。
详见STEP4_STRUCTURAL_LIST_CONSTRUCTORS_ACCEPTANCE.zh-CN.md。


2026-10-22内部有限列表轨迹对象推导更新：trace(w,z,e,l,d,f,n)包含实际Empty(z)、Nil(w,e)、
l∈w、Succ(d,l)、原完整sequence(f,d,w)、种子edge(f,z,e)、末值edge(f,l,n)和每个i∈l的相邻Cons行。
每行实际存在后继索引j、前后值a,b和自然head，使Succ(j,i)、两条图边及Cons(w,head,a,b)成立。
Valid(w,n)存在量化z,e,l,d,f共五个内部对象，没有宿主List或外部标准长度限制。
实际Nil种子、Cons追加及前缀图构造给出完整对象双条件：
Valid(w,n)↔Nil(w,n)∨∃t(Valid(w,t)∧∃h(h∈w∧Cons(w,h,t,n)))。
已知自然Cons(w,h,t,n)下，Valid(w,n)↔Valid(w,t)；有效码属于w且非零，实际零码被排除。
轨迹批次十个闭句均有源ZF及原nativeZF推导；该批次尚未实现唯一内部长度、实际字段图及往返，
因此完整列表解码、树语法、专用ProofZF/U和最终Con的完成标志仍为False。
详见STEP4_INTERNAL_LIST_TRACES_ACCEPTANCE.zh-CN.md。


2026-10-22内部长度对象推导更新：
HasLength(w,n,l):=∃z∃e∃d∃f Trace(w,z,e,l,d,f,n)。
Ω(w)下，HasLength(w,n,l)∧HasLength(w,n,k)→l=k；此式没有归纳假设或已知唯一性前提。
其前提自身给出n,l,k∈w，全部候选为内部对象，包含外部看来非标准的ω成员。
Valid(w,n)给出实际纤维∃l((l∈w∧HasLength(w,n,l))∧∀k(HasLength(w,n,k)→k=l))。
任意两条同码迹即使采用不同零、Nil种子、域和完整函数图，其实际长度仍相等。
精确前缀存在式保留指定的前驱长度p与域l；已知Cons尾实际等于前驱边值。
Nil迹长度为空，Cons迹长度为尾的实际长度的后继，成员归纳在w内沿严格尾码界下降。
九个新完整闭句均有源ZF、sourceZF原核核心和原nativeZF证明；具体见STEP4_INTERNAL_LIST_LENGTH_ACCEPTANCE.zh-CN.md。
实际有序字段图、字段往返和完整列表解码尚未完成；专用ProofZF/U及最终内部Con仍为False。
原语言、原背景ZF、完整六条核规则/27种逻辑模式和全内部ω证明码的Con规格保持不变。


2026-10-22内部Cons投影及实际递归对象推导更新：
Selected_head(w,x,y):=∃a((y∈w∧a∈w)∧Cons(w,y,a,x))；
Selected_tail(w,x,y):=∃a((y∈w∧a∈w)∧Cons(w,a,y,x))。
HasCons_h(w,x):=∃y Selected_h(w,x,y)；
Step_h(w,x,y):=Selected_h(w,x,y)∨(¬HasCons_h(w,x)∧Empty(y))。
Ω(w)下每个内部集合x都有实际唯一Step_h值，且值属于w；输入不预设自然或有效列表。
原自然Cons输入分别返回实际head/tail，Nil和无Cons输入返回实际空集。
h为两个外部公式模式索引，不是新增对象排序、对象函数符号或对象布尔变量。
Iteration_h仍为原NaturalEvaluationSyntax.evaluation，即实际后继域、完整原递归图和实际边的存在公式。
原算子义务已实际消去；任意内部种子a与r∈w有实际唯一Iteration_h(w,a,r,y)。
另有实际唯一递归图、零点和后继方程；a∈w时所有求值属于w。
11个完整闭句模式/22个head-tail实例均有原nativeZF推导，见STEP4_INTERNAL_LIST_PROJECTION_ACCEPTANCE.zh-CN.md。
尚未把该递推与原列表构造迹逐步对齐，故实际完整有序字段图、往返、ProofZF/U和Con仍为False。


2026-10-22真实移位与Nil终端对象推导更新：
Coupled_h(w,a,b,r):=∀u∀v(Iteration_h(w,a,r,u)→Iteration_h(w,b,r,v)→Step_h(w,u,v))。
Ω(w)、r∈w、Step_h(w,a,b)推出Coupled_h；通过原Separation支持的对象ω归纳取得。
r∈w、Succ(s,r)时，Iteration_h(w,a,s,y)↔Iteration_h(w,b,r,y)。
a,b,y均为任意内部对象，没有递归正确性作为额外前提；实际求值仍有完整原图见证。

Ends(w,n):=∀l∀y(HasLength(w,n,l)→Iteration_tail(w,n,l,y)→Nil(w,y))。
Ω(w)下每个内部码满足Ends；无实际长度的码仅有蕴含，未因此认定它有效。
证明使用原Cons严格尾码界、精确实际前驱长度、真实tail移位和w内成员归纳。
给定完整Trace(w,z,e,l,d,f,n)，对象核实际证明Iteration_tail(w,n,l,e)，
且任意Iteration_tail(w,n,l,y)的值y=e，恢复该迹原Nil种子。
Valid(w,n)给实际内部l,y，同时满足l∈w、HasLength(w,n,l)、Iteration_tail(w,n,l,y)、Nil(w,y)。
任意两组实际长度与求值见证满足l=k且y=z。
九个闭句/模式、12个实例均有原nativeZF推导，详见STEP4_INTERNAL_LIST_END_ACCEPTANCE.zh-CN.md。
这些是精确端点对应；全部原迹位置的对应、实际有序字段图及往返仍未实现。
原背景ZF、全内部ω的ProofZF/U和最终Con规格保持不变，完整Con完成标志仍为False。


2026-10-22全部原迹位置对象推导更新：
Positions(w,l,f,n,r):=∀k∀y(((k∈w∧Sum(w,r,k,l))∧edge(f,k,y))→Iteration_tail(w,n,r,y))。
原完整sequence、全部Links和末边下，Ω(w)、r∈w推出Positions。
反向用原完整函数图实际取得k处的值，得Ω、原完整Trace、r,k∈w、Sum(w,r,k,l)下：
edge(f,k,y)↔Iteration_tail(w,n,r,y)，y为任意内部对象。
给原迹任意k∈d，实际证明∃r((r∈w∧Sum(w,r,k,l))∧∀y(edge(f,k,y)↔Iteration_tail(w,n,r,y)))。
原内部自然差的存在前提已由原后继域成员关系与全内部自然差定理消去。
八个闭句/模式、九个实例均有原nativeZF推导；详见STEP4_INTERNAL_LIST_POSITIONS_ACCEPTANCE.zh-CN.md。
全部位置对应完成；实际完整有序head字段图、字段往返和完整语法树解码仍未完成。
最终内部ProofZF/U及Con的对象层规格和完成标志保持不变。


2026-10-22实际完整字段图对象推导更新：
Field(w,n,i,y):=∃t(Iteration_tail(w,n,i,t)∧Step_head(w,t,y))。
Entry(w,n,i,p):=∃y(Field(w,n,i,y)∧Ordered(p,i,y))，Ordered为原Kuratowski纯公式。
Graph(w,n,l,g):=∀p(p∈g↔∃i(i∈l∧Entry(w,n,i,p)))。
Fields(w,n,l,g)包含原完整Sequence(g,l,w)、Graph及∀i∀y(edge(g,i,y)↔(i∈l∧Field(w,n,i,y)))。
Ω(w)、l∈w下，任意内部种子n都有实际唯一完整Fields图；图由原Replacement精确像实际构造。
比较候选图仅要求Graph，未假定其functionOn或值域；这些性质均已证明。

Decoded(w,n):=∃l∃g((l∈w∧HasLength(w,n,l))∧Fields(w,n,l,g))。
Ω(w)下Valid(w,n)↔Decoded(w,n)，且任意两组实际长度/Fields图均有l=k及g=h。
原Cons下实际空索引读取head；实际后继索引读取tail的前驱字段，均为双条件并覆盖全部内部自然索引。
原迹中的Cons head与对应字段读取也有直接的对象双条件。
15个完整闭句有源ZF、sourceZF原核核心及原nativeZF证明，见STEP4_INTERNAL_LIST_FIELDS_ACCEPTANCE.zh-CN.md。
该解码保留实际HasLength构造迹；任意字段序列的逆编码、码唯一性及双向往返仍未完成。
内部专用ProofZF/U和最终Con规格不变，不能由当前图解码或编译通过宣称最终目标完成。


2026-10-22任意内部字段序列逆编码对象推导更新：
Encoding(w,F,L,n):=(n∈w∧HasLength(w,n,L))∧Fields(w,n,L,F)。
Ω(w)、L∈w和原完整sequence(F,L,w)实际推出∃n Encoding(w,F,L,n)。
不预设序列已有编码，也不限制为外部标准长度；F,L,n均为内部集合对象。
后缀匹配Aligned(w,F,k,r,n)量化所有i∈r和q，Sum(w,k,i,q)时Field(w,n,i,y)↔edge(F,q,y)。
固定F,L，对全部内部r作原Separation支持的ω归纳，量化所有自然偏移k且r+k=L，
实际构造HasLength为r且满足Aligned的自然码，再取零偏移全长实例。
源F的原完整functionOn将逐边对应提升为精确Kuratowski图像，证明完整Fields就是给定F。
Encoding实际推出Valid；任意HasLength(w,n,k)、Fields(w,n,k,g)的解码读回均有k=L且g=F。
13个完整闭句有源ZF及原nativeZF推导，见STEP4_INTERNAL_LIST_ENCODE_ACCEPTANCE.zh-CN.md。
这完成任意序列逆编码存在性和编码后图读回；不同候选码的唯一性、解码后原码恢复及完整双向往返仍未完成。
内部专用ProofZF/U、任意内部证明码正确性和最终Con的目标与未完成标志保持不变。


2026-10-22原列表码单射及完整双向往返对象推导更新：
Agree(w,r,a,b):=∀i∀y(i∈r→(Field(w,a,i,y)↔Field(w,b,i,y)))。
Ω(w)、HasLength(w,a,r)、HasLength(w,b,r)和Agree推出a=b，原对象ω归纳覆盖全部内部长度。
任意内部完整ω值序列实际取得唯一Encoding纤维，比较全部候选内部码。
Valid(w,n)下实际取得L,F,a，满足HasLength(w,n,L)、Fields(w,n,L,F)、Encoding(w,F,L,a)及a=n。
这是实际解码再编码的原码恢复；结合上一批编码后解码恢复原长度/图，两个方向均已完成。
十个新增闭句有源ZF及原nativeZF实际Derives；见STEP4_INTERNAL_LIST_ROUNDTRIP_ACCEPTANCE.zh-CN.md。
这些是列表层的关系式往返，尚未交付实际递归语法检查算法及树有效性。
专用ProofZF/U、任意内部证明码正确性、内部编译器及最终内部Con仍未完成；本文件最初锁定的Con展开和背景不变。


2026-10-22全内部递归列表检查对象推导更新：
Terminal(w,b):=Empty(b)∨Nil(w,b)，Occurs(w,n,r)实际量化真实tail递归值。
Before(w,n,r)排除全部更早内部索引上的终端事件，CheckValue保留实际首个索引、完整递归见证和终端值。
定义不引用Valid；严格尾码对象归纳证明全部内部自然码终止，原Foundation/Separation给首个终端存在唯一。
停止前有效性不变量经对象ω归纳闭合，得到接受↔原Valid、拒绝↔¬Valid及完整互斥分类。
每个内部自然码有实际唯一检查值；原Nil/零边界和接受后的实际内部长度/完整图解码也已证明。
十六个新增完整闭句有源ZF及原nativeZF实际Derives；见STEP4_INTERNAL_LIST_CHECK_ACCEPTANCE.zh-CN.md。
列表有效性/解码总门禁现为True，树、专用ProofZF/U、任意内部证明码正确性及最终Con仍为False。
本文件锁定的原背景、内部Con展开、全部六条规则/27逻辑模式及全内部ω量词范围不变。


2026-10-22全内部字段严格界和实际树算子递归图更新：
HasLength(w,n,l)、i∈l和Field(w,n,i,y)下，原对象ω长度归纳实际推出y∈n。
完整Fields图的每条边继承此严格界，组合原Raw载荷界后得到全部子字段严格属于父码。
具体树前段算子Good保留实际自然标签、raw载荷、长度、完整图；H查询只涉及严格较小子码。
该额外显式界已在Shape下证明等价于原Marks；不引用树有效性或宿主判定器。
原对象递归定理的Total/Deterministic义务已实际消去，取得全部内部序数的唯一完整递归图，及真实零/单位标志见证。
四个字段界和十个树算子完整闭句有源ZF及原nativeZF实际Derives，见STEP4_TREE_OPERATOR_RECURSORS_ACCEPTANCE.zh-CN.md。
前段图子码值对齐、完整树接受/拒绝正确性及实际树解码仍待证明。
专用ProofZF/U、任意内部证明码正确性和最终内部Con仍False；最初锁定的原背景、六规则/27逻辑模式及全内部ω量词不变。

2026-10-22全部内部树检查与唯一解码更新：
Eval(w,z,e,n,y):=∃s∃f(Succ(s,n)∧Recursor_Step(w,z,e,f,s)∧edge(f,n,y))，合取结合以源码为准。
每个内部原序数n均实际存在唯一y；任意原序数域d、n∈d及对应实际图f下，edge(f,n,y)↔Eval(w,z,e,n,y)。
保留真实限制历史，局部Good↔存在Shape且每个字段Eval为实际单位。
Empty(z)、Succ(e,z)下，接受Eval(...,e)恰为该递归分支，拒绝Eval(...,z)恰为其否定；输出实际属于ω且为零或单位。
Valid(w,n):=n∈w∧∃z∃e((Empty(z)∧Succ(e,z))∧Eval(w,z,e,n,e))；Invalid同式末值换为z。
二者与任意实际零/单位选择一致，并在所有内部自然码上完整互斥。
Recursive实际存在tag,p,l,f，要求Shape及∀i∀y(edge(f,i,y)→Valid(w,y))。
原ZF证明Recursive↔Valid；DecodedFiber保留上述四个真实见证及所有候选四分量相等的唯一式，且DecodedFiber↔Valid。
这两个双条件量化任意内部候选对象，内部自然性由Shape实际推出，没有外部标准码限制。
20个完整闭句有Source.Derives、sourceZF原核及nativeZF原核证书；实际验收见STEP4_INTERNAL_TREE_CHECK_ACCEPTANCE.zh-CN.md。
此门禁只完成通用结构树；全部11公式构造、bound/free、纯签名membership编号0、捕获规避替换及ProofZF/U仍待做。
对象背景、Con全内部ω量词和最终原核Derives规格不变，最终Con标志仍False。

2026-10-22任意内部字段序列的实际树构造更新：
TreeEncoding(w,tag,l,f,n):=∃p Shape(w,n,tag,p,l,f)。
原ZF证明每个tag∈w、l∈w、完整Sequence(f,l,w)实际存在唯一自然码n；无需假定已存在编码。
该Shape严格保留原raw标签/payload、实际HasLength和原完整Fields图。
Shape四分量唯一性不预设子树Valid，因此任意实际解码均恢复原tag、长度和整个原输入图f。
从实际解码Shape出发，任何同tag/长度/完整字段图的重编码结果等于原码。
对任何TreeEncoding，原核证明Valid(w,n)↔∀i∀y(edge(f,i,y)→Valid(w,y))。
这两个方向都量化全部内部码、全部内部有限长度及所有图边；非标准内部序列未被排除。
8个完整闭句的源ZF及原nativeZF证书、完整验收见STEP4_INTERNAL_TREE_ENCODE_ACCEPTANCE.zh-CN.md。
这些是通用树构造与关系式恢复；全部11构造类型检查、替换内部化、ProofZF/U及Con仍未完成。
