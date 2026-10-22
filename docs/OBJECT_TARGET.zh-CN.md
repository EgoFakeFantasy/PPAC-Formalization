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

2026-10-22有限语法构造及全部内部变量索引更新：
Num_0(x):=Empty(x)；Num_{k+1}(x):=∃p(Num_k(p)∧Succ(x,p))。
k为外部有限公式索引，每个实例有原核证明；候选x及变量索引i仍为全部内部对象/ω成员。
原ZF证明每个有限数码实际存在唯一，i<j的两个数码满足严格成员关系，不同有限数码互斥。
Forest_k(w,xs,p)保留精确k个原Cons字段及末端原Nil；实际构造唯一并满足HasLength(w,p,l)于Num_k(l)。
Node_k实际存在该payload，保留自然标签和原raw；有限标签Constructor_{k,t}另实际取得Num_t标签见证。
所有构造器有实际唯一原自然码、异标签互斥和每个字段严格子码界。
Scalar(w,i,n):=Node_0(w,i,[],n)，对全部内部自然i存在唯一并在索引上单射。
Var_bound/free(w,i,n)是标签0/1的原单字段节点，其字段必须为Scalar(w,i,s)的实际叶码s。
这两个编码模式在所有内部自然i上实际存在唯一，并证明两类在同一码处互斥。
全部11个公式标签/字段数实例已通过构造存在唯一；类型限制、membership编号0字段和作用域仍待核验。
18个闭句模式的source/sourceZF核/nativeZF核证书和验收见STEP4_SYNTAX_CONSTRUCTORS_ACCEPTANCE.zh-CN.md。
变量码反向索引单射、纯项bound/free检查、全部公式类型、非单射捕获规避替换、ProofZF/U及Con仍未完成。

2026-10-22实际变量反向解码及纯项scope更新：
同一码的精确森林/节点/构造器恢复所有字段；变量的单scalar字段实际恢复唯一内部索引。
Recognized_bound/free(w,n):=∃i Var_bound/free(w,i,n)，原ZF证明其恰为实际唯一自然索引纤维。
该唯一性对所有内部候选j要求Var(w,j,n)→j=i，不只在某个作用域内比较。
Ctx(w,b,f):=b∈w∧f∈w；Branch_mode(w,l,n):=∃i(i∈l∧Var_mode(w,i,n))。
Term(w,b,f,n):=Ctx(w,b,f)∧(Branch_bound(w,b,n)∨Branch_free(w,f,n))。
已知Var_mode(w,i,n)及Ω(w)下，原核证明Term↔(Ctx∧i∈相应的b或f)。
每个合法内部索引实际产生自然项码；Term与实际唯一索引解码双条件成立，bound/free解码分支互斥。
空上下文、错索引域、不同字段数及裸scalar被正式拒绝。
函数标签2的排除量化任意内部自然payload p，不限外部标准字段长度；纯签名确实没有函数项分支。
27个完整闭句模式的Source.Derives/sourceZF核/nativeZF核证书和验收见STEP4_SYNTAX_TERM_SCOPE_ACCEPTANCE.zh-CN.md。
这是纯项关系及其对象正确性；全部11公式局部分支、量词上下文状态、内部替换、ProofZF/U及最终Con仍未完成。
未知标签t本身也为内部对象变量：t∈ω且不满足对象数码0/1时，任意自然payload的raw节点不是纯项；覆盖非标准标签。

2026-10-22原子局部类型更新（4c.a.iii.a）：
原ZeroScalar(w,s)恰为Num_2(s)；给定Scalar(w,i,s)时恰好要求Num_0(i)。
Membership保留关系scalar叶和两个同上下文Term；Equality保留两个同上下文Term。
两个零字段常量保留Ctx；四个Atomic分支有精确已知构造双条件、实际自然码存在和范围。
同输入码唯一，同码恢复所有字段；真实内部全称唯一性不预先限制候选字段的scope。
Membership/Equality恰好对应包含原码、合法类型和所有内部候选唯一性的实际解码纤维。
任意内部自然标签t不满足Num_0/1/2/3时，任意自然payload的raw节点均非Atomic。
25个完整闭句模式均有原Source/sourceZF/nativeZF推导；详见STEP4_SYNTAX_ATOM_TYPING_ACCEPTANCE.zh-CN.md。
下一项是其余七种逻辑/量词局部分支。完整类型递归须保留所有内部(b,f)状态，
量词体在实际Succ(b',b)下读取(b',f)，不能以固定初始bound的树二值递归替代。
ProofZF/U、任意内部证明码正确性、内部替换/编译器及最终Con依旧未完成。

2026-10-22逻辑局部类型及实际上下文载体更新：
Read(h,x,b,f):=∃S(Edge(h,x,S)∧Edge(S,b,f))，S为内部上下文对集合。
历史为实际原函数图时，读取恰好对应其真实输出状态的上下文对成员。
两个量词使用Advanced:=∃k(Succ(k,b)∧Read(h,x,k,f))；原核证明给定真实后继k时恰为Read(h,x,k,f)。
否定及四种二元联结词保持原(b,f)；所有分支保留Ctx、精确原字段及严格子码界。
实际自然码构造、原字段恢复、编码唯一性、真实内部量词解码双条件和缺失状态拒绝均证明。
三层幂集Tower(w,A,C,U)实际存在唯一；b,f∈w的Kuratowski对属于C=P(P(w))，所有状态子集属于U=P(C)。
33个新增完整闭句模式有原Source/sourceZF/nativeZF证书；详见STEP4_SYNTAX_LOGICAL_CONTEXT_ACCEPTANCE.zh-CN.md。
组合局部状态的实际Separation、集合值算子和完整类型递归仍待做。
内部替换、ZF/U专用Proof检查及任意内部码正确性、内部编译器和最终Con依旧未完成。

2026-10-22实际类型状态及原递归更新：
Local组合全部11个原构造；Row(p):=∃b∃f(Ordered(p,b,f)∧Local(w,b,f,h,n))。
State:=∀p(p∈V↔p∈C∧Row(p))由原Separation实际构造唯一，逐对成员恰好对应完整Local。
集合值算子实际总单值，已消去原递归前提，全部内部原序数域上有实际唯一完整递归图。
每个内部自然码有真实后继域状态值，任意前段图边与实际值精确等价；值有实际统一载体界。
Typed(w,C,n,b,f):=n∈w∧Ctx(w,b,f)∧∃V(Evaluation(w,C,n,V)∧Edge(V,b,f))。
给定实际值，Typed恰为其上下文对成员；完整历史自然域内的Read恰为Typed。
35个完整闭句模式均有原Source/sourceZF/nativeZF证书；详见STEP4_ACTUAL_TYPE_STATES_ACCEPTANCE.zh-CN.md。
这完成实际状态存在、递归图与读取对应；完整11构造的历史无关类型递归式和原编码识别正确性仍待证。
完整类型门禁仍False；内部替换、ProofZF/U及任意内部证明码正确性、内部编译器和最终Con均未完成。

2026-10-22全11历史无关类型递归式更新：
Criterion保留n∈w和原11构造精确析取，所有严格子码的Read已等价替换为Typed。
量词体为∃k(Succ(k,b)∧Typed(w,C,child,k,f))，free不变，不冻结父式bound。
原核证明Ω(w)、A=P(w)、C=P(A)下，对全部内部n,b,f有Typed↔Criterion，非自然候选也正式处理。
进一步实际取得ω、A/C/U、完整状态递归和∀n∀b∀f定律，闭句存在证书无额外存在前提。
12个新增完整原核模式及验收见STEP4_HISTORY_FREE_TYPE_RECURSION_ACCEPTANCE.zh-CN.md。
内部bound/free类型递归关卡现True；原编码识别/构造仍待验收，完整类型识别关卡仍False。
内部替换、ZF/U专用Proof及任意内部码正确性、内部编译器和最终Con依旧未完成。


2026-10-22无额外载体FormulaCode和已知原构造类型批次：
对象公式FormulaCode(w,n,b,f)通过内部存在量词取得真实A=P(w)、C=P(A)及Typed。
原ZF证明它与任意真实载体上的Typed等价，且实际ω见证无关。
已消去递归双条件的额外载体前提，在Ω(w)下量化全内部n,b,f；量词体仍是实际后继bound。
全11已知原构造的FormulaCode精确类型双条件及未知任意内部标签的完整拒绝也有原核证书。
候选标签和payload都为内部自然，payload长度没有外部标准界；不只核验宿主标准码样本。
合法输入实际带类型构造、完整字段解码和错码分类还需连接；完整识别总关卡不提升。
背景仍为原ZF纯语言像，原FirstOrder.Derives及内部Con数学定义不变；
没有新增对象AC、Con或不可达前提。内部ProofZF/U、替换、编译器及最终Con仍未完成。
完整验收见STEP4_FORMULA_CODE_CARRIER_ACCEPTANCE.zh-CN.md。


2026-10-22实际带类型构造及接受根完整字段批次：
全11合法内部输入现实际产生带类型原码唯一纤维，保留给定原字段、n∈ω、FormulaCode及对所有原构造候选的唯一性。
membership从两个合法Term实际取得原编号0符号及完整带类型构造纤维。
每个接受码实际解码为唯一标签、payload、内部长度及完整字段图；原根本身可重编码，所有同字段重编码均回到原根并保留类型。
任意实际长度候选由原长度唯一性对应精确字段数；接受根标签/长度的原11精确内部配对分类和所有非匹配Shape拒绝已证明。
这些结果没有外部码深度/长度标准性假定。它们仍不替代递归子字段的完整类型分类及原树有效性证明。
逐位置字段对应、全递归TypedData的完整接受/拒绝以及任意内部捕获规避替换尚待装配；
完整类型识别总关卡、ProofZF/U、全内部证明码正确性和最终Con仍未完成。
对象语言、原ZF背景、原FirstOrder.Derives和原Con的六规则/27模式规格保持不变。


2026-10-22全内部索引位置与字段图类型批次：
原forest与同根真实完整Fields图已对任意内部i,y证明精确图边双条件；
有限数码域的所有内部成员均由对象成员分类覆盖，不假设候选索引外部标准。
实际Slot通过对象存在量词取得索引，精确等价于原字段；任意外部纯公式模式的字段检查有原核双条件。
FormulaCode、Term、真实后继bound的AdvancedCode和原ZeroScalar四个实例已装配；
已知原Constructor下的全部非零元父类型精确等价于同根实际图检查，量词保持实际Succ及原free上下文。
外部矩阵仍是定理模式索引，不引入内部统一真值谓词。
完整TypedData解码/反向识别仍需消去当前已知Constructor前提；原树递归有效性仍需对象ω归纳。
完整类型识别、内部捕获规避替换、ProofZF/U、任意内部证明码正确性及最终Con仍未完成。
对象背景、原核、内部Con的原六规则/27模式和全内部ω范围不变。


2026-10-22原树有效性及TypedData正向解码批次：
原ZF已通过内部ω上的对象成员归纳证明所有FormulaCode均满足原StructuralTree.valid。
归纳性质内部全称量化全部bound/free参数，量词体使用真实后继作用域；归纳由原Foundation及完整Separation关闭。
任意内部scalar/bvar/fvar及完整Term的树有效性、所有实际图边子树有效性和原树实际唯一解码均已证明。
TypedData有限纯公式保留原NodeData、Ctx、11类真实标签/字段数及递归图字段检查。
Code在任意同根Shape上推出TypedData，并实际存在唯一完整TypedFiber；正向终点没有Constructor前提。
失败同根类型数据正式拒绝；反向TypedData→FormulaCode及完整双向识别仍未证明。
Tree.valid比纯语言类型宽，因此不把Code→Tree.valid误写成双条件。
原背景、原核和原Con的全内部ω、六规则/27模式要求不变；
内部替换、ProofZF/U、任意内部证明码正确性、内部编译器和最终Con仍未完成。


2026-10-22完整类型识别更新：
内部公式码的完整11类类型识别及实际唯一TypedData解码现有双向对象推导。
其闭句由ObjectFormulaCodeTypedDecode.native_dataCode/native_dataIff/native_fiberIff等返回原FirstOrder.Derives。
所有内部候选、bound/free上下文、完整图边与真实量词后继均保留；反向不假定已知Constructor。
这完成内部证明检查器的公式识别前提，并没有给出内部rename/替换或ProofZF/U。
上述背景B及Con_T数学定义保持不变；最终Con闭句AST与任意内部证明码正确性、对象Con蕴含仍未交付。
后续工作单元见AGENT_WORKFLOW.zh-CN.md最后的4c.c至6表。


2026-10-22内部项重命名更新：
纯语言项的RenameTerm现有固定纯对象关系，输入为两个实际完整索引映射图和源/目标bound/free长度。
原核已证明所有合法内部输入实际唯一输出、实际唯一类型纤维、源/目标作用域和原变量码的精确图边双条件。
恒等律消费实际对角映射图，不宣称已构造任意映射的量词提升或复合图。
完整公式rename、量词下映射提升、捕获规避替换和ProofZF/U仍未交付；背景B及内部Con规格不变。


2026-10-22实际binder提升更新：
任意对象功能关系现可由原Replacement实际构造成唯一完整Kuratowski图。
原IndexMap的头槽量词提升已在全部内部零/后继域输入上证明总性、唯一性和范围，
并实际联合取得两个后继作用域及唯一完整提升图；原项新/旧bound及free兼容性均有原核闭句。
完整FormulaRename、捕获规避替换、ProofZF/U和最终内部Con仍未交付，背景B及Con定义保持不变。


2026-10-22 映射自然码及状态更新：
完整内部有限索引图已实际唯一编码到原 structural_list_code，自然码可实际唯一恢复完整图和源长度。
目标范围为额外参数，码不决定唯一目标范围。给定真实两个后继作用域，bound 映射码实际唯一提升。
原 Forest(7) 实际编码两个映射码、源/目标 bound/free 四个作用域和目标 FormulaCode；
源码留作未来 recursor 索引。所有字段与状态均在内部 ω 中，实际唯一解码有七个内部量词。
两个实际完整图与目标 FormulaCode 联合产生实际映射码和自然状态，35 个新增完整闭句均返回原 nativeZF Derives。
见 STEP4_MAP_CODE_STATE_ACCEPTANCE.zh-CN.md。
这仍是对象状态表示，不是完整 FormulaRename、内部替换、ProofZF/U 或 Con 公式的正确性。
下一步由原 Separation 构造实际重命名状态算子并接全内部递归，详见流程 F1c 至 F1e。
最终背景、六条规则、27 类模式、完整 Separation/Collection 和全部内部 ω 证明码的 Con 范围保持不变。


2026-10-22 实际重命名状态算子/递归更新：
纯成员 Read 现在实际读取完整历史图的集合值与七字段自然状态码；
全11类矩阵保留同一个原零符号码、实际完整图项重命名、严格子源码和真实 CodedLift，free 自然码不变。
原 Separation 实际构造唯一 ω 状态子集，精确成员判据及同码七字段恢复均有原核推导。
具体算子的 total/deterministic 前提已消去，所有内部原序数上实际存在唯一完整递归图和后继域求值，
自然输入全部覆盖；真实前段边与求值精确等价，实际前缀满足同一个分离方程。
实际 ω、原幂集载体与完整唯一递归族亦联合存在，无存在前提。
42 个新增闭句模式返回真正的原 nativeZF Derives；详见 STEP4_RENAME_OPERATOR_RECURSORS_ACCEPTANCE.zh-CN.md。
这些证明状态集合递归，不证明每个合法公式恰有一个目标码。
完整 RenameFormula 判断、11类不带历史的递归正确性、实际唯一公式输出及后续替换仍是 F1e 及以后目标。
内部 ProofZF/U、任意内部证明码正确性、内部解释和最终 Con 主句的完成状态仍为 False。


2026-10-22 纯对象重命名判断/递归双条件更新：
RenameFormula 使用内部自然码守卫及实际 Evaluation/Contains 的对象存在见证；
原完整序数前段的任意域内 Read 与判断精确等价，子码自然性在对象层恢复。
全11类矩阵已消去历史参数，真实 CodedLift、严格子码、原零符号和不变 free 码保留。
Ω(w) 下对所有内部候选码、映射码、作用域和目标均有判断↔完整递归判据，无实际值/前段存在前提。
两端 FormulaCode 类型保持、八参数内部统一定律及实际 ω/载体/递归族/定律联合存在均有原 nativeZF 闭句。
见 STEP4_RENAME_JUDGMENT_RECURSION_ACCEPTANCE.zh-CN.md。
这不证明合法输入上的实际唯一公式输出；其全内部成员归纳和单构造精确律仍待 F1e.3/F1e.4。
完整重命名、替换、专用 ProofZF/U、内部编译/解释和最终 Con 主句仍未完成。


2026-10-22实际输出合同及空原子进度：Property(w,n) 现为六个内部全称参数 R,S,a,b,c,d 下 Input→实际唯一输出 Fiber。
Earlier 量化全部内部 x∈ω 且 x∈n；不改成外部标准码归纳。
给定实际 CodedLift 的两个后继和输出码唯一，AdvancedRename 精确对齐其提升后的子判断，free参数保持。
给定原子标签0–3可筛选全部11分支。假/真两个空原子实际自重命名并唯一；原核已经证明它们的完整六参数 Property。
这不是任意公式码的 Property 定理；membership/equality 实际输出和七类逻辑推进、归纳关闭尚未完成。
本批17个完整 sourceZF/nativeZF 闭句模式均已通过五个 trust=0 入口和精确公理足迹检查。
详见 STEP4_RENAME_OUTPUT_NULLARY_ACCEPTANCE.zh-CN.md。
背景 B、原六规则/27模式、完整 Separation/Collection、全部内部ω码上的 Con 定义及最终原核目标保持不变。
专用 ProofZF/U、全内部码编译正确性和最终内部 Con 蕴含仍未实现。


2026-10-22四类原子实际输出进度：所有候选解码图现可精确对齐给定真实图。
成员式/等式从实际重命名项和原构造器产生目标码；成员式保留源中同一个原 ZeroScalar 符号码。
原同码字段恢复及项唯一性证明任意内部候选输出相等；两幅图及所有输出项见证均由原 exE 消去。
假/真/成员/等式四类原子均已得到实际 ∃! Fiber，并证明 Ω(w)→Atomic(w,a,b,n)→Property(w,n)。
Property 内部量化全部 R,S,a,b,c,d，且无 Earlier 前提；这是四类基础情形，未证明任意公式码的 Property。
本批25个 Source/sourceZF核/nativeZF核闭句模式均通过五个 trust=0 入口与精确公理足迹审计。
详见 STEP4_RENAME_ATOMIC_OUTPUT_ACCEPTANCE.zh-CN.md。
七类逻辑推进、归纳关闭、完整 FormulaRename、替换、专用 ProofZF/U、全内部编译正确性与最终内部 Con 仍未完成。
背景 B、原规则/模式和全部内部ω证明码上的 Con 定义保持不变。


2026-10-22全内部公式输出进度：七类逻辑实际唯一输出推进已证明，包含真实后继/提升码的两个量词。
Property(w,n)内部量化全部映射码与四个作用域；原Foundation及Property否定矩阵的原Separation关闭内部ω成员归纳。
Earlier合取守卫与原Below蕴含式守卫已用原规则显式转换，不假定外部良基或标准ω。
故所有合法Input实际存在唯一RenameFormula输出；任意内部候选下ExistsOutput↔Input和Fiber↔Input，并有非法输入拒绝。
无Earlier、解码图、载体或历史存在前提；非单射完整图和非标准内部公式码均包含。
40个新增Source/sourceZF核/nativeZF核闭句模式已通过五个trust=0入口和精确公理足迹审计；见STEP4_RENAME_TOTAL_OUTPUT_ACCEPTANCE.zh-CN.md。
精确单构造律、映射恒等/复合、捕获规避Subst、专用ProofZF/U、全内部编译/解释及最终内部Con尚未完成。
背景B、原规则/全模式和全部内部ω证明码上的Con定义保持不变；输出总性不能替代最终Con蕴含。


2026-10-22精确构造接口进度：原11构造的正式RenameFormula端点双条件已取得原核证书。
候选两端字段均由原同码单射对齐；成员式保留ZeroScalar及源/目标符号相等。
规范子判断恢复源FormulaCode和Input，最终端点律无需额外Input、Earlier、载体或历史前提。
逻辑律消去解码图见证；任意实际CodedLift下，两种量词精确等价于正确提升作用域内的体判断，free码/范围保持。
26类新增Source/sourceZF核/nativeZF核闭句均通过五个trust=0入口与精确足迹审计；见STEP4_RENAME_EXACT_FIELDS_ACCEPTANCE.zh-CN.md。
前批全内部实际唯一输出和成员归纳继续有效；映射恒等/复合、捕获规避Subst、ProofZF/U及最终内部Con尚未完成。
背景B、原规则/全模式及全部内部ω证明码上的Con定义保持不变，不以精确构造接口代替最终对象主句。


2026-10-22 恒等进度：原 Replacement 已实际构造完整恒等图，内部自然长度实际取得原自然列表码。
IdCode(w,a,R) 明确把源/目标范围都定为 a，并要求实际 Encoded 图的全边对角性；任意同码实际解码保持对角。
任意真实 CodedLift(w,a,a,R,u,v,L) 在 Ω 与 IdCode 下推出 u=v 及 IdCode(w,u,L)。
四参数 Property 内部量化 R,S,a,b；全 11 原构造推进后，原 Foundation 与 Property 否定矩阵的完整 Separation 关闭归纳。
因此在 Ω 与两个实际恒等码下，所有内部 n,q 满足 RenameFormula(n,q) ↔ (FormulaCode(n) ∧ n=q)。
没有标准 ω、外部良基、有限宿主深度、Earlier、解码图或历史存在前提；量词体使用真实内部后继/提升码，free 参数保持。
16 类新增 Source/sourceZF核/nativeZF核闭句已通过完整脚本、五个 trust=0 及精确足迹审计；见 STEP4_RENAME_IDENTITY_ACCEPTANCE.zh-CN.md。
恒等已完成；复合、完整 FormulaRename、捕获规避 Subst、ProofZF/U、全内部编译/解释和最终内部 Con 仍未完成。
背景 B、原六规则/27 模式、完整 Separation/Collection 及全部内部 ω 证明码上的 Con 定义保持不变。


2026-10-22 复合进度：原 Replacement 已实际构造两幅完整索引图的唯一复合图，全部内部边有精确存在中间值双条件。
CodedCompose 内部量化三幅实际图，保留 a,c,e 三个明确范围及全部原 Encoded 条件；任意实际解码恢复同一 Composed。
在 Ω 下，可复合两个 MapCode 实际取得唯一输出码，实际存在与精确输入判据互为双条件。
给定 bound/free 两组实际 Composed，TermRename 复合精确等价于存在内部中间项码的两阶段关系；六个作用域保持。
允许非单射、空域和内部非标准码；没有宿主选择的中间图、值或项码。
28 类新增 Source/sourceZF核/nativeZF核闭句已通过完整脚本、五个 trust=0 与精确足迹审计；见 STEP4_COMPOSITION_MAP_TERM_ACCEPTANCE.zh-CN.md。
真实 binder 提升与复合相容、公式复合、完整 FormulaRename、捕获规避 Subst、ProofZF/U、内部编译/解释及最终 Con 仍未完成。
背景 B、原六规则/27 模式、完整 Separation/Collection 及全部内部 ω 证明码上的 Con 定义不变。


2026-10-22 提升复合进度：真实 binder 提升与实际完整图、原自然码的复合相容，均取得任意候选的识别双条件。
零/后继点实际构造中间后继；原完整同域函数图相等取得完整 Composed 及全内部边双条件。
给定原 CodedCompose 和两个输入提升，任意输出候选 Lk 满足 CodedLift(K,Lk) ↔ CodedCompose(Lr,Lt,Lk)，原作用域全部显式保留。
独立中间后继 C,D 由原 Insert 唯一性证明相等，原等词替换对齐第二提升的源范围；不从列表码推断独立目标范围。
17 类新增 Source/sourceZF核/nativeZF核闭句已通过完整脚本、五个 trust=0 与精确足迹审计；见 STEP4_BINDER_COMPOSITION_ACCEPTANCE.zh-CN.md。
下一步全内部公式复合的 Property 必须内部量化六个映射码、六个作用域以及 q,v，原 Foundation/Separation 关闭成员归纳。
公式复合、原核加强规则兼容、完整 FormulaRename、捕获规避 Subst、ProofZF/U、内部编译/解释和最终 Con 仍未完成。
背景 B、原六规则/27 模式、完整 Separation/Collection 及全部内部 ω 证明码上的 Con 规格不变。


2026-10-22 全公式复合进度：原Foundation与完整Separation已关闭14内部参数Property的成员归纳。
六个映射码、六个作用域和中间/最终公式码q,v均在对象全称量化内；全11构造复合推进已证明。
给定两组实际CodedCompose，RenameFormula复合精确等价于存在内部中间公式码的两阶段判断，最终无Earlier前提。
实际目标字段由对象存在量词取得，量词体用真实中间后继对齐及复合bound码提升；free码和范围保持。
35类新增Source/sourceZF核/nativeZF核闭句通过完整脚本、五个trust=0及精确足迹审计；见STEP4_FORMULA_COMPOSITION_ACCEPTANCE.zh-CN.md。
原核free_strengthening是删除未用fresh free头槽；下一步用b→Succ(b)的实际free位移图/码刻画其weakenFree前提链接，含空free上下文。
恒等与复合联合门禁已完成；原核加强规则兼容、完整FormulaRename总门禁、捕获规避Subst、ProofZF/U、内部编译/解释及最终Con仍未完成。
背景B、原六规则/27模式、完整Separation/Collection及全部内部ω证明码上的Con规格不变。


2026-10-22 原free头槽位移进度：实际完整图i↦Succ(i)和原自然列表码已在原ZF对象核中构造。
全部内部候选的边双条件、实际图码唯一纤维、任意实际解码识别和合法输入双条件均已证明。
给定Ω及b∈ω实际取得后继B及唯一位移码，不残留后继存在前提；fresh零槽无入边且空源域实际图为空。
Ω及Empty也直接给空上下文的实际后继/唯一码状态，未加非空上下文限制。
23类Source/sourceZF核/nativeZF核闭句通过完整脚本、五个trust=0及精确足迹审计；见STEP4_FREE_SHIFT_ACCEPTANCE.zh-CN.md。
F2.4a完成；纯WeakenFree全公式定律与原加强规则兼容仍待完成，完整FormulaRename总门禁继续False。
捕获规避Subst、ProofZF/U、内部编译/解释及最终Con仍未完成；背景B、原六规则/27模式、全Separation/Collection和全内部ω量化不变。


2026-10-22全内部公式弱化进度：WeakenFree内部存在量化bound恒等码和free位移码，
从所有合法FormulaCode实际取得唯一输出；存在/唯一纤维与FormulaCode及实际后继输入精确等价。
全11构造的已知端点双条件和真实binder提升已证明，逻辑律不再要求调用方提供映射码见证。
30个新增Source/sourceZF核/nativeZF核对象闭句已完整验收，见STEP4_FORMULA_WEAKENING_ACCEPTANCE.zh-CN.md。
原weakenFree编码对应、原六规则检查器中的全内部free_strengthening兼容、捕获规避替换、ProofZF/U、
全内部编译/解释及最终Con仍未完成；没有据此改变固定背景、原六规则/27模式或全部内部ω量化范围。


2026-10-22替换参数对象进度：纯OpenTerm在实际空bound域下精确等价实际fvar分支。
原term-code列表与实际完整索引MapCode已全内部双向存在唯一，实际唯一纤维和接受输入互为双条件。
任意实际MapCode解码图的索引边，精确等价源域成员关系与原列表真实字段对应；原参数格式和独立目标范围保留。
33个Source/sourceZF核/nativeZF核闭句通过完整验收，见STEP4_FREE_SUBSTITUTION_CODEC_ACCEPTANCE.zh-CN.md。
全公式free替换、原free_substitution规则检查兼容、跨bound/free替换、专用ProofZF/U和最终Con仍未完成。
原六规则/27模式、完整Separation/Collection、固定纯语言以及全部内部ω证明码量化没有改变。


2026-10-22原列表参数全公式free替换进度：纯对象FormulaFreeSubst内部绑定实际IdCode和CodeConversion，
在全部内部合法FormulaCode/TermList输入上实际取得唯一输出，准确类型及存在/唯一纤维输入双条件已证明。
全11构造端点律、bound保持及free目标码为原列表实际字段的双条件均已证明；
量词使用真实bound恒等提升并保持同一原free列表，逻辑码见证在对象量词内取得和消去。
25个Source/sourceZF核/nativeZF核闭句通过完整验收，见STEP4_FORMULA_FREE_SUBSTITUTION_ACCEPTANCE.zh-CN.md。
原substituteFree/weakenFree编码对应及规则检查兼容、一般混合bound/free替换、ProofZF/U和最终Con仍未完成。
当前纯free项像不含bound变量，不能代替InstantiateTop/AbstractFreeTop；背景和全部内部ω量化不变。


2026-10-23混合项进度：完整项像表中的两类源变量均允许任意合法目标bound/free项。
混合项实际总唯一、准确类型/输入及已知源码字段双条件已在原核交付。
原Replacement实际构造任意总单值且目标合法关系的完整项像表；逐值目标重命名亦有实际唯一新表。
旧bound/free两表均经过变换；实际后继bound/free恒等映射给出两表后移状态。
此状态仍保持旧源bound域，尚无新的源bound0→目标bvar0行，不能宣称完整mixed binder lift。
21组Source/sourceZF核/nativeZF核闭句通过完整验收，见STEP4_MIXED_TERM_IMAGES_ACCEPTANCE.zh-CN.md。
后续必须补齐fresh行、旧bound源索引后移、混合公式递归及InstantiateTop/AbstractFreeTop。
原编码与原规则检查兼容、专用ProofZF/U、全内部编译/解释及最终Con保持未完成；全部内部ω量化和固定背景不变。


2026-10-23混合binder进度：新源bound0行及旧bound源索引后移已在原对象核实现。
原Replacement实际构造完整prefix表，两个旧源类别的项像bound部分都经过目标后移。
目标位移/恒等图、空索引、原bvar0码及中间表均为对象存在见证；规范见证在原核内唯一并对齐。
最终两表实际存在唯一，存在及唯一纤维均与完整旧表及真实后继范围精确等价。
准确目标类型、新零位/旧bound位/旧free位字段双条件均已证明；30组原核闭句通过完整验收。
见STEP4_MIXED_BINDER_ACCEPTANCE.zh-CN.md。当前只交付实际项像表层binder提升，
一般混合公式替换的纯AST、数值环境码和原编码对应、InstantiateTop/AbstractFreeTop仍待完成。
原六规则/27模式及全部内部ω上的检查/编译/解释和最终内部Con保持未完成；背景未改变。
