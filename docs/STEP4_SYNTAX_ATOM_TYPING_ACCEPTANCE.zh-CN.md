# 原子公式局部类型与唯一解码验收

日期：2026-10-22；分支：migration/yesmeta-step3。
本批基点：64f008447409e3471ffc700301cb24501726db20。
完成关卡4c.a.iii.a；25个闭句模式实际取得原FirstOrder.Derives nativeZF []证书。
其余七种公式构造、全内部上下文类型递归、内部替换、ProofZF/U及最终Con仍未完成。

## 对象合同与背景

语言保持原单排序等词/成员语言；背景是原ZF，不增加AC、不可达、Con前提或新推导核。
数学证明首先为Source.Derives，再经既有TheoryTransport与ZFReplay回放至原YesMetaZFC推导核。
闭句化量化全部自由对象变量，包括内部ω、bound/free长度、索引、字段和候选码。
外部Bool仅索引falsum/truth两个有限公式模式；不对内部码、字段长度或内部自然数作标准性假设。
Fin m仅指定公式变量槽位，不是内部候选取值的有限界。

## 精确原编码

沿用固定SyntaxEncode的原顺序：falsum=leaf(0)，truth=leaf(1)，
membership=node(2,[leaf(关系编号),项左码,项右码])，equal=node(3,[项左码,项右码])。
纯签名唯一关系编号为0；该字段必须是leaf(0)树码，而非内部自然数0。
ZeroScalar(w,s):=Constructor_{0,0}(w,[],s)。原ZF证明ZeroScalar(w,s)↔Num_2(s)。
这是原树数值约定的编码事实，不是对象falsum成立。
若Scalar(w,i,s)，则ZeroScalar(w,s)↔Num_0(i)，因此任意内部非零关系编号均被拒绝。

Ctx(w,b,f):=b∈w∧f∈w；Term沿用前批已证的完整bound/free作用域关系。
MemberTypes(w,b,f,s,x,y):=ZeroScalar(w,s)∧Term(w,b,f,x)∧Term(w,b,f,y)。
EqualTypes(w,b,f,x,y):=Term(w,b,f,x)∧Term(w,b,f,y)。
Membership实际存在s,x,y，保留MemberTypes和原三个字段构造；Equality实际存在x,y，保留相同上下文的项类型和原两字段构造。
两个Nullary模式保留Ctx及原零字段构造，Atomic为这四个分支的析取。

给定实际原构造码，原核分别证明Membership↔MemberTypes、Equality↔EqualTypes，
以及Atomic在相应membership/equal码处的同一类型双条件。
给定任一原零字段常量码，Nullary和Atomic均恰好对应Ctx；falsum分支另有Ctx∧Num_2的无已知码双条件。
所有Atomic码属于内部ω，且保留两侧上下文自然守卫。

## 实际构造与解码

合法Ctx实际构造falsum/truth自然码；给定合法原项x,y，实际构造membership/equal自然码。
ExistsMembership保留给定x,y，仅内部存在根码及唯一编号的scalar码；没有把原输入遗忘为任意项存在。
存在性前件不假定已经有某个原子码。两个相同项输入的合法membership码即使采用不同scalar候选也相等；equal同样唯一。

同码membership恢复s,x,y全部三个字段；同码equal恢复x,y两个字段。
MemberUnique(w,n,s,x,y):=∀s'∀x'∀y'(MemberCode(w,s',x',y',n)→s'=s∧x'=x∧y'=y)。
EqualUnique以两个真实内部全称量词作同样检查。
候选字段不限制在scope内，也不假定是外部标准数。
DecodedMember/DecodedEqual实际存在合法字段，并包含原码、完整项类型及上述唯一性公式。
原核证明Membership↔DecodedMember、Equality↔DecodedEqual；不以宿主存在/唯一命题代替解码纤维。

## 排除性质

原构造标签互斥排除其他原子分支冒充当前membership/equal分支。
已知任意Scalar关系字段时，membership成立恰好要求内部编号满足Num_0，另两字段在同一完整scope内为项。
未知原子标签拒绝句直接量化内部t与payload p：
Ω(w)、t∈w、p∈w、Raw(w,t,p,n)、¬Num_0(t)、¬Num_1(t)、¬Num_2(t)、¬Num_3(t)推出¬Atomic(w,b,f,n)。
这不依赖外部Nat标签界或固定外部字段向量，覆盖内部非标准标签和payload。

## 模块与25个证书模式

| 模块 | 实际职责 |
|---|---|
| SyntaxAtomSyntax / Logic | 精确字段AST、非单射重命名、原exE消去、等词替换 |
| SyntaxZeroScalar | leaf(0)的实际内部数值2，原关系编号0检查 |
| SyntaxAtomTyping / Existence | 同scope项类型双条件、给定合法输入的实际码构造 |
| SyntaxAtomUnique / Decode | 同码字段恢复、码唯一性、真实内部唯一解码纤维及双条件 |
| SyntaxAtomCases / Reject | 四分支、内部ω范围、异标签和未知内部标签排除 |
| ObjectSyntaxAtoms | 25个完整闭句的Source/sourceZF核/nativeZF核证书 |

25个模式：zeroTwo、zeroIndex、nullaryContexts、falseTwo、memberTypes、equalTypes、
nullaryExists、memberExists、equalExists、memberFields、equalFields、memberValueUnique、equalValueUnique、
memberDecode、memberFiber、equalDecode、equalFiber、atomicContexts、atomicRange、nullaryAtomic、
memberAtomic、equalAtomic、symbolCheck、badSymbol、unknownAtomicTag。
CheckStep4另核对原字段顺序、scalar零字段、唯一解码量词及两个常量实例。

## 实际命令和依赖验收

执行：C:/Python314/python.exe -X utf8 scripts/verify.py，最终退出0。
内部九条正式命令均退出0：两个固定源锁检查、Lean版本、全仓wfail构建、
Check/CheckStep2/CheckStep3/CheckStep4/Audit五份lake env lean --trust=0入口。
结果：566个构建任务；5304项声明审计；216项无公理依赖、5088项在原允许依赖内；0警告。
本批10个模块、200项显式声明全部列入审计；Internal累计2989项具名声明覆盖。
累计297对核心/native证书或模式通过精确足迹核验；本批新增25对。
每个新增核心证书恰为propext、Classical.choice、Quot.sound；native端点另继承原七个ZF证书。
Classical.choice在这里是Lean证明基础依赖，没有增加对象AC公理；原choice额外证书仍限域。
535份源码SHA256独立重算，差异0。原19规则、九类源ZF、两份可信基和全部固定依赖锁不改。
YesMetaZFC仍为039c8e132cc19671d73a3933c66b4799d2599dd6，依赖工作区干净。
独立回读保存在本地verification/syntax-atoms-readback.json；日志/哈希/探针不入库。
原OpenAI完整构建与Comparator未运行；本批未推送。

## 下一关与最终缺口

4c.a.iii.b：五个逻辑联结词读取同一(b,f)的真实子式类型状态；
两个量词通过实际Succ(b',b)读取(b',f)，不能继续使用原bound长度。
随后4c.b用实际集合状态递归覆盖全部内部上下文，而不是固定(b,f)的单个树布尔值。
Kuratowski上下文对可由实际P(P(ω))覆盖；每个节点的上下文状态为其子集，位于再取一次幂集所得集合中。
须实际构造载体、局部Separation状态、算子总单值性、递归图和全前段对应，才验收完整公式类型。
捕获规避非单射内部替换、ZF/U全部原规则/模式检查、任意内部证明码正确性、内部编译器和最终Con蕴含均仍待完成。
