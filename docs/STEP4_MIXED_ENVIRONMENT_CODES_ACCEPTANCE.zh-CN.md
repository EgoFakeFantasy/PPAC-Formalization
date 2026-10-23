# 原数值混合环境、项替换及binder码验收

2026-10-23；分支migration/yesmeta-step3；本批基点a673fd0a70ad3bfcc998d4d4ac06d0725db23b6d。
S3.3a已验收：完整混合项像表现有原自然数列表码的双向实际唯一转换；
混合项替换及binder提升已使用这些数值环境码参数，并取得实际总唯一及准确字段对应。
一般混合公式替换递归、原操作编码/规则检查兼容及最终内部Con仍未完成。

## 固定对象合同

对象语言保持原纯等词/成员语言。背景为原nativeZF完整Collection呈现，
源完整Replacement通过已经证明的对象互导及原核replay接入；未增加对象公理。
最终要求原FirstOrder.Derives nativeZF [] (Con_ZF→Con_target)，target为ZF+PP+ACwo+¬AC。
内部Con规格遍历全部内部ω证明码，保留原六推导规则、27逻辑模式及完整Separation/Collection。
本批实际交付原对象推导；宿主Consistent、语义模型或有限标准码测试不能替代最终主句。
专用ProofZF/U完整AST及最终内部Con尚未交付。

## 原自然列表码的混合环境

实际表f的定义域a是内部自然数；其值为合法目标Term(w,c,d,q)，允许bound/free两类。
项码q属于内部ω，不能误要求q小于目标bound或free变量数。
原完整ω值序列编码StructuralListEncodeExistence实际构造原列表L，无需人为取项码数值上界。

纯列表类型谓词不以图存在为输入：

```
TermList(w,a,c,d,L) :=
  a∈w ∧ Contexts(w,c,d) ∧ (L∈w ∧ HasLength(w,L,a)) ∧
  ∀i ∀q ((i∈a ∧ Field(w,L,i,q)) → Term(w,c,d,q)).
Encoded(w,f,a,c,d,L) := ImageMap(w,f,a,c,d) ∧ Encoding(w,f,a,L).
```

括号按源码的合取结合实现；上述显示只展开数学内容。
c/d目标范围始终显式保留，不从原列表或项码默认推断。
当前TermList支持混合目标项，区别于此前仅纯free OpenTerm的替换列表。

在Ω(w)下，每个ImageMap实际有唯一原列表码，每个纯TermList实际有唯一完整解码图。
输出存在及实际唯一纤维分别与ImageMap/TermList互为精确双条件。
任意原Encoding所得图只要该列表满足纯TermList，就实际为合法混合ImageMap。
所有内部候选都有Edge(f,i,q) ↔ (i∈a ∧ Field(w,L,i,q))。
原长度、原完整Fields、原HasLength和原列表码唯一性均保留；没有宿主数据解码或选择见证。
两张表/两份列表码的实际存在与成对唯一性也已在对象层证明。

## 数值环境下的混合项替换

```
CodedTermSubst(w,R,S,a,b,c,d,n,q) :=
  ∃r ∃s (EncodedPair(w,r,s,a,b,c,d,R,S) ∧
         MixedTerm(w,r,s,a,b,c,d,n,q)).
```

r/s实际图见证在对象量词中，任意同码实际解码图识别相同替换关系。
在Ω下，全部合法源项及混合环境输入都有实际唯一输出，准确源/目标类型及q∈ω均已证明。
存在和实际唯一输出纤维，恰与TermLists(w,a,b,c,d,R,S)∧Term(w,a,b,n)等价。
给定原源变量码BVar/FVar(w,i,n)，精确得到：

```
CodedTermSubst(...) ↔ i∈所选源域 ∧ Field(w,所选原列表,i,q).
```

源类别只选择bound/free环境列表；目标q可为任一类合法项码，不被源类别限制。
该字段律没有要求调用方提供解码图见证。

## 数值binder提升及原字段律

```
CodedBinder(w,R,S,a,b,c,d,A,C,K,H) :=
  ∃r ∃s ∃k ∃h (
    EncodedPair(w,r,s,a,b,c,d,R,S) ∧
    Binder(w,r,s,a,b,c,d,A,C,k,h) ∧
    EncodedPair(w,k,h,A,b,C,d,K,H)).
```

四张实际输入/输出表均是内部存在见证。任意已知有效输入和输出解码图，
都给CodedBinder与原实际表Binder的精确双条件。
对象解码图唯一性先对齐两个输入图，实际Binder唯一性再对齐输出图，原列表码唯一性最终对齐K/H。
因此实际输出码对唯一，不依赖任何图、规范位移图或头码的见证选择。

在Ω下，实际输出存在和唯一输出码对纤维都精确等价：
TermLists(w,a,b,c,d,R,S)∧Succ(A,a)∧Succ(C,c)。
准确输出TermLists(w,A,b,C,d,K,H)，且K/H属于内部ω。
源/目标真实后继范围仍显式保留为输入，不宣称其存在前提已经消去。

给任意实际规范位移U、恒等V及原bvar0头码n，三个原列表字段律为：

- 新零位：z∈A∧Field(w,K,z,q) ↔ q=n。
- 旧bound位：给定j∈a、Succ(i,j)、Field(w,R,j,t)，i∈A∧Field(w,K,i,q) ↔ TermRename(w,U,V,c,d,C,d,t,q)。
- 旧free位：给定j∈b、Field(w,S,j,t)，j∈b∧Field(w,H,j,q) ↔ TermRename(w,U,V,c,d,C,d,t,q)。

域成员守卫显式保留；不把任意原列表字段的域外候选混同于完整图的真边。
两种源类别的项像bound分量均经目标后移；free源索引本身不移动。
此处字段律是数值环境接口，不等同于原证明检查器或一般混合公式递归正确性。

## 原核传输与实际验收

ObjectMixedEnvironment提供45组Sentence/source/sourceZF核/nativeZF核闭句模式。
每组调用本批Source.Derives，再经TheoryTransport.sentence和ZFReplay.replay，
实际返回原YesMetaZFC.Logic.FirstOrder.Derives nativeZF []，没有替代推导核。

| 检查 | 实际结果 |
|---|---|
| 完整验收命令 | C:\Python314\python.exe -X utf8 scripts/verify.py，退出0 |
| 构建 | 901任务，成功 |
| 声明审计 | 10615项；303无公理依赖、10312允许依赖 |
| 警告 | 0 |
| 本批新增 | 21模块、311项显式声明、45个闭句模式 |
| Internal显式声明全覆盖 | 8300项 |
| 核心/native精确足迹 | 新增45对；累计1102对 |
| SHA256独立回读 | 870份，差异0 |
| 九命令及五trust=0入口 | 全部退出0 |
| 七份理论/信任/依赖锁 | 与基点一致 |
| YesMetaZFC固定提交 | 039c8e132cc19671d73a3933c66b4799d2599dd6，依赖工作区干净 |

新增核心证书恰依赖propext、Classical.choice、Quot.sound；native另恰含既定七项原证书。
原choice额外证书范围未扩大；无sorry/admit、新对象公理、宿主数据见证选择或模型前提。
没有修改原依赖、恢复退役反射、运行原OpenAI完整构建/Comparator或推送。
独立回读在忽略目录verification/mixed-environment-readback.json；生成辅助和日志不纳入发布文件。

## 接续工程表

| 单元 | 输入与依赖 | 必须交付的对象推导 | 状态 |
|---|---|---|---|
| S2.1–S2.3 | 原TermList、恒等/转换码 | 原列表全公式free替换、唯一输出、准确输入与11端点律 | 已验收 |
| S2.4/F2.4b.3 | 原substituteFree/weakenFree数值语法 | 原编码对应及原规则5/4任意内部证明码检查兼容 | 待完成 |
| S3.1–S3.2b | 原实际完整项像表及真实后继 | 混合项替换、两表位移、完全内部化唯一binder提升 | 已验收 |
| S3.3a | 原Encoding/Fields、混合ImageMap及Binder | 双向实际唯一环境码、纯类型/字段；数值混合项与binder实际总唯一、精确输入及原字段律 | 本批验收 |
| S3.3b.1 | 原七字段自然cell及本批TermLists | 新混合状态合法性、实际状态码唯一性和有限纯查询/局部11构造AST | 下一步 |
| S3.3b.2 | 新状态、CodedTermSubst、CodedBinder、原子/逻辑构造 | 实际状态算子与全部内部递归，原11构造的一般混合公式替换实际总唯一、准确类型/输入/端点律 | 待完成 |
| S3.4 | 一般混合公式替换及首槽表 | InstantiateTop/AbstractFreeTop，嵌套binder保护及原数值编码对应 | 待完成 |
| 5a | 原六规则/27模式及完整ZF/目标公理 | 专用ProofZF/U纯AST、准确原参数字段及全部内部证明码检查 | 待完成 |
| 5b | 内部源/目标证书转换器 | 全内部编译及检查正确性，覆盖完整Separation/Collection | 待完成 |
| 6 | 内部解释与固定Con | 原FirstOrder.Derives nativeZF [] (Con_ZF→Con_target) | 待完成 |

仅开启本批八项细分门禁。一般捕获规避公式替换、原加强规则兼容、完整FormulaRename验收、
专用检查器、任意内部证明码正确性、最终Con及相对一致性仍为False。
下一步不能直接别名旧RenameState.state：旧legal强制两个IndexMap MapCode。
可以复用原七字段cell编码及纯cell单射，但新legal必须是本批TermLists和目标FormulaCode。
量词查询必须同时传递两个新环境码K/H，并更新bound源/目标范围A/C；不能保持旧free码S不变。
原扩展BasicSetTheory函数项、NatPacket/带头部证明树包装须分别核对。
主agent独占串行Lean/Lake，每批核验准确公式范围、实际原核接口、逐声明依赖及独立哈希。
