# 混合项替换及实际项像表变换验收

2026-10-23；分支migration/yesmeta-step3；本批基点80f532d6b8576ac57e798a555b84cd7522d9c334。
S3.1和S3.2a已验收：混合项替换实际唯一输出；两张完整项像表均可逐值重命名，并实际构造bound后移状态。
完整混合binder提升、混合公式替换、原证明检查连接及最终内部Con仍未完成。

## 固定对象合同

对象语言保持原纯等词/成员语言。背景是原nativeZF完整Collection呈现，
源完整Replacement由已经证明的对象互导和原核replay接入；没有增加对象公理。
最终主句仍要求原FirstOrder.Derives nativeZF [] (Con_ZF→Con_target)，target为ZF+PP+ACwo+¬AC。
内部Con规格遍历全部内部ω证明码，保留原六条推导规则、27个逻辑模式和完整Separation/Collection。
此处没有以宿主Consistent、语义模型或有限标准码测试代替该主句。
专用ProofZF/U完整纯AST及最终Con主句尚未交付。

## 混合项替换的实际对象推导

SyntaxTermImageSyntax定义完整项像表ImageMap(w,f,a,c,d)：
a∈ω，c/d为合法目标范围，f是从全部a到ω的实际完整函数图，且每条边的值都是Term(w,c,d,q)。
两张表r/s分别对应源bound/free变量；其输出都可为合法目标bound或free项。

```
MixedTerm(w,r,s,a,b,c,d,n,q) :=
  ImageMaps(w,r,s,a,b,c,d) ∧
  (∃i∈a (BVarCode(w,i,n) ∧ Edge(r,i,q)) ∨
   ∃i∈b (FVarCode(w,i,n) ∧ Edge(s,i,q))).
```

源类别仅决定查哪张表，不能把输出类别限制成源类别。
在Ω(w)下，所有内部合法输入都有实际唯一输出；存在及实际唯一纤维都与
ImageMaps∧Term(w,a,b,n)互为双条件。输出准确满足Term(w,c,d,q)且q∈ω。
给定源变量码后，判断精确等价源域成员与所选表的真实边。
这些推导不要求目标索引单射，不要求内部ω外部标准，也不把对象见证抽取成Lean数据。

SyntaxTermImageGraph为任意外部纯公式矩阵P、参数映射ρ提供成图模式：
在对象总单值和目标项合法前提下，用原Replacement实际取得完整ImageMap和全部候选边的精确关系。
外部P只索引句子模式；每个实例都有源ZF及原nativeZF闭句推导，没有内部统一真值断言。

## 两类项像均逐值变换

```
Value(w,R,S,c,d,C,D,f,i,q) :=
  ∃t (Edge(f,i,t) ∧ TermRename(w,R,S,c,d,C,D,t,q)).
```

SyntaxTermImagePushGraph用原Replacement实际构造完整新表g，源域保持a，目标范围变为C/D。
新表实际存在唯一；对所有内部候选有Edge(g,i,q)↔Value(...,f,i,q)。
若已知旧表Edge(f,i,t)，则精确有：

```
Edge(g,i,q) ↔ TermRename(w,R,S,c,d,C,D,t,q).
```

旧值t仍是对象码，证明通过对象函数图单值性和等词替换消去中间见证。
SyntaxTermImagePushBoth在对象存在量词中同时构造r/s的新表g/h，
证明两张新表的准确目标类型和给定旧表及目标映射时的成对唯一性。
不能因为某张表来自源free类别就跳过其值中的bound部分。

SyntaxTermImageBoundShift进一步实际构造R:c→Succ(c)的后继映射及S:d→d的恒等映射，
并取得上述两张实际新表。这里只移动目标项中的bound分量；源bound域仍为a。
**尚未加入新源bound0及其0→目标bvar0行，故这还不是完整mixed binder lift。**
当前状态保留实际Succ(C,c)前提，不把目标后继存在作为已消去前提宣称。

## 原核证书与实际验收

ObjectMixedTerm提供21组Sentence/source/sourceZF核/nativeZF核闭句模式。
每组先调用本批Source.Derives，再经TheoryTransport.sentence和ZFReplay.replay，
实际返回原YesMetaZFC.Logic.FirstOrder.Derives nativeZF []，未另建替代推导核。

| 检查 | 实际结果 |
|---|---|
| 完整验收命令 | C:\Python314\python.exe -X utf8 scripts/verify.py，退出0 |
| 构建 | 862任务，成功 |
| 声明审计 | 10068项；294无公理依赖、9774允许依赖 |
| 警告 | 0 |
| 本批新增 | 14模块、188项显式声明、21个闭句模式 |
| Internal显式声明全覆盖 | 7753项 |
| 核心/native精确足迹 | 新增21对；累计1027对 |
| SHA256独立回读 | 831份，差异0 |
| 九命令及五trust=0入口 | 全部退出0 |
| 七份理论/信任/依赖锁 | 与基点一致 |
| YesMetaZFC固定提交 | 039c8e132cc19671d73a3933c66b4799d2599dd6，依赖工作区干净 |

新增核心证书恰依赖propext、Classical.choice、Quot.sound；native另恰含既定七项原证书。
原choice额外证书范围未扩大。无sorry/admit、新对象公理、宿主数据选择或模型前提。
没有修改原依赖、恢复退役反射、运行原OpenAI完整构建/Comparator或推送。
独立回读位于本地忽略目录verification/mixed-term-readback.json；生成辅助及日志不纳入发布文件。

## 接续工程表

| 单元 | 输入及依赖 | 必须交付的对象推导 | 状态 |
|---|---|---|---|
| S2.1–S2.3 | 原TermList、实际IdCode/转换码 | 全公式free替换的唯一输出、准确输入、11端点律和真实恒等binder提升 | 已验收 |
| S2.4/F2.4b.3 | 原substituteFree/weakenFree及数值码 | 精确原编码对应，再接原规则5/4的任意内部证明码检查 | 待完成 |
| S3.1 | 实际两张完整项像表 | 跨bound/free项替换唯一输出、准确类型/输入及已知源码字段律 | 本批验收 |
| S3.2a | 目标重命名与S3.1 | 两表逐值变换的实际唯一图、精确边及实际bound后移状态 | 本批验收 |
| S3.2b | S3.2a和真实源/目标后继域 | 新bound0→目标bvar0；旧bound源索引后移；free源索引保持；两表bound像均后移；实际唯一完整提升 | 下一步 |
| S3.3 | S3.2b、原11构造、全部内部公式码 | 一般混合公式替换实际总唯一、准确类型和全部构造端点律 | 待完成 |
| S3.4 | S3.3及实际首槽表 | InstantiateTop/AbstractFreeTop实际总唯一、嵌套binder保护、准确原字段/数值编码对应 | 待完成 |
| 5a | 原六规则/27模式、完整ZF及目标公理 | 专用ProofZF/U纯AST、全部原字段及任意内部码的检查正确性 | 待完成 |
| 5b | 内部源/目标证书转换器 | 全内部证明码编译及正确性，包含完整Separation/Collection | 待完成 |
| 6 | 内部解释及固定Con | 原FirstOrder.Derives nativeZF [] (Con_ZF→Con_target) | 待完成 |

本批仅开启七个细分门禁；完整捕获规避替换、原加强规则兼容、完整FormulaRename验收、
专用检查器、任意内部证明码正确性、最终Con及相对一致性继续False。
原模式20/23/25需要InstantiateTop，21/22/24需要AbstractFreeTop，规则3也有对应义务。
扩展BasicSetTheory函数项不等同于纯项；NatPacket、原数值字段及带头部树包装必须分别证明兼容。
每批由主agent独占串行Lean/Lake，验收准确公式范围、原核接口、逐声明依赖和独立哈希。
