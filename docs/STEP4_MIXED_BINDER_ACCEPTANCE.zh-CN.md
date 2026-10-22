# 完全内部化的混合binder提升验收

2026-10-23；分支migration/yesmeta-step3；本批基点f8bfb74d5495e7ea7a1d93ff6831627b7ff852c4。
S3.2b的实际项像表提升已验收：新bound0行、旧bound源索引后移、free源索引保持，
以及两类项像值中的bound分量后移，现已组成全部内部输入上的实际唯一输出表对。
一般混合公式替换、原数值编码/规则检查兼容及最终内部Con仍未完成。

## 固定对象合同

对象语言保持原纯等词/成员语言，背景是原nativeZF完整Collection呈现。
源完整Replacement由既有对象互导和原核replay接入；没有增加对象公理。
最终要求原FirstOrder.Derives nativeZF [] (Con_ZF→Con_target)，target为ZF+PP+ACwo+¬AC。
内部Con规格遍历全部内部ω证明码，保留原六规则、27逻辑模式与完整Separation/Collection。
本批证明在原对象推导接口交付；宿主Consistent、语义模型、有限标准码测试均不替代最终主句。
专用ProofZF/U完整AST及最终Con主句尚未交付。

## 完整头槽扩展表

对已经变换值的完整旧表f:a→Term(w,c,d)和指定合法项码z，定义纯对象关系：

```
PrefixValue(f,a,z,i,q) :=
  (Empty(i) ∧ q=z) ∨ ∃j (j∈a ∧ Succ(i,j) ∧ Edge(f,j,q)).
```

原Replacement实际构造完整新表g，其源域A满足Succ(A,a)。
零位精确取z，旧源索引j精确移动到Succ(j)；项码值本身不做数值后继。
所有内部候选的边关系、零位和后继位都有精确双条件，实际新图存在唯一。
证明使用对象ω零/后继分解、后继单射和原完整函数图单值性；没有非空旧源域假设。
空旧域的合法情况仍由同一实际总性证明覆盖，没有外部标准ω或语法深度限制。

## 实际新头部与两表提升

SyntaxMixedImageHead实际取得空索引z及原BVarCode(w,z,n)，证明其项码n在目标Succ(c)/d下合法。
空集和项码都在对象存在量词内取得，未使用Lean选定的数据见证。

先对旧bound/free两表r/s的每个值实施目标bound后继映射R和free恒等映射S，得中间表g/h。
再在g上插入新源bound0→目标bvar0项码n，并将旧bound源索引后移，得到最终bound表k。
最终free表仍为h，其源索引不变，但其中所有bound项像已经移动。

```
Binder(w,r,s,a,b,c,d,A,C,k,h) :=
  ∃R S z n (
    ShiftMap(w,c,C,R) ∧ IdMap(w,d,S) ∧
    (Empty(z) ∧ BVarCode(w,z,n) ∧ Term(w,C,d,n)) ∧
    ∃g (BothValuePush(w,R,S,c,d,C,d,r,s,a,b,g,h) ∧
        Prefix(w,g,a,C,d,n,A,k))).
```

所有辅助R/S/z/n/g均为对象存在见证。先证明给定实际映射/头码的输出唯一，
再用对象后继图唯一性、恒等图唯一性、空集唯一性及原变量码唯一性对齐全部见证。
因此最终输出表对(k,h)的唯一性不依赖调用方选择任何辅助见证。

在Ω(w)下，实际输出存在和实际唯一表对纤维，都准确等价：

```
ImageMaps(w,r,s,a,b,c,d) ∧ Succ(A,a) ∧ Succ(C,c).
```

输出准确满足ImageMaps(w,k,h,A,b,C,d)。真实后继范围仍显式保留为输入，
本批没有把A/C存在前提已消去作为验收结论。

任意实际规范R/S及实际头码n都精确识别相同内部Binder，字段律为：

- 新零索引z：Edge(k,z,q) ↔ q=n。
- 旧bound行：给定j∈a、Succ(i,j)、Edge(r,j,t)，Edge(k,i,q) ↔ TermRename(w,R,S,c,d,C,d,t,q)。
- 旧free行：给定Edge(s,j,t)，Edge(h,j,q) ↔ TermRename(w,R,S,c,d,C,d,t,q)。

字段律保留真实原变量码、规范映射及相应边前提；没有将这些局部端点律冒充原证明检查器正确性。

## 原核传输与实际验收

ObjectMixedBinder提供30组Sentence/source/sourceZF核/nativeZF核闭句模式。
每组实际调用本批Source.Derives，再经TheoryTransport.sentence和ZFReplay.replay，
返回原YesMetaZFC.Logic.FirstOrder.Derives nativeZF []，没有另建替代内核。

| 检查 | 实际结果 |
|---|---|
| 完整验收命令 | C:\Python314\python.exe -X utf8 scripts/verify.py，退出0 |
| 构建 | 880任务，成功 |
| 声明审计 | 10304项；303无公理依赖、10001允许依赖 |
| 警告 | 0 |
| 本批新增 | 18模块、236项显式声明、30个闭句模式 |
| Internal显式声明全覆盖 | 7989项 |
| 核心/native精确足迹 | 新增30对；累计1057对 |
| SHA256独立回读 | 849份，差异0 |
| 九命令及五trust=0入口 | 全部退出0 |
| 七份理论/信任/依赖锁 | 与基点一致 |
| YesMetaZFC固定提交 | 039c8e132cc19671d73a3933c66b4799d2599dd6，依赖工作区干净 |

新增核心证书恰依赖propext、Classical.choice、Quot.sound；native另恰含既定七项原证书。
原choice额外证书范围未扩大；无sorry/admit、新对象公理、宿主见证数据选择或模型前提。
没有修改原依赖、恢复退役反射、运行原OpenAI完整构建/Comparator或推送。
独立回读位于本地忽略目录verification/mixed-binder-readback.json；生成辅助和日志不纳入发布文件。

## 接续工程表

| 单元 | 输入及依赖 | 必须交付的对象推导 | 状态 |
|---|---|---|---|
| S2.1–S2.3 | 原TermList、实际恒等/转换码 | 全公式free替换唯一输出、准确输入、11端点律及真实恒等binder提升 | 已验收 |
| S2.4/F2.4b.3 | 原substituteFree/weakenFree及数值码 | 精确原编码对应，再接原规则5/4的任意内部证明码检查 | 待完成 |
| S3.1/S3.2a | 两张完整合法项像表 | 混合项唯一输出、两类表逐值变换及实际bound后移图 | 已验收 |
| S3.2b | 实际源/目标后继范围、S3.2a | 完全内部的唯一两表binder提升、新bound0、旧bound索引后移、free源索引保持及精确字段律 | 本批验收 |
| S3.3a | 完整项像表与原列表Encoding/Fields | 混合环境的实际原数值列表码、准确类型/字段/唯一性，及binder提升与这些码的精确对应 | 下一步 |
| S3.3b | S3.3a、真实binder提升、原11构造 | 有限纯AST的一般混合公式替换，全部内部公式码上的实际总唯一、准确类型和11构造端点律 | 待完成 |
| S3.4 | S3.3及实际首槽表 | InstantiateTop/AbstractFreeTop实际总唯一、嵌套binder保护、准确原数值编码对应 | 待完成 |
| 5a | 原六规则/27模式、完整ZF及目标公理 | 专用ProofZF/U纯AST、准确原字段及全部内部证明码检查正确性 | 待完成 |
| 5b | 内部源/目标证书转换器 | 全内部证明码编译及检查正确性，覆盖完整Separation/Collection | 待完成 |
| 6 | 内部解释和固定Con | 原FirstOrder.Derives nativeZF [] (Con_ZF→Con_target) | 待完成 |

仅开启本批七项细分门禁。完整一般捕获规避公式替换、原加强规则兼容、完整FormulaRename验收、
专用检查器、任意内部证明码正确性、最终Con及相对一致性仍为False。
目前交付的是实际项像表层的binder提升，尚未给出它在一般混合FormulaSubst递归中的使用和原数值编码对应。
原模式20/23/25需要InstantiateTop，21/22/24需要AbstractFreeTop，规则3也有相应义务。
下一步应直接使用StructuralListEncodeExistence的完整ω值序列编码，
不能将目标为任意项码的表误当作取值小于目标变量数的IndexMap，也不能复用仅纯free项的TermList类型。
扩展BasicSetTheory函数项、NatPacket和带头部原证明树必须分别核对。
主agent独占串行Lean/Lake，每批核验准确公式范围、原核接口、逐声明依赖和独立哈希。
