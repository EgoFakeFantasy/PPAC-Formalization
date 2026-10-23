# 原App与纯成员原子结构连接验收

基点：c9286dbaf779fd43877959d6ec0a686ac69158c8。完成S3.4c.2b.2c.3c.2c.2b.3f.1：原关系应用与纯成员码固定编号0及实际两个参数的对象层连接。完整公式归纳及最终Con仍未证明。

## 对象合同

保持YesMetaZFC原纯等词／成员语言、原nativeZF完整Collection和原FirstOrder.Derives。最终目标仍为Derives nativeZF [] (Con_ZF → Con_target)，target=ZF+PP+ACwo+¬AC；内部Con要求全部内部ω证明码、原六规则／27模式、完整Separation／Collection。没有引入对象AC、标准ω、外部良基、新推导核或退役反射。

静态自然数k及有限字段索引只用来构造每个对象句子实例。全部符号编号、树码、参数森林码及中间载荷都是对象变量或对象存在见证，不抽取宿主集合选择数据。八组闭句均有实际Source推导，经TheoryTransport.sentence及ZFReplay.replay回放原核。

## 一般App与首字段构造

OriginalFormulaApplicationNodes.application_iff_constructor在Omega(w)、Scalar(w,symbol,s)和Forest_k(w,xs,args)守卫下，证明任意内部候选n满足：

```text
App(w,symbol,args,n) ↔ Ctor_(k+1),2(w,[s;xs],n).
```

正向消去App的三对象存在，将实际符号树码与给定s用原节点唯一性对齐，再合成首字段Cons森林及标签2节点。反向消去真实构造器的标签、载荷及森林尾见证，用原森林唯一性将实际尾与args对齐并重建App。所有量词在对象推导内消去。

OriginalFormulaApplicationRecover.recover_application还证明反向字段恢复：在Omega、args∈w、已知首字段为s及尾向量为xs的标签2构造码处，实际App推出Scalar(w,symbol,s)及Forest_k(w,xs,args)。证明使用原Raw节点载荷单射、实际Cons单射及森林输出等词传输，而不把同输入编码唯一性误当作字段解码。

## 纯成员的精确接口

这里的纯成员码是Ctor₃,2(w,[s,x,y],n)，并有ZeroScalar(w,s)。关系编号是内部Num0；它的零字段树码s等价于内部Num2，两者不能混淆。

OriginalFormulaMemberApplication.scalar_at_zero从Num0(z)和ZeroScalar(w,s)正式取得Scalar(w,z,s)。在真实两参数森林Forest₂(w,[x,y],args)处，App(w,z,args,n)与MemberCode(w,s,x,y,n)双向对应。

在已知MemberCode和ZeroScalar处，精确的无外部参数自然性前提的checked接口是：

```text
(args∈w ∧ App(w,symbol,args,n))
  ↔ (Num0(symbol) ∧ Forest₂(w,[x,y],args)).
```

单独对App取双条件的接口保留args∈w作为显式前提；没有声称任意非法参数的App已经被排除。checked反向从真实森林推出自然性。正向由反向字段恢复及已验收SyntaxZeroScalar.index_iff取得实际编号Num0。

## 接入真实原applicationCase

OriginalFormulaMemberCaseSyntax.membershipCase是以下三个内部存在量词，所有子运行仍使用原完整规则表：

```text
∃zero ∃args ∃newArgs
  Num0(zero) ∧
  (Forest₂(w,[x,y],args) ∧
   (App(w,zero,newArgs,q) ∧ Run₂(w,mode,depth,parameter,args,newArgs))).
```

在Omega、ZeroScalar(w,s)和MemberCode(w,s,x,y,n)下，OriginalFormulaMemberCase.case_iff证明原applicationCase(w,mode,depth,parameter,n,q)恰好等价于该内部成员分支。没有额外给定args∈w：正向由真实原Run₂子运行推导其输入自然性，反向从Num0及实际源森林重建源App，保留原输出App和同一真实Run₂。mode、depth及parameter均可为任意内部对象；这里不预设模式0／3或有类型公式。

## 文件与闭句

| 模块 | 对象产物 |
|---|---|
| OriginalFormulaApplicationNodes | 任意固定有限字段数的App与首字段节点双条件 |
| OriginalFormulaApplicationRecover | 实际Raw／Cons单射恢复符号树码及完整参数森林 |
| OriginalFormulaMemberApplication | 编号0／树码2区别、纯成员App双条件及checked接口 |
| OriginalFormulaMemberCaseSyntax | 内部Num0／两参数森林／输出App／真实Run₂分支 |
| OriginalFormulaMemberCase | 原applicationCase与该成员分支双向对应 |
| ObjectOriginalMemberApplication | 八组Source→TheoryTransport→ZFReplay原核闭句 |

八组闭句族：

- originalAppHeadForestConstructorIff
- originalAppHeadForestRecovered
- originalMemberScalarAtZeroIndex
- originalMemberAtTwoArgumentForestIff
- originalMemberAppZeroAndTwoArgumentsRecovered
- originalMemberAppAtNaturalArgumentsIff
- originalMemberCheckedAppIff
- originalMemberApplicationCaseIff

## 实际验收

定向lake --wfail build PPAC.Migration.Internal.ObjectOriginalMemberApplication及C:/Python314/python.exe -X utf8 scripts/verify.py均实际退出0。全仓1444构建任务；15777项声明审计（380无公理／15397允许依赖）；零警告。九命令及五个--trust=0入口全部退出0。Lean/Lake严格串行，LEAN_NUM_THREADS=1。

新增6模块55显式声明，8组核心证书精确依赖propext、Classical.choice、Quot.sound，native精确为标准三项加原七固定句子语法证书。1756对精确证书足迹、13433项Internal显式声明覆盖、1308份工作区独立哈希无差异。七锁及固定底座039c8e132cc19671d73a3933c66b4799d2599dd6干净状态不变，隔离Choice桥未修改。

此前45个执行／分支定义及两个独立字段像定义的直接oracle检查保留；纯公式定义检查由十五项扩至十七项，新增成员body／membershipCase。该定义不调用宿主eval、旧变换结果或独立完整公式程序作为答案原语。全部源码无sorry／admit等禁止缺口。

日志及独立证据保留本地verification/commands.json、audit.log、member-application-readback.json；没有推送或PR，没有运行OpenAI全仓／Comparator。

## 下一门与边界

一般App首字段／森林双条件、纯成员固定编号0／两参数森林双条件、原纯成员applicationCase精确双条件三个细门通过。原Run₃整体方程和参数列表全部内部字段对应保持已验收。

下一步将真实两参数Run₂接入已验收的全内部字段像对应，连接完整原子与连接词情况。随后要在对象公式中量化所有变化运行参数，以原Separation／Foundation关闭完整公式成员归纳，并证明实际量词环境／像列表提升，取得完整有类型公式程序双条件及实际输出性质。

完整公式内部归纳、有类型原公式与独立公式程序总桥、原扩展语言quotation总桥、完整数值Option接口、ProofZF/U检查／编译、内部解释及最终Con均未完成。当前App／原子编码接口与全仓构建不能替代这些终点。
