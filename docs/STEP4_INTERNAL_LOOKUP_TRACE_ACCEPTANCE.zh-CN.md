# 任意内部lookup轨迹的对象推导验收

2026-10-23；S3.4c.2b.2c.3c.1b.2b.2；基点16c3136bc9c4fc8022cbe0bee2ab138c0ebdc374。

本批对完整原Horn规则表的关系式编译，完成任意内部闭合轨迹的可靠性、实际规范轨迹构造及完备性；原S(row)搜索和实际P(ω)域均有双向桥接。21模块207显式声明、25组新闭句先在Source.Derives证明，再经TheoryTransport／ZFReplay取得原FirstOrder.Derives nativeZF []。

对象语言仍为纯成员／等词；背景原nativeZF完整Collection。最终目标Con_ZF → Con_(ZF+PP+ACwo+¬AC)不变，内部Con保持全部内部ω证明码、原Hilbert六规则／27模式及完整Separation/Collection。本批不证明最终Con蕴含。

## 原量化应用与任意轨迹可靠性

HornLookupRowSyntax定义Row(w,n,i,y,r)=原Constructor(3,0,[n,i,y],r)。原ZF实际取得行码；原字段单射对齐任意同根行的三个运行时值，字段和行码自然性由原构造器推出。

HornLookupHeadSound实际取得Cons与零索引，以原head矩阵和字段单射对齐当前表码、索引和输出，再返回真实查找执行。HornLookupTailSound实际取得Cons、后继索引和轨迹子行；Cons.components给出tail∈table，在此严格界上使用对象归纳假设，随后等词对齐输出并重建后继执行。原arity存在块由锁定源ex规则实际消去，未从宿主Prop选取运行值；未访问尾部非法但零索引成功的行为仍保留。

```text
Closed(w,R) := ∀r (r∈R → OriginalCompiledStep(w,r,R))
Property(w,R,n) := ∀i ∀y ∀r
  ((Row(w,n,i,y,r) ∧ r∈R) → Executed(w,n,i,y)).
```

HornLookupSoundInduction在原Foundation与Separation中按表码成员关系归纳，性质内部量化全部索引、输出及行码。完整原表tag0分派穷尽头／尾情况，tail∈table排除内部循环。得到Omega(w)、Closed(w,R)、Row(w,n,i,y,r)、r∈R ⊢ Executed(w,n,i,y)。可靠性本身甚至不需要R⊆ω；不假设外部有限轨迹、外部标准自然数或外部良基。

## 实际规范轨迹及完备性

```text
GoodRow(w,r) := ∃n ∃i ∃y
  (Row(w,n,i,y,r) ∧ Executed(w,n,i,y))
Value(w,R) := ∀r (r∈R ↔ (r∈w ∧ GoodRow(w,r))).
```

原Separation实际取得R及R⊆w，每个真实成功行属于R。头步构造真实原head规则应用；尾步实际取得子行码、证明其属于同一R，再构造真实原tail规则应用。由GoodRow全部内部见证，证明R每个成员满足完整原表步骤，从而Closed(w,R)。R可以在对象意义下无限，原ObjectTrace的幂集域允许任意ω子集。

GoodRow用已证明执行构造完备性见证，独立轨迹条件的执行定义不调用旧查找规格或执行作oracle。没有以规范轨迹的定义代替任意轨迹可靠性。

```text
Trace(w,r) := ∃R (R⊆w ∧ r∈R ∧ Closed(w,R))
Omega(w), Row(w,n,i,y,r) ⊢ Trace(w,r) ↔ Executed(w,n,i,y).
```

## 原有界搜索、实际幂集与成功图

HornLookupSearchCondition在R⊆ω下逐成员调用原S(row)搜索桥，证明应用闭合与实际有界搜索闭合等价，相应轨迹条件也等价。HornLookupPowerCondition实际取得P满足PowerOf(P,w)，证明R∈P ↔ R⊆w，因此实际P(ω)域与子集形式完全对应；未假设已选好的宿主幂集值。

```text
Returned(w,n,i,y) := ∃r (Row(w,n,i,y,r) ∧ BoundedSearchTrace(w,r))
HasOutput(w,n,i) := ∃y Returned(w,n,i,y)
NoOutput(w,n,i) := ¬HasOutput(w,n,i).
```

HornLookupSome对任意内部n/i/y证明Returned iff Executed iff CheckedStrictLookup，不要求预给外部行码或标准输入。反向由执行的自然参数实际构造行码和轨迹。HasOutput／NoOutput与原表码程序精确对应；自然表码与索引守卫下，又对应既有严格查找的HasOutput／Rejected及Returned；所有内部成功输出单值。这里给出成功图与无输出公式，没有新造Option数字封包，也未用排中穷尽性代替轨迹正确性。

## 实际验收

1322构建任务、14415项审计（369无公理／14046允许依赖）、零警告；九命令及五trust=0入口全部退出0；1186份工作区独立哈希一致、1566对精确证书足迹、12071项Internal显式声明覆盖。新增25对证书严格等于std3核心／std3加原七证书依赖；Choice桥、七锁、固定YesMetaZFC提交039c8e132cc19671d73a3933c66b4799d2599dd6及干净依赖状态不变。

新增13个执行定义的直接宿主／旧查找引用禁用检查，覆盖行、闭合／轨迹条件、成功图、无输出和幂集域；保留此前所有核心检查。规范轨迹见证和正确性证明可引用已验收执行，执行定义不能把它当oracle。

实际执行LEAN_NUM_THREADS=1、lake --wfail build PPAC.Migration.Internal.ObjectLookupTrace，再运行C:/Python314/python.exe -X utf8 scripts/verify.py。九命令及退出码见本地verification/commands.json；独立复核见本地verification/lookup-trace-readback.json。未运行OpenAI原仓完整构建或Comparator。

## 总目标边界

完成的是直接读取完整原Rule/Expr AST得到的纯关系式编译及全部内部轨迹接口。原扩展语言公式整体的函数图消去／quotation总桥尚未完成，因此object_original_lookup_full_trace_condition_and_numeric_interface_proved仍为false；本批八个细门单独为true。工程表把已完成关系式轨迹与未完成原扩展语言总桥分列，未提前通过原数值接口总门。

随后仍需原boundValue/freeValue及十一公式模式0／3、原规则5／4检查兼容、专用ProofZF/U、全部内部ω证明检查／编译、完整L／对称扩张内部解释，最后原nativeZF中的内部Con蕴含。背景、量词及全部原公理模式没有缩减。
