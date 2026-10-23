# 按表码递归的固定查找程序验收

2026-10-23；S3.4c.2b.2c.3c.1b.1；基点76de048470dca947133071cb0032a71cb6b20db8。

本批完成独立两分支查找程序、原ZF中实际状态集合／递归图／求值的构造、所有内部运行时候选的正确性，以及固定程序描述的唯一数值码和统一对象句子。28模块265显式声明、19组新闭句先有Source.Derives，再经TheoryTransport与ZFReplay返回原FirstOrder.Derives nativeZF []。

对象语言仍为纯等词／成员；背景原nativeZF含完整Collection。最终目标仍是Con_ZF → Con_(ZF+PP+ACwo+¬AC)。内部Con保留全部内部ω证明码、原六规则／27模式及完整Separation/Collection，没有改成外部标准自然数范围。

## 独立执行与原推导

固定DSL含returnHead、recurseTail两个指令；lookupProgram为两分支并集。returnHead匹配零索引和实际Cons head；recurseTail匹配实际Cons tail、自然前驱j及successor(i,j)，从实际历史图在tail处读取状态(i,y)。执行定义不调用旧StrictLookup、默认field或宿主SyntaxTransform.lookup；五个核心模块有直接引用禁用检查，对照证明可引用旧规格。此前八个公式核心及严格查找核心的检查仍保留。

状态(i,y)用原数值Gödel pair编码，显式要求i/y/p属于内部ω。原Separation在ω中实际构造任意历史的状态集合；Extensionality证明单值，Power Set提供集合值载体；原序数递归实际取得所有原序数域的图。后继域求值在每个内部自然表码n上存在唯一，历史边与子表实际执行精确对应。

程序递归按表码n进行。实际Cons的tail∈n给出严格下降界；原Foundation／Separation的集合内成员归纳，性质内全称量化索引i及候选输出y，闭合全部内部n/i/y的对应：

```text
Omega(w) ⊢ Executed(w,n,i,y) ↔ CheckedStrictLookup(w,n,i,y)
Omega(w), n∈w, i∈w ⊢ Executed(w,n,i,y) ↔ Returned(w,n,i,y).
```

候选y不加外部数值、有限深度或标准性假设。表码／索引守卫明确保留；不会错误声称原未加类型守卫的宿主操作对任意集合输入有同一行为。零索引直接返回当前Cons head，不检查未访问尾部合法性；因此保留上游lookup对非法未访问尾部仍可能成功的行为。

## 固定码、统一句子与分支

programTree将固定有限DSL描述映到原树编码；原quotation的存在／唯一性实际取得P∈ω。在同一个对象句子内证明：

```text
∃P (P∈w ∧ Code(P) ∧ (∀n ∀i ∀y
  ((Code(P) ∧ Executed(w,n,i,y)) ↔ CheckedStrictLookup(w,n,i,y)))
  ∧ ∀Q (Code(Q) → Q=P)).
```

P是固定程序描述码；运行时使用这一固定程序的关系式编译。没有实现任意内部程序码的解码执行器或通用编译器正确性。

HasOutput=∃y Executed，NoOutput=¬HasOutput。自然表码和索引下分别等价于此前严格查找的HasOutput／Rejected；全部输入上的两分支穷尽且互斥，每个成功输入输出唯一。这里以成功图与无输出公式表达Option分支，没有自造Option数值封包。排中得到的穷尽性本身不替代上游可执行检查器的正确性。

## 实际验收

1241构建任务、13943项审计（365无公理／13578允许依赖）、零警告；九命令与五trust=0入口退出0；1139份工作区独立哈希一致、1511对精确证书足迹、11599项Internal显式声明覆盖。新增19对证书全部严格等于std3核心／std3加原七证书依赖；Choice桥单独审计，七个锁文件、固定YesMetaZFC提交039c8e132cc19671d73a3933c66b4799d2599dd6及其干净工作区不变。所有显式声明进入Audit，新闭句进入CheckStep4；无sorry/admit、新对象公理或新推导核。

执行命令：LEAN_NUM_THREADS=1、lake --wfail build PPAC.Migration.Internal.ObjectLookupTableProgram；随后C:/Python314/python.exe -X utf8 scripts/verify.py。完整九条命令及退出码见本地verification/commands.json；独立复核见本地verification/lookup-table-readback.json。上述统计来自本批实际运行；未运行OpenAI原仓完整构建或Comparator。

## 下一验收门

3c.1b.2仍须把上游实际SyntaxTransform／ObjectSyntaxTransform的规则表与数字接口接到上述内部成功图，包括严格失败分支，证明所需quotation／编译对应。上游lookupHead、lookupTail的已读定义与本程序分支形状一致，但宿主层lookup_accept／checked_iff不能代替全内部原ZF推导。

随后依次是boundValue/freeValue模式0／3、十一构造器公式与binder深度+1、原规则5／4检查兼容（不添加FreeClosed）、专用ProofZF/U及全内部检查／编译、完整L与对称扩张解释，最后原nativeZF内的内部Con蕴含。所有这些总门保持未完成。
