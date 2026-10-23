# 原有界赋值与完整查找分派验收

2026-10-23；S3.4c.2b.2c.3c.1b.2b.1；基点413b7fd6a6fa3e8ce88a4be8b8200202a185fad8。

本批把原Rule的全部arity个赋值实际放进对象存在量词，证明原S(row)搜索界及完整原规则表在tag0行上的精确lookup分派。12模块124显式声明、13组新闭句均先有Source.Derives，再经TheoryTransport／ZFReplay取得原FirstOrder.Derives nativeZF []。

对象语言仍为纯成员／等词；背景原nativeZF完整Collection。最终目标仍为Con_ZF → Con_(ZF+PP+ACwo+¬AC)，内部Con保持全部内部ω证明码、原Hilbert六规则／27模式和完整Separation/Collection。本批处理的Horn规则表与该Hilbert合同分开，未改写任何一个原推导核。

## 所有赋值由对象量词取得

HornBinderSyntax为任意固定有限arity定义末槽存在块、旧变量与赋值槽嵌入、提升及实际赋值代入。HornBinderRules由原锁定源规则证明整块存在引入／消去及ZF上下文传输，允许赋值把不同槽映到同一对象；没有增加结构规则或从宿主Prop抽取运行数据。

HornApplicationSyntax直接读取原Rule.arity、head／guards／premises，定义：

```text
Application(rule,w,row,R) := ∃env_0 ... ∃env_(arity-1)
  (EnvNat(w,env) ∧ EnvBound(row,env) ∧ CompiledMatrix(rule,w,row,R,env)).
EnvBound(row,env) := ∧j (env_j=row ∨ env_j∈row).
```

arity是固定原规则的有限模式索引；每个赋值都是无外部数值限制的内部对象量词。证明从有限合取逐个推出自然性：Omega(w)、row∈w及EnvBound即可推出EnvNat。因此在原数字行范围内，自然守卫是原搜索界的后果，没有给原规则加独立自然前提。

## 原S(row)搜索界及完整原表

HornApplicationBounds用原对象后继关系证明：

```text
Successor(s,row) ⊢ EnvBound(row,env) ↔ ∧j env_j∈s
Omega(w), row∈w, Successor(s,row)
  ⊢ Application(rule,w,row,R) ↔ BoundedAt(rule,w,row,R,s).
```

BoundedAt在同一个实际有限存在块内量化全部原赋值，只保留原后继集合的成员约束与原关系式矩阵。存在块双条件逐个用原ex规则提升，未用模型语义／完备性转回推导。

HornSearchRules进一步用原Pairing／Union实际构造s，然后对整个实际原规则表证明：

```text
Omega(w), row∈w ⊢ Step(rules,w,row,R) ↔
  ∃s (Successor(s,row) ∧ BoundedStep(rules,w,row,R,s)).
```

没有把S(row)当作已选取的宿主函数值。rule／rules仅索引固定原有限表，运行时行码、轨迹和赋值仍全部内部化。

## 完整表精确分派

OriginalRuleTags.actual_split以核等式确认从原完整表取前两条lookupHead／lookupTail，其余列表确为原表drop 2。remaining_classified对该实际固定表核检查：剩余规则头的最外层原节点标签均非零。

OriginalHeadDisjoint不从宿主自然数计算推断任意内部候选。它实际取得原标签和载荷的内部值，利用原节点的tag单射及numeral不同性，证明非零标签头不可能等于任意tag0精确字段行；再消去实际原arity个存在赋值。因此原表剩余规则在这些行上全部被对象推导排除。

```text
Omega(w), Constructor(k,0,w,xs,row)
  ⊢ OriginalStep(w,row,R) ↔
    (Application(lookupHead,w,row,R) ∨ Application(lookupTail,w,row,R))
  ⊢ OriginalSearchStep(w,row,R) ↔ 同一右式。
```

这里使用完整原表，未把只有两条规则作为输入假设；当前行的自然性从实际Constructor推出，不要求外部标准性、有限运行或预先解析的宿主数组。

## 实际验收与剩余边界

1301构建任务、14208项审计（368无公理／13840允许依赖）、零警告；九命令及五trust=0入口全部退出0；1165份工作区独立哈希一致、1541对精确证书足迹、11864项Internal显式声明覆盖。新增13对证书严格等于std3核心／std3加原七证书依赖；Choice桥、七锁、固定YesMetaZFC提交039c8e132cc19671d73a3933c66b4799d2599dd6及干净依赖工作区不变。新增三个核心的直接宿主／旧查找引用禁用检查，保留此前所有检查。

实际执行LEAN_NUM_THREADS=1、lake --wfail build PPAC.Migration.Internal.ObjectBoundedLookupDispatch，再运行C:/Python314/python.exe -X utf8 scripts/verify.py；九命令见本地verification/commands.json，独立复核见本地verification/bounded-dispatch-readback.json。未运行OpenAI原仓完整构建或Comparator。

当前交付是直接编译原AST的纯关系式有界规则应用与完整全表分派；原扩展语言公式的函数消去总桥、任意内部轨迹条件的可靠性／完备性，以及原完整数字接口仍未闭合。源码验收中的完整轨迹／数字接口总门保持false。

下一步3c.1b.2b.2：从原lookup量化应用提取实际Cons／索引／子行，完成任意内部ω子集轨迹与已验收表码程序的双向对应。正向用原Separation构造全部成功行的规范轨迹；反向按实际table码成员归纳，保留tail∈table严格界，排除内部循环。随后继续模式0／3、原规则检查、ProofZF/U、全内部编译、完整内部解释及最终Con；不附加FreeClosed或模型标准性。
