# 实际完整图、自然码复合与项复合验收

2026-10-22；分支 migration/yesmeta-step3；本批基点 bef6eeb50b9aecb90647584016c8b0fd26bf144b。
F2.3a 及 F2.3b.1 已完成：实际唯一完整复合图、实际唯一原自然复合码，以及项重命名的精确两阶段复合双条件。
真实 binder 提升与复合相容、公式复合、捕获规避替换、ProofZF/U、内部编译/解释和最终内部 Con 仍未完成。

## 对象合同和固定背景

对象语言保持原 YesMetaZFC 纯等词/成员语言，推导关系保持原 FirstOrder.Derives。
背景保持 nativeZF 的完整 Collection 呈现；源 ZF 的完整 Replacement 经既有 TheoryTransport/ZFReplay 传输到原核。
最终要求 FirstOrder.Derives nativeZF [] (Con_ZF → Con_target)，target 为 ZF+PP+ACwo+¬AC。
Con 遍历全部内部 ω 证明码，原六规则、27 模式及完整 Separation/Collection 不变。
没有新增对象 AC、标准 ω、外部良基、不可达、模型存在或 Con(nativeZF) 前提。

## 全部内部边上的实际复合图

输入为完整实际索引图 r:a→c 与 t:c→e；顺序是先 r 后 t，结果图 g 表示 t∘r。
三个作用域 a,c,e 显式保留。关系矩阵和结果合同为：

```
Value(r,t,i,j) := ∃k (Edge(r,i,k) ∧ Edge(t,k,j))
Composed(w,r,t,a,c,e,g) :=
  IndexMap(w,r,a,c) ∧ IndexMap(w,t,c,e) ∧
  IndexMap(w,g,a,e) ∧ EdgeLaw(Value,a,g).
```

每个 i∈a 先经 r 取得实际中间值 k∈c，再经 t 取得实际输出 j∈e。
原 functionOn 的单值性对齐任意两个中间值，继而对齐输出，证明原 Replacement 所需的总单值纤维。
原 Replacement 实际构造 g；保留完整 entriesOn、totalOn、值域限制及无杂项要求。

对全部内部 i,j，原核证明：

```
Edge(g,i,j) ↔ ∃k (Edge(r,i,k) ∧ Edge(t,k,j)).
```

右侧由原完整 r 图恢复 i∈a，因此最终双条件无需额外的输入域守卫。
实际图存在且唯一；空域、非单射映射和内部非标准有限长度均在范围内。
此集合图存在证明只消费两个 IndexMap，不额外要求 Ω；自然码构造另用 Ω。
关键证书：native_pointExists/pointFiber/relationTotal、native_graphExists/graphFiber/graphUnique/graphEdges/graphTargetMap。

## 原自然映射码的实际复合

CodedCompose(w,a,c,e,R,T,K) 是有限纯公式，内部存在量化实际 r,t,g，内容为：

```
Encoded(w,r,a,c,R) ∧ Encoded(w,t,c,e,T) ∧
Composed(w,r,t,a,c,e,g) ∧ Encoded(w,g,a,e,K).
```

不是把 Lean 中两个函数的复合作为对象图；输入图、结果图和原自然列表码均实际存在。
候选输入/输出的任意实际解码图，由原同码图唯一性和原等词替换恢复同一 Composed 关系。
在给定三个实际 Encoded 图时，CodedCompose 与 Composed 精确等价，所有内部边继承上述复合双条件。
源长度、中间范围与目标范围仍分别为 a,c,e；没有从列表码单独推断独立目标范围。

在 Ω(w) 下，原核还证明：

```
∃K CodedCompose(w,a,c,e,R,T,K)
  ↔ (MapCode(w,a,c,R) ∧ MapCode(w,c,e,T)).
```

合法输入实际产生唯一 K，唯一性与全部内部候选比较；另有实际唯一 codeFiber。
CodedCompose 本身恢复两个输入 MapCode 及输出 MapCode(w,a,e,K)。
关键证书：native_codeReadSources/codeReadGraphs/codeEncodedIff/codeEdges、native_codeExists/codeUnique/codeFiber/codeInputIff。

## 项重命名的精确两阶段双条件

对 bound/free 两类原变量码，正式消去两次重命名的实际索引字段。
原中间变量码的索引唯一性对齐连接点，再用实际复合边双条件构造结果分支。
相反类别的连接由原变量码互斥性排除，不把 bound 和 free 混合。

给定 Ω(w)、Composed(w,r,t,a,c,e,g) 和 Composed(w,s,u,b,d,f,h)，对全部内部项码候选 n,v：

```
TermRename(w,g,h,a,b,e,f,n,v)
  ↔ ∃q (TermRename(w,r,s,a,b,c,d,n,q) ∧
         TermRename(w,t,u,c,d,e,f,q,v)).
```

反向分解先从结果的源类型实际取得第一次输出 q，再取得第二次输出 v'。
正向复合及原结果图上的项重命名唯一性证明 v'=v，原等词替换修正第二次输出。
中间 q 由对象存在量词取得；两端自然性及类型由原项关系恢复，无外部标准码限制。
六个 bound/free 作用域 a,b,c,d,e,f 均显式保留，图允许非单射。
关键原核证书：native_termBranch、native_termCompose、native_termFactor、native_termCollapse、native_termComposeIff。

## 实际验收

`C:/Python314/python.exe -X utf8 scripts/verify.py` 退出 0。
完整命令记录为原源规则/理论锁检查、版本检查、全仓 --no-cache --wfail 构建及五个 trust=0 入口，共九条，全部退出 0。

| 检查项 | 实际结果 |
|---|---|
| 全仓构建 | 794 jobs，退出 0 |
| 声明审计 | 8864 项；292 项无公理依赖，8572 项允许依赖 |
| 警告 | 0 |
| 本批显式声明 | 11 模块、171 项，全覆盖 |
| Internal 累计显式声明 | 6549 项，无漏审 |
| 新增 Source/sourceZF核/nativeZF核模式 | 28 对核心/native 精确足迹 |
| 累计模式 | 843 对核心/native 精确足迹 |
| 源码 SHA256 独立回读 | 763 份，差异 0 |
| 九命令/五 trust=0 | 全部退出 0 |
| 七份理论/可信基/依赖锁 | 与基点一致 |
| YesMetaZFC | 039c8e132cc19671d73a3933c66b4799d2599dd6，依赖工作区干净 |

新增核心证书依赖精确为 propext、Classical.choice、Quot.sound；native 证书另含既定七项原证书。
这是记录中的 Lean 可信基依赖，没有新增对象公理，原 choice 额外证书仍单独限域。
所有新声明显式纳入 Audit；CheckStep4 含 28 个原核模式实例及两个纯 AST 检查。
独立回读为忽略目录 verification/compose-readback.json；日志和生成辅助仅留本地。
原 OpenAI 完整构建和 Comparator 本批未运行；未推送。

## 后续 agent 工程流程

| 单元 | 输入与实现职责 | 原核验收条件 | 状态 |
|---|---|---|---|
| F2.3a | 两幅完整实际图、三个明确作用域及原自然码 | 实际唯一复合图/码、全内部边双条件、任意实际解码识别及精确输入判据 | 完成 |
| F2.3b.1 | 原 bound/free 项关系和两幅结果复合图 | 两阶段项复合及存在实际中间项码的精确双条件 | 完成 |
| F2.3b.2 | 原 Composed 及三个真实 binder Lifted；共享实际后继范围 A,C,E | 提升后的结果图满足提升输入图的 Composed；再传输到三组 CodedLift 与 CodedCompose | 待完成 |
| F2.3c | 全 11 构造、上述提升相容、全部内部码/作用域 | 内部成员归纳关闭公式正向复合；再用实际输出总性/唯一性取得完整两阶段双条件 | 待完成 |
| S | 内部替换序列及全部 bound/free 范围 | 捕获规避替换存在唯一、类型与代数，覆盖原替换/加强规则 | 待完成 |
| 5–6 | 原六规则/27 模式与完整 ZF/目标理论公理码 | ProofZF/U、全内部编译/解释及最终内部 Con 原核推导 | 待完成 |

提升相容须处理真实零边和同步后继边；中间后继须实际构造，独立后继候选由原唯一性对齐。
不能用宿主 Nat.succ/函数复合或外部 AST 等式跳过该步。
图/码复合与项复合门禁已为 True；提升相容、公式复合、恒等与复合联合总门禁、完整 FormulaRename、替换、ProofZF/U 与最终 Con 仍为 False。
