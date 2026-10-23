# 严格查表准确域与自由替换量词稳定性验收

2026-10-23；S3.4c.2b.2c.3c.1a；基点ec44af2177e1d158be454871de2ff4755263de2f。

本批完成严格查表的对象操作核心、合法列表上全部内部索引的准确成功／拒绝域，以及原自由替换表L在实际量词提升下严格不变。对象语言为纯等词／成员语言，背景为原nativeZF完整Collection。全部结论先有Source.Derives，再经TheoryTransport及ZFReplay产生原FirstOrder.Derives nativeZF []证书。

最终目标仍为原nativeZF中Con_ZF → Con_(ZF+PP+ACwo+¬AC)。Con保留全部内部ω证明码、原六规则／27模式和完整Separation/Collection。本批不等于原SyntaxTransform数值程序码／Option结果的完整对应，也未完成模式0／3的全公式接口、原规则检查兼容、ProofZF/U、内部解释或最终Con。

## 实际量词提升保持同一L

FreeSubstProgramBinder.free_code_stable从实际旧环境、原CodeConversion(w,b,d,L,J)、旧索引binder提升及新双项表提升，证明新free项像码H=L。证明先取得真实提升环境，再以新目标bound长度的合法性调用上一批same_code和全内部转换唯一性。没有把索引码J误当作项列表L，也没有假定free项像图提升后自动相等。

lifted_environment进一步结合SyntaxIdentityLift.code_lift，得到：

```text
u=v ∧ IdentityCode(w,u,M) ∧ H=L ∧ Env(w,M,J,K,L,u,a,u,c).
```

这里u/v为实际新源／目标bound长度，M为实际提升后的bound恒等索引码，K/H为实际提升后的两份项像码。等词代换把新目标长度及free项像码归一到u、L。child_execution据此把真实子调用重新装配成同一FreeSubstProgram接口，保留原列表L；量词下仍不添加FreeClosed前提。

## 严格查表的执行定义

旧StructuralListField的head投影在非法形状上默认返回零，不能直接充当严格Option查表。新StrictLookupSyntax不调用旧完整field关系：

```text
Returned(w,n,i,y) := ∃t (
  ActualTailIteration(w,n,i,t) ∧ SelectedConsHead(w,t,y)).
HasOutput(w,n,i) := ∃y Returned(w,n,i,y).
Rejected(w,n,i) := ¬HasOutput(w,n,i).
Checked(w,n,i,y) := n∈w ∧ i∈w ∧ Returned(w,n,i,y).
```

ActualTailIteration使用已证明的真实内部后继域及原递归图；单步tail在当前外壳不是Cons时进入空集零状态。SelectedConsHead必须实际匹配原Cons构造，不采用默认head值。执行核心只组合已验收的数值库子程序；字段关系只在对照证明中出现。新增直接引用检查禁止StrictLookupSyntax调用旧field或宿主SyntaxTransform.lookup。

| 对象接口 | 全部内部数据上的结论 |
|---|---|
| StrictLookupRules.zero_selected | 零索引成功恰等于当前真实Cons head匹配 |
| successor_iff | 当前Cons(h,t,n)上的后继索引读取，恰等于tail t的前驱索引读取 |
| StrictLookupSinkInduction.empty_iteration | 原ω归纳证明空集零状态对所有内部tail迭代索引均吸收 |
| StrictLookupFailure.no_cons_rejected | 当前外壳不是Cons时，任意内部自然索引均拒绝；不会通过默认零恢复成功 |
| nil_rejected | 合法空列表在所有内部自然索引上拒绝 |
| cons_zero_returns | 当前Cons的零索引返回head；不要求未访问的tail是完整合法列表 |

最后一项保留原lookup的重要行为：未访问尾部非法不意味着零索引一定失败。本批没有错误地声称所有非法完整列表都返回none。原函数的外壳检查、当前Cons的严格tail界及Option递归结构仍须与其数值程序表示进一步对应；不能据此提前通过全原接口总门。

## 合法列表的准确域

StrictLookupDomainInduction在原ZF中用第二个ω归纳闭合全部内部列表长度。归纳性质在同一对象公式内全称量化列表码n、索引i和候选y；后继步实际取得Cons头尾和非零索引前驱，不使用外部List或标准性。

对任意内部长度r、列表码n、自然索引i及候选y：

```text
Omega(w), HasLength(w,n,r), i∈w
  ⊢ Returned(w,n,i,y) ↔ (i∈r ∧ Field(w,n,i,y))
  ⊢ HasOutput(w,n,i) ↔ i∈r
  ⊢ Rejected(w,n,i) ↔ ¬i∈r.
```

StrictLookupValue.actual_fiber在i∈r时实际取得y，value同时包含Returned、y∈w和对全部内部候选的唯一性。fiber_iff_bound证明该真实唯一值纤维恰等于i∈r；in_range_field_iff及checked_iff_domain给出准确字段接口。没有把默认零输出当作越界读取成功。

free_image_at_edge从原CodeConversion(w,a,c,L,J)、J的实际解码图r及真实边r(i)=j，推导：

```text
Omega(w), CodeConversion(...), Encoded(r,J), Edge(r,i,j)
  ⊢ Returned(w,L,i,q) ↔ VarCode(false,w,j,q).
```

候选q仍是任意内部变量；证明不预设q已是合法目标变量码。这把严格查表直接接到原自由替换参数L，而不是只接到外部有限列表样例。

## 原核闭句与实际验收

ObjectStrictLookup提供21组Source闭句、sourceZF原核和nativeZF原核证书，包括binder原L稳定、子执行闭包、严格零／后继方程、外壳及Nil拒绝、空集吸收归纳、准确成功／拒绝域、实际唯一纤维及原替换表字段对应。全部运行时变量通过close在对象语言中闭合。

- 全仓lake --no-cache --wfail build：1213 jobs，退出0；九条验收命令及五个--trust=0入口全部退出0。
- 13678项声明审计：357项无公理依赖、13321项符合记录依赖，零警告；禁止补洞标记检查通过。
- 新增12模块、167条显式声明、21组闭句；累计11334条Internal显式声明全部纳入审计。
- 新21组及累计1492对core/native证书逐项匹配精确足迹：core恰为propext、Classical.choice、Quot.sound；native恰为该三项加原固定七项。独立Choice桥依赖未扩散。
- 1111份工作区文件独立SHA-256全部一致；严格查表直接引用检查及原公式程序8核心模块检查通过。
- 七项锁文件不变；YesMetaZFC固定039c8e132cc19671d73a3933c66b4799d2599dd6，依赖工作区干净。
- 八项本批细分门为true；原模式0／3完整数值接口、原规则兼容、专用Proof检查／编译和最终Con等总门保持false。

命令：LEAN_NUM_THREADS=1，C:\Python314\python.exe -X utf8 scripts/verify.py。独立读回为本地verification/strict-lookup-readback.json；日志及生成器留在本地。本批没有推送、创建PR、运行原OpenAI全构建或Comparator。

## 后续工程单元

| 单元 | 实施输入 | 原对象推导验收 | 状态 |
|---|---|---|---|
| 3c.1a | 实际tail递归、原Cons匹配、原L同码桥 | 严格查表操作方程、准确域／拒绝／唯一值、L的binder稳定性及原核证书 | 本批完成 |
| 3c.1b | 上述执行核心及固定原lookup程序 | 原数值程序码／Option结果表示与操作核心的统一对应，保留精确失败行为 | 下一步 |
| 3c.2 | 原boundValue/freeValue模式0／3 | bound恒等、free位移或同一L查表的准确数值接口 | 待完成 |
| 3c.3 | 原全11公式分支、depth+1和真实binder | 原类型／参数守卫下，全内部数值变换与独立特化执行对应 | 待完成 |
| 3c.4 | 原free_strengthening/free_substitution和上下文码 | 原严格Option模式0／3及规则检查兼容，不加原规则没有的FreeClosed前提 | 待完成 |
| 5／6／7 | 专用ProofZF/U、完整内部解释及准确内部Con | 六规则／27模式和全Separation/Collection检查／编译、最终原nativeZF对象Con蕴含 | 未完成 |

原raw函数还处理未通过类型／参数检查的树；纯签名受检接口不能声称在这些非法输入上与所有raw默认行为等价。固定lookup程序的表示也不等于任意内部程序码的通用解释器。
