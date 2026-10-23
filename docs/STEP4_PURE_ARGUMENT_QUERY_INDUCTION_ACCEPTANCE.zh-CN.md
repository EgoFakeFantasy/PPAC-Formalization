# 全内部纯参数查询与对象集合归纳验收

基点：d1b689e0963531e8d33bb198c284548b502c3b21。完成3f.2c.3b.2b.2；9模块83项显式声明、10组闭句。

## 背景及最终目标

对象语言是原YesMetaZFC纯等词／成员语言，背景nativeZF保留完整Separation／Collection，正式推导关系是原FirstOrder.Derives。最终要求：

```text
Derives nativeZF [] (Con_ZF → Con_target)
target = ZF + PP + ACwo + ¬AC
```

内部Con涵盖全部内部ω证明码、原六规则／27模式。本批未证明最终主句；不加入对象AC、标准ω、外部良基或新的推导核。

## 全内部查询双条件

PureSyntaxArgumentInduction.checked_iff取得：

```text
Ω(w) →
  (PureSyntaxTrace.arguments(w,b,f,k,n) ↔ TermList(w,k,b,f,n)).
```

b、f、k、n均是任意内部集合候选。除Ω外不预给自然性、合法性、列表解码、实际轨迹或IH；非法候选也在该双条件范围内。

PureSyntaxListInductionSyntax.correct(w,n)以三个内部全称量词量化绑定界、自由界和长度；allIH只引用严格成员子码。该归纳性质是对象公式，不是Lean宿主归纳假设的替代接口。

PureSyntaxArgumentPremises从consRule两个真实EX前提取得实际头项行和尾列表行。头项类型由完整十五规则的真实闭轨迹恢复；尾列表查询使用同一轨迹的实际成员关系构造。原Cons编码的components在对象层推出尾码严格属于父码。

PureSyntaxConsSound恢复实际头行的四字段图、内部长度后继及Cons码；用统一IH在真实尾码处的实例获得完整尾列表类型，再按原类型构造父列表。PureSyntaxArgumentSound对完整十五规则分派：nil／cons分别处理，其余十三条由原实际首标签不交排除。

PureSyntaxConsComplete从合法头项及尾列表实际查询，在对象EX中依次选择头行、尾行和父行，调用已验收的真实轨迹合并／插入，消去全部见证。PureSyntaxArgumentComplete按原内部nil／cons分解组合双向证明。

PureSyntaxArgumentInduction使用原SetInduction.all_holds、归纳矩阵否定的Separation、Foundation及已有对象传递覆盖定理，取得所有内部根码的correct并消去allIH。没有使用宿主WellFounded、宿主自然数长度或数据选择。

## 空绑定界及mode3接入

PureArgumentsModeThree.empty_bound_query_iff取得：

```text
Ω(w) → Empty(z) →
  (PureSyntaxTrace.arguments(w,z,c,a,L) ↔ FreeVariableTermList(w,a,c,L)).
```

mode_three_iff把该真实纯参数查询接入原整条mode3运行与独立自由替换程序的双条件。此接口仍要求实际源FormulaCode、模式数码3、运行元数据和空绑定界；不预给frame、转换表、实际历史或IH。

这里的查询是已定义的纯Horn轨迹对象AST。原数值检查器及其quotation到该AST的全内部对应仍未证明；kind4公式查询桥也未完成。因此原substitutionShape最终检查器适用性和原数值纯语法桥门继续保持false，不把本批结果扩大为完整Proof检查正确性。

ObjectPureSyntaxArgumentChecker提供十组source／kernel／native闭句。CheckStep4额外直接展开仅Ω的完整参数查询双条件及空绑定界双条件，以trust=0核对。

## 实际验收

1542构建任务、16689项审计（389无公理／16300允许依赖）、零警告；九命令及五trust=0入口全部退出0；1404份独立哈希一致、1886对精确证书足迹、14345项Internal显式声明覆盖。

- scripts/verify.py退出0，全仓--wfail及五trust=0入口全部通过。
- 新增83项声明显式列入Audit；十组kernel证书精确保持三项标准依赖，native证书精确继承固定七项上游证书依赖。
- 独立复核所有源哈希、全部证书对，以及最终接口只有Ω前提、原ZF归纳资源和展开原核合同。
- 七锁文件和YesMetaZFC提交039c8e132cc19671d73a3933c66b4799d2599dd6不变；上游工作树干净。
- 无新增sorry／admit或占位公理；原纯轨迹接受定义、类型定义和十五规则表保持不变。
- 编译中修正一处iff_trans所在命名空间，未修改定理前提或推导关系。

证据：verification/pure-list-induction-readback.json、verification/summary.json、verification/commands.json、verification/build.log、verification/audit.log。提交后另复核Git原始字节，保留17份既存CRLF-only blob。

## 后续工程流程

| 顺序 | 实现任务 | 对象验收条件 | 状态 |
|---|---|---|---|
| 1 | kind0项查询 | Ω下所有内部候选的查询↔Term | 完成 |
| 2 | kind1参数查询 | Ω下查询↔TermList；内部全参数归纳消去IH | 完成 |
| 3 | 空绑定界纯参数与mode3 | 自由变量像列表双条件及原mode3完整运行接入 | AST接口完成 |
| 4 | kind4公式查询十一规则 | 查询↔FormulaCode；绑定界后继及全内部集合归纳 | 待证明 |
| 5 | 原数值quotation及实际节点调用 | 全内部数值接受与上述纯轨迹AST准确对应 | 待证明 |
| 6 | Option及其他原数值操作 | 成功失败、mode0／1／2／3和顶层抽象实例化 | 待证明 |
| 7 | 专用ProofZF／ProofU及内部解释 | 六规则／27模式、完整ZF模式、任意内部证明码 | 待证明 |
| 8 | 最终Con推导 | 原nativeZF中的Con_ZF→Con_target | 待证明 |

本批开启完整参数轨迹查询及其IH消去门；公式查询、原数值桥、最终检查器和Con门保持false。总体目标保持active。
