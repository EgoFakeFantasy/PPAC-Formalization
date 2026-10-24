# 原七规则投影轨迹、真实规则引入与全根展开验收

基点：c8429cf2afa61a96de200e09003def194608bd75。单元3f.2c.3b.2d.2c.1，9模块130项显式声明、15组闭句。

## 背景与对象合同

固定原YesMetaZFC纯等词／成员语言、完整Separation／Collection的nativeZF，以及原FirstOrder.Derives。最终主句仍是：

```text
Derives nativeZF [] (Con_ZF → Con_target)
target = ZF + PP + ACwo + ¬AC
```

内部Con覆盖全部内部ω证明码及原六规则／27模式。本批交付原投影轨迹的构造和一步展开，未完成上述主句。

## 独立的原七规则接受关系

ProjectionTraceSyntax直接编译固定上游ObjectProjection.rules：tagZero、tagPositive、getZero、getHead、getTail、fieldZero、fieldPositive。闭轨迹定义要求R⊆w且每个成员行在R上满足实际HornStepSyntax；condition为实际对象EX轨迹集合。tag／get／field查询再对象EX取得对应编码行。

ProjectionExprQuery.query直接为EX行图和该condition；rowQuery为实际有限构造器和该condition。constructor_query_iff通过实际图唯一性在这两种查询间双向转换，消去行见证。定义不调用RawCodeGet／Field等数值规格、纯十五规则、原变换二十八规则、宿主Expr.eval或FormulaCode类型预言机。

这里的R是对象内部集合，不限定为宿主给定的有限轨迹；内部ω也不假定外部标准。

## 从实际原规则构造闭轨迹

ProjectionTraceRules使用原Pairing取得单点闭轨迹；ProjectionTraceExtension使用原Pairing／Union为已有实际闭轨迹插入父行。所有集合见证均在对象EX内构造和消去。

ProjectionRuleConstruction直接核对七条规则无guard且至多一个子前提。head_bound实例化固定原head_variables，并用实际头表达式图推导每个赋值变量不超过头行码；application据此构造原有界赋值存在块，无额外赋值界假设。

condition_from_rule的前提只有Ω、自然赋值、实际头图和实际子查询。query_from_rule进一步对象EX构造实际头值并消去该见证，最终只有Ω、自然赋值及真实子查询；五条无子前提规则不要求任何递归正确性假设。getTail和fieldPositive直接消去子查询及子轨迹，再插入父行。七条原规则各有独立native闭句。

这证明原规则的正向轨迹封闭性，尚未将数值关系与轨迹双向对应。

## 原Separation的全部根集合与统一展开

ProjectionTraceSetSyntax.value(w,V)是原Separation公式：V为w中满足独立condition的全部根。ProjectionTraceSet.exists_value实际实例化完整Separation；每个已有闭轨迹都包含于V。

ProjectionTraceUnfold证明V仍对原七规则闭合，且每个r∈w满足condition(w,r)↔Step7(w,r,V)。exists_unfolded实际构造并消去V，返回对象闭句：

```text
∃V [SeparatedByCondition(w,V) ∧
    ∀r (r∈w → [Condition(w,r) ↔ Step7(w,r,V)])].
```

该合同没有预先给定轨迹集合、IH或外部有限性前提；推导本身甚至不需Ω假设。它是原七规则的一步展开，不是tag／get／field数值正确性定理。

## 实际验收

1635构建任务、17476项审计（394无公理／17082允许依赖）、零警告；九命令及五trust=0入口全部退出0；1470份独立哈希一致、1983对精确证书足迹、15132项Internal显式声明覆盖

- scripts/verify.py完成全仓--wfail和五个trust=0入口；130项新增声明均列入Audit。
- 15组闭句经Source→TheoryTransport→ZFReplay回到原nativeZF；独立读回精确核查全部核心／native证书足迹。
- 验收入口显式展开原七规则表和内部EX集合／ALL根双条件，避免仅通过一个未展开的命名包装。
- 接受定义守卫排除数值／类型／宿主检查器预言机；七锁文件和固定上游提交不变，上游工作树干净。
- 新增代码无sorry／admit、占位公理或Type层内部集合选择。未增加对象AC或新的推导核。

证据：verification/projection-trace-readback.json、verification/summary.json、verification/commands.json、verification/build.log和verification/audit.log。独立读回脚本、生成器和探针留在本地；提交后核查Git字节并保留17份既存CRLF-only blob。

## 后续流程及未完成边界

| 下一单元 | 实现动作 | 对象验收合同 | 状态 |
|---|---|---|---|
| 七规则数值桥2c.2 | 按原头标签／arity分派，证明tag局部等价；get按内部索引归纳，field接get | Ω下轨迹查询↔真实数值关系，并显式保留输入／索引∈ω；消去全部IH | 下一步 |
| 原替换节点投影 | 原substitutionShape第2／3项查询与实际前驱构造器槽位 | 两项实际Expr投影查询的数值等价，不假定查询已经成立 | 待完成 |
| 完整替换节点 | 合并已证第0／1／4查询、两投影查询、真实head和有界赋值存在块 | 完整局部节点检查双条件 | 待完成 |
| 原六规则／27模式及ProofZF/U | 完整公理表、原数值quotation／Bool／Option、内部序列及编译 | 全内部证明码检查／编译正确性 | 待完成 |
| 内部解释与最终Con | 完整内部解释和锁定内部Con | Derives nativeZF [] (Con_ZF→Con_target) | 待完成 |

原数值投影在ω外总化，编码行则含自然字段守卫；下一步不得丢弃输入／索引自然性。完整数值轨迹桥、完整Proof和最终Con门禁继续保持false。
