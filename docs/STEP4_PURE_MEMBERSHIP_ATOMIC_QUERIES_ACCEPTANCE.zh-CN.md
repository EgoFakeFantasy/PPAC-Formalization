# 纯成员关系与四种Source原子查询构造验收

基点：5747104f92f30a29a32eca6fb65249aba1099207。完成3f.2c.3b.2c.2；8模块74项显式声明、10组闭句。

## 背景及最终目标

对象语言为原YesMetaZFC等词／成员语言，背景nativeZF保留完整Separation／Collection，正式推导关系为原FirstOrder.Derives。最终要求：

```text
Derives nativeZF [] (Con_ZF → Con_target)
target = ZF + PP + ACwo + ¬AC
```

内部Con必须覆盖全部内部ω证明码、原六规则／27模式。本批未证明主句；未加入对象AC、标准ω、外部良基或新的推导核。

## 原成员规则的实际载荷与类型恢复

PureSyntaxMembershipInput独立定义原关系规则的实际输入表达式，以及由零字段成员符号码、真实Cons载荷、内部数码2和原raw节点组成的对象EX数据。input／body／data定义不引用Term、TermList、FormulaCode或纯接受关系；data_iff证明真实表达式图与该载荷数据双向对应，不调用宿主Expr.eval。

PureSyntaxMembershipType.data_app_iff在内部零数码前提下连接该独立数据与原关系application。at_forest_iff再用精确二项森林和实际零字段符号码连接Source成员码。零集合和中间节点留在对象EX中，不抽取宿主见证。

PureSyntaxMembershipPremise从原kind1前提的实际EX行及真实闭轨迹，恢复长度为内部数码2的纯TermList。随后使用已有ArgumentPairOutput.exists_output，在对象EX内恢复两个合法项和精确二项森林。有限索引2只指定固定原规则，列表长度值、字段值、列表码均为内部对象。

PureSyntaxMembershipRule逐字保留relationRule membership的原head和唯一长度2前提，CheckStep4以rfl另核对。matrix_sound由实际head三字段、真实参数前提及同一闭轨迹取得FormulaCode；application_sound消去原三槽有界赋值。接口没有预给FormulaCode或IH。反向matrix_complete／application_complete实际构造原规则应用和搜索界。

## 完整成员与原子查询构造

PureSyntaxMembershipQuery由实际长度2列表及独立载荷数据取得真实参数查询，然后实际构造成员父行并插入已有闭轨迹，消去参数行、父行及轨迹见证。

PureSyntaxMembershipComplete.checked_at的对象合同为：

```text
Ω(w) → ZeroScalar(w,s) → Term(w,b,f,x) → Term(w,b,f,y) →
  MemberCode(w,s,x,y,n) → PureSyntaxTrace.formula(w,b,f,n).
```

没有预给参数森林、列表长度值、编码行、最终轨迹或IH。森林和内部数码2在对象EX中实际构造。typed_membership_checked从FormulaCode与真实成员码恢复两项类型后取得查询；checked_membership消去完整Source成员原子的三个内部字段见证。

PureSyntaxAtomicComplete.checked_atomic统一四种完整Source原子公式：

```text
Ω(w) → SourceAtomic(w,b,f,n) → PureSyntaxTrace.formula(w,b,f,n).
```

它组合已验收的两个常量、等式及本批成员关系，只有Ω与完整SourceAtomic前提。该构造方向不等于任意完整kind4查询的反向健全性，也不是全公式查询双条件。

ObjectPureSyntaxMembership提供十组source／kernel／native闭句；CheckStep4额外直接展开成员查询和四原子统一构造合同，以trust=0核对。

## 实际验收

1557构建任务、16839项审计（390无公理／16449允许依赖）、零警告；九命令及五trust=0入口全部退出0；1419份独立哈希一致、1906对精确证书足迹、14495项Internal显式声明覆盖。

- scripts/verify.py退出0；全仓--wfail与五trust=0入口全部通过。
- 新增74项声明显式纳入Audit；十组kernel证书精确保持三项标准依赖，native证书精确继承固定七项上游证书依赖。
- 独立复核所有源哈希、全部证书对、原head／premise精确对应、独立载荷定义，以及查询接口没有预给森林／行／轨迹／IH。
- 七锁文件及YesMetaZFC提交039c8e132cc19671d73a3933c66b4799d2599dd6不变；上游工作树干净。
- 无新增sorry／admit或占位公理；纯轨迹定义与十五规则表保持不变。

证据：verification/pure-membership-readback.json、verification/summary.json、verification/commands.json、verification/build.log、verification/audit.log。提交后另复核Git原始字节，保留17份既存CRLF-only blob。

## 仍未完成的目标及工程流程

| 顺序 | 实现任务 | 对象验收条件 | 状态 |
|---|---|---|---|
| 1 | 项／参数查询 | 全内部kind0／kind1双条件，仅Ω、IH已消去 | 已验收 |
| 2 | 四种原子 | 实际局部规则健全性，完整Source原子统一查询构造 | 本批完成 |
| 3 | 否定及四二元连接词 | 实际子公式查询、严格子码IH及真实轨迹合并 | 待证明 |
| 4 | 两量词 | 内部绑定界后继、实际子查询及变化参数IH | 待证明 |
| 5 | 全公式桥 | 十五规则完整分派；任意内部kind4查询↔FormulaCode；集合归纳消去IH | 待证明 |
| 6 | 原数值quotation／Option及检查器调用 | 数值接受与纯轨迹AST对应，完整内部成功失败条件 | 待证明 |
| 7 | ProofZF／ProofU和内部解释 | 六规则／27模式、完整ZF模式、全内部证明码 | 待证明 |
| 8 | 最终Con推导 | 原nativeZF中的Con_ZF→Con_target | 待证明 |

成员规则局部健全性／查询构造及四原子构造门开启；成员输入上的完整kind4查询双条件、逻辑分支、全公式桥、原数值桥和最终Con门保持false。总体目标保持active。
