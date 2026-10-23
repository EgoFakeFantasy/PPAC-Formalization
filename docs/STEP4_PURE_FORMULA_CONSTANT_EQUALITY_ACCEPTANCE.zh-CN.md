# 纯公式常量与等式的对象规则及查询构造验收

基点：a8139130d5345ec13ee5ca088528487b824be0b1。完成3f.2c.3b.2c.1；7模块76项显式声明、10组闭句。

## 背景与最终目标

对象语言固定原YesMetaZFC等词／成员语言，背景nativeZF使用完整Separation／Collection，正式推导关系为原FirstOrder.Derives。最终目标仍为：

```text
Derives nativeZF [] (Con_ZF → Con_target)
target = ZF + PP + ACwo + ¬AC
```

内部Con覆盖全部内部ω证明码、原六规则／27模式。本批未证明主句，没有增加对象AC、标准ω、外部良基或新推导核。

## 实际对象推导

PureSyntaxFormulaGraph为真实kind4父行提供通用表达式字段恢复和构造。recover从实际父行与原head图取得两个元数据等式及输入表达式图；contexts_subst使用原对象EqSubst传输FormulaCode上下文；intro_formula仅引入实际编码行和真实轨迹见证，不把类型结论写入接受定义。

PureSyntaxConstantRule精确保留原constantRule 0／1。原输入表达式图与零字段常量构造双向对应；matrix_nullary恢复实际nullary，matrix_sound及application_sound取得原FormulaCode。反向matrix_complete和application_complete实际构造原有界赋值，搜索界来自实际head变量界。

PureSyntaxConstantComplete.application_iff_nullary的对象合同为：

```text
Ω(w) → FormulaRow(w,b,f,n,r) →
  (ActualConstantApplication(truth,w,r,R) ↔ Nullary(truth,w,b,f,n)).
```

truth是两个固定规则的外部有限模式索引，b、f、n、r、R均为内部候选。无预给类型前提。checked_nullary从合法常量实际取得父行和单点闭轨迹；typed_constant_checked把已有FormulaCode与实际零字段常量码接入该完整查询构造。

PureSyntaxTermPremise将任意固定有限原赋值中的真实项前提EX行恢复为纯Term，使用完整十五规则的闭合性；不调用宿主Expr.eval，也不假设该前提的项类型。它为等式及后续关系原子提供通用接口。

PureSyntaxEqualityRule保留原equalityRule两个真实项前提。matrix_sound由实际head三字段恢复内部EqualCode，经两个EX前提与同一真实闭轨迹恢复两项类型，再由既有FormulaCodeKnownAtomic.equal_iff取得FormulaCode；对象等词负责原上下文传输。application_sound没有FormulaCode或IH前提。

PureSyntaxEqualityComplete.condition_from_rows先实际合并两条子轨迹，再按原规则构造并插入父行。checked_equality从Ω、两个合法项及实际EqualCode出发，在对象EX中选择两个项查询行、构造父行和公共闭轨迹，并消去全部见证：

```text
Ω(w) → Term(w,b,f,x) → Term(w,b,f,y) → EqualCode(w,x,y,n) →
  PureSyntaxTrace.formula(w,b,f,n).
```

typed_equality_checked从FormulaCode和实际EqualCode恢复两项类型后使用该构造。无预给行、轨迹或IH。

ObjectPureSyntaxFormulaAtoms提供十组source／kernel／native闭句；名称仅是模块分组，不表示所有四种原子构造已完成。CheckStep4额外直接展开常量局部双条件及等式查询构造，以trust=0核对。

## 范围边界

本批完成两个常量与等式的局部规则健全性及查询构造。尚未从任意完整kind4查询恢复FormulaCode，也未完成全公式查询双条件。membership、否定、四种二元连接词、两个量词和统一内部集合归纳仍待实现。

原纯轨迹AST、十五规则表及既有kind0／kind1查询证明均保持原样。原数值检查器quotation与这些对象轨迹AST的对应、最终证明检查器适用性及Con仍未证明。相关验收门保持false。

## 实际验收

1549构建任务、16765项审计（390无公理／16375允许依赖）、零警告；九命令及五trust=0入口全部退出0；1411份独立哈希一致、1896对精确证书足迹、14421项Internal显式声明覆盖。

- scripts/verify.py退出0；全仓--wfail及五trust=0入口全部通过。
- 新增76项声明显式纳入Audit；十组kernel证书精确保持三项标准依赖，native证书精确继承固定七项上游证书依赖。
- 独立复核全部源哈希和证书对，以及常量局部双条件仅Ω／实际父行、等式健全性不预给类型／IH、等式查询不预给轨迹的接口。
- 七锁文件和YesMetaZFC提交039c8e132cc19671d73a3933c66b4799d2599dd6不变；上游工作树干净。
- 无新增sorry／admit或占位公理；未关闭警告或内核检查。
- 构造常量单点轨迹时显式选取临时原应用的轨迹参数为内部w，再由原无前提规则搬到实际单点集合；不存在宿主选择或预给最终轨迹。

证据：verification/pure-formula-atoms-readback.json、verification/summary.json、verification/commands.json、verification/build.log、verification/audit.log。提交后另核对Git原始字节，保留17份既存CRLF-only blob。

## 下一实现流程

| 构造／任务 | 具体原规则 | 下一对象验收要求 | 状态 |
|---|---|---|---|
| 两常量 | constantRule 0／1 | 实际应用↔nullary，完整查询构造 | 本批完成 |
| 等式 | equalityRule，tag3 | 真实两项前提恢复及完整查询构造 | 本批完成 |
| 成员原子 | relationRule membership，tag2 | 实际二项参数森林、纯参数查询和Source成员码对应 | 待证明 |
| 否定 | unaryRule 4 false | 实际子公式前提、严格子码IH及查询构造 | 待证明 |
| 四二元连接词 | binaryRule 5／6／7／8 | 两实际子查询、共同轨迹、严格子码IH | 待证明 |
| 两量词 | unaryRule 9／10 true | 实际绑定界后继、变化上下文和严格子码IH | 待证明 |
| 完整公式桥 | kind4，完整十五规则 | 任意内部候选查询↔FormulaCode，全参数集合归纳消去IH | 待证明 |
| 数值检查与最终迁移 | 原quotation／Option／六规则／27模式 | 全内部ProofZF/U、内部解释和最终Con推导 | 待证明 |

总体目标保持active。
