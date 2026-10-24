# 原投影查询自然域、七规则分派与tag数值等价验收

基点：d1c61a070ca28e2549855536eaffcff075663a58。单元3f.2c.3b.2d.2c.2a，5模块86项显式声明、14组闭句。

## 固定背景与最终目标

对象语言仍是原YesMetaZFC纯等词／成员语言，背景nativeZF保留完整Separation／Collection，正式推导关系仍为原FirstOrder.Derives。最终目标：

```text
Derives nativeZF [] (Con_ZF → Con_target)
target = ZF + PP + ACwo + ¬AC
```

内部Con仍覆盖全部内部ω证明码及原六规则／27模式。本批证明tag投影桥，未完成最终主句。

## 三类查询的真实自然域

ProjectionNodeFields.field_2对原两字段头图实际取得两个内部表达式值，用原构造器字段单射性对齐候选字段，消去全部值见证。

constructor_field_natural对任意固定有限arity／标签的实际原构造器，使用原码自然性、子字段成员关系及内部ω传递性推出任意字段属于ω。tag_natural_at、get_natural_at、field_natural_at实际消去各自查询的行见证，对任意合法外部字段位置j推出字段自然性。前提只有Ω和实际查询；没有输入、索引或候选输出自然性假设。

因此数值桥不能丢弃查询所含的自然输入域。外部arity／字段位置只索引对象定理模式，所有运行值和候选码仍为对象变量。

## 原七规则按外壳标签分派

ProjectionRuleDispatch.application_contradiction实际消去原Rule全部有界赋值存在块，用原节点标签互斥排除错误头标签。三条step分派引理把完整原七规则精确限制到：

| 实际候选行标签 | 保留原规则 |
|---|---|
| tag行0 | tagZero、tagPositive |
| get行1 | getZero、getHead、getTail |
| field行2 | fieldZero、fieldPositive |

这些是实际候选构造器与原一步规则之间的对象推导，没有把候选行的类型作为宿主检查结果，也没有替换原规则表。

## tag的全内部候选双条件

RawTag(w,x,y)在下式中缩写原数值关系PairingProjectionSyntax.step true true w x y。最终接口为：

```text
Ω(w) → [TagQuery(w,x,y) ↔ (x∈w ∧ RawTag(w,x,y))].
```

ProjectionTagCases直接反演原tagZero／tagPositive头的两个字段，并消去实际规则应用赋值块，证明闭轨迹查询的数值可靠性。tag规则无子前提，因此此处从闭轨迹取得原一步即可，不需要将ω当作已接受子查询集合。

反向的zero_checked使用原零输入／零输出的真实字段图构造原tagZero查询；positive_checked由任意内部自然标签y、载荷b及真实Raw(w,y,b,x)，构造原tagPositive的真实赋值及头查询。两者均通过原Expr行图与实际行构造器双条件消去根行见证，无预先给定根码或闭轨迹。

selected_checked实际消去载荷存在见证。checked_complete对原数值投影两分支分类：实际选中原外壳时用positive_checked；补零分支在自然输入域上由原解码定理推出输入为空，再用zero_checked。checked_iff的最终前提只有Ω，自然输入域在对象结论内明确保留，不要求候选输出自然性或正确性IH。checked_unique由实际数值函数性得到查询输出唯一。

该定理覆盖全部内部候选，保留零码及任意非规范自然外壳，不限定为规范Cons或标准自然数。完整get／field数值双条件仍未证明。

## 实际验收

1640构建任务、17562项审计（394无公理／17168允许依赖）、零警告；九命令及五trust=0入口全部退出0；1475份独立哈希一致、1997对精确证书足迹、15218项Internal显式声明覆盖

- scripts/verify.py完成全仓--wfail及五trust=0入口；86项新增声明全部列入Audit。
- 14组闭句经Source→TheoryTransport→ZFReplay返回原nativeZF；独立读回核查全部核心／native证书精确依赖。
- CheckStep4显式展开只有Ω前提的tag双条件及get任意字段自然性，并展开三组原规则名单。
- 原独立七规则接受定义未变，原数值投影定义未变；新增规则名单守卫固定2／3／2分派，独立审查仅允许原描述符及构造Expr的raw，禁止宿主数值投影／check_sound／Expr.eval等捷径。
- 七锁文件、固定上游提交和原推导核不变；新增代码无sorry／admit、占位公理或Type层内部集合选择。

证据：verification/projection-tag-readback.json、verification/summary.json、verification/commands.json、verification/build.log和verification/audit.log。探针、生成器及读回脚本留本地。提交后核查Git字节并保留17份既存CRLF-only blob。

## 接下来的完整工程路径

| 单元 | 实现动作 | 对象验收合同 | 状态 |
|---|---|---|---|
| 查询域／原规则分派／tag | 实际字段反演、原应用存在块消去、tag正反构造 | Ω→TagQuery↔自然输入域及真实数值投影 | 本批验收 |
| get内部索引归纳 | 三条原get规则、实际Separation根集合V、原get零／后继方程、完整Separation | 全内部索引及输入／候选输出的查询双条件；消去全部IH | 下一步 |
| field数值桥 | fieldZero／fieldPositive及已证get双条件 | 自然输入／索引域上的完整field查询等价 | 待完成 |
| 完整替换节点 | 原第2／3投影查询、已证第0／1／4查询、实际head及赋值界 | 全部五查询及有界赋值存在块的完整局部检查 | 待完成 |
| ProofZF/U与最终Con | 原六规则／27模式、完整公理、内部序列／编译及内部解释 | 原nativeZF中的Con_ZF→Con_target | 待完成 |

getTail必须从真实已闭合的V或实际子轨迹取得子查询；Step7在ω上仅给子行自然性，不可据此推出接受性。内部ω不得假定外部标准。最终Con及完整七规则数值桥门禁继续保持false。
