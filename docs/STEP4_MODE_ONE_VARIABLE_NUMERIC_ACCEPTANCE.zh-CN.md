# 原 mode1 变量数值方程及整条内部运行验收

基点：1033d70967fbe6c63201c6cffe7e2e4dec566930。单元3f.2c.3b.2d.6b；7模块100项显式声明、14组闭句。

## 对象合同

背景仍为固定 YesMetaZFC 的纯等词／成员语言、完整 Separation／Collection 的 nativeZF 和原 FirstOrder.Derives。内部 Con 保持对全部内部 ω 证明码、原六规则／27逻辑模式及完整 ZF 公理模式的量化，不假设内部 ω 外部标准。

```text
最终要求：Derives nativeZF [] (Con_ZF → Con_target)
target = ZF + PP + ACwo + ¬AC
```

最终主句仍未证明。本批完成 forall 所需 mode1 的全部变量数值输出对应，包含整条原 kind1 变量运行的行码见证消去；递归应用项、参数列、完整公式与 forall 节点尚未完成。

## 独立数值规格

AbstractVariableValueSyntax 不引用原轨迹、规则接受器、公式类型判定或比较程序，直接使用内部成员关系、后继、空集和实际变量码：

```text
BoundValue(w,d,i,x,y) :=
  [i∈d ∧ y=x] ∨ ∃s [Succ(s,i) ∧ d∈s ∧ BoundVarCode(w,s,y)].

FreeValue(w,d,i,y) :=
  [Empty(i) ∧ BoundVarCode(w,d,y)] ∨ ∃k [Succ(i,k) ∧ FreeVarCode(w,k,y)].
```

绑定索引低于当前深度时保留；其余分支把索引加一。自由索引零转为当前深度的绑定变量；后继自由索引取前驱。这里 s／k 是对象存在见证，运行 idx／depth／输出 y 均为任意内部候选，不使用宿主自然数计算。

外部 Bool 仅索引绑定／自由两个固定模式；valueSpec 不是内部统一真值断言。

## 原四规则的可靠性与完备性

AbstractVariableIndex.index_graph 在真实变量表达式图和实际变量码下，反向取得索引 Expr 图。它实际构造索引表达式的值，再由变量码索引唯一性对齐，最后消去对象 EX；不将宿主 Expr.eval 作为解码。

AbstractVariableSound 逐原规则读取真实五字段图：

- boundIdentity1：由实际守卫得 i∈depth，并由相同原输出表达式的唯一性得 y=x。
- boundAbstract：构造内部后继 s，读取守卫 depth∈s 及输出绑定变量码，再消去 s。
- freeAbstractHead：从实际输入表达式得到 Empty(i)，输出码由真实深度字段对齐。
- freeAbstractTail：从实际输入表达式得到 Succ(i,k)，输出为自由变量 k 的码。

四个 application_* 定理进一步通过原 arity 的对象 EX 消去完整有界规则应用的赋值见证。数值关系不只是预先给定某组赋值时成立。

AbstractVariableComplete 反向由各数值分支重建真实五字段 head 图和全部自然赋值；原行构造器提供 depth／parameter 的自然性，变量码提供索引自然性。再调用四条已验收原规则轨迹引入，实际构造原闭轨迹。

AbstractVariableNumeric 用上一批的两原规则精确分派合并这两个方向：在真实五字段行、Num1 和真实变量输入下，原完整闭轨迹与 BoundValue／FreeValue 对象等价。所有候选输出保留，没有仅检查某个外部计算结果。

## 整条原 kind1 变量运行

AbstractVariableRun.output_natural 从独立数值关系推导输出自然性；它不要求调用方提供 y∈ω。run_iff 的反向再从 Num1、自然 depth／P、真实输入变量码及该输出自然性，使用 SyntaxConstructors.exists_constructor 实际取得原五字段行。

正向消去原 run 自带的行 EX；反向构造行、接数值双条件并重新引入原 run。最终闭句模式是：

```text
Ω(w), Num1(mode), metadata(w,depth,P), VarCode(bound,w,idx,x)
  ⊢ Run1(w,mode,depth,P,x,y) ↔ ValueSpec(bound,w,depth,idx,x,y).
```

没有给定行码、输出自然性、赋值、后继／前驱值、全根集合、闭轨迹或归纳假设。参数 P 与深度仍是任意内部自然值。14组闭句经 Source→TheoryTransport→ZFReplay 返回原 nativeZF。

## 实际验收

1695构建任务、18288项审计（398无公理／17890允许依赖）、零警告；九命令及五trust=0入口全部退出0；1530份独立哈希一致、2095对精确证书足迹、15944项Internal显式声明覆盖

- scripts/verify.py 全仓 --wfail、九命令及五个 trust=0 入口实际退出0；100项新增声明全部进入 Audit。
- 14组新增核心／native闭句保持精确既有依赖：核心三项标准公理；native额外继承固定七个基础句子证书，无新增自定义公理。
- CheckStep4 展开 BoundValue／FreeValue 数值关系及整条运行合同，检查最终无给定行码或输出自然性前提。
- 独立读回检查全部四条原应用的赋值消去、四分支真实头图重建、对象后继／前驱消去、实际新行构造和最终前提集合。
- 数值规格守卫排除接受器／类型程序／宿主求值预言机；原 mode1 接受式、原行语法和变量码引擎保持基点 Git 字节不变。
- 七份锁及固定 YesMetaZFC 提交／干净状态不变；没有修改底座、退役反射或任何外部发布。

证据：verification/abstract-variable-readback.json、verification/summary.json、verification/commands.json。本地生成／读回脚本在 .local。

## 下一阶段工程流程

| 单元 | 实现动作 | 对象验收合同 | 状态 |
|---|---|---|---|
| mode1 全部变量 | 原四规则数值双条件，原行 EX 构造／消去 | 全内部候选输出的整条变量 Run1↔数值关系 | 已验收 |
| mode1 递归项／参数列 | 原 application1、nil／cons 与实际抽象环境 | 原 Run1／Run2 与独立项／列表变换对应 | 下一阶段 |
| mode1 完整公式 | 原11公式构造、量词深度递增及实际环境提升 | 任意内部合法公式的原mode1运行正确性 | 待完成 |
| forall 完整节点 | 原嵌套node9头、四查询、全部四赋值界 | 完整纯关系式节点双条件 | 待完成 |
| logical／theory | 原27逻辑模式、完整ZF／U公理检查 | 真实内部判定对象正确性 | 待完成 |
| 共享条件／Proof／Con | quotation／Bool／Option、内部编译及完整解释 | 原nativeZF内部Con蕴含 | 未证明 |

此前 substitution／MP／strengthening 的完整纯关系式节点仍已验收。mode1 数值变量和整条变量运行门禁为 true；完整 mode1 公式、forall 及最终 Con 门禁继续为 false。
