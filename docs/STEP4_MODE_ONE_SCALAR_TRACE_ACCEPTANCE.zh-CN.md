# 原 mode1 项分派、变量完整轨迹及四条实际规则引入验收

基点：b646447a6e81e809fe04829c6715e150fa0508d4。单元3f.2c.3b.2d.6a；5模块62项显式声明、9组闭句。

## 对象背景与最终目标

固定原 YesMetaZFC 纯等词／成员语言、完整 Separation／Collection 的 nativeZF 和原 FirstOrder.Derives。内部 Con 保持锁定定义，覆盖全部内部 ω 证明码、原六规则／27逻辑模式及完整 ZF 公理模式。最终仍要求：

```text
Derives nativeZF [] (Con_ZF → Con_target)
target = ZF + PP + ACwo + ¬AC
```

最终主句未证明。本批补 forall 所需 mode1 的底层原规则接口；不把变量展开、正向轨迹或完整构建误作完整 mode1 公式操作／forall 节点已完成。

## 原完整规则表精确分派

OriginalAbstractClasses 对固定原28规则逐项分类，直接引用原规则，无新执行表。内部 mode 数码由 Num1 提供，输入／输出码和参数仍是对象变量。真实 kind1 五字段行上，OriginalAbstractDispatch.dispatch_iff 证明：

```text
OriginalStep(w,row,R) ↔ Step([
  boundIdentity 1 true, boundAbstract,
  freeAbstractHead, freeAbstractTail, application 1],w,row,R).
```

异种行头由原构造器不交性排除；错误 mode 由实际第0字段图及对象数码不等式排除。没有根据宿主 Expr.eval 计算运行码。

给定真实变量输入，variable_dispatch_iff 再以原变量标签不交性排除无关规则：绑定变量保留 boundIdentity1／boundAbstract；自由变量保留 freeAbstractHead／freeAbstractTail。原 application1 在两种变量情况下均被排除。

## 完整变量闭轨迹双条件

OriginalAbstractTrace.variableStep 只定义为上述两条原规则的完整 HornStepSyntax.step，包括原赋值数、自然赋值、搜索界、真实头、守卫和原前提。两条变量规则均无子前提，因此 trace 参数在接受公式中定义性消失；variable_step_trace_irrelevant 用 rfl 核查，不能据此把 w 当作已给定有效轨迹。

variable_condition_iff 实际由原完整 Separation 构造全部原轨迹根集合 V，使用原 HornUniversalTraceClosed.unfold_iff 接原一步展开，随后应用变量两规则精确分派，最后在对象 EX 中消去 V：

```text
Ω(w), Constructor5tag1(w,xs,row), Num1(xs0), VarCode(bound,w,idx,xs3)
  ⊢ OriginalCondition(w,row) ↔ VariableStep(bound,w,row).
```

最终无给定 V、闭轨迹、成员关系、规则应用或自然输出前提。任意内部候选输出 xs4 保留在原规则的有界搜索中，没有有限样本或外部标准自然数限制。

这取得真实变量查询与两条原有界应用的全双条件；尚未把所有赋值见证完全化简为 idx／depth／输出的数值方程。

## 守卫数值对应及四规则实际轨迹

OriginalAbstractPositive 使用真实 Expr 图和 HornRuleValue.guard_at，证明两个完整守卫（含尾部 truth）的对象双条件：

| 原规则 | 真实内部守卫 |
|---|---|
| boundIdentity 1 true | env2 ∈ env0 |
| boundAbstract | Succ(s,env2) 下 env0 ∈ s |

前者是索引低于绑定深度；后者覆盖索引不低于深度时的移位分支。这里尚不声称已证明两分支的完整数值输出方程或总性。

通用 guarded_leaf_step／condition 从实际原头图取得全部赋值搜索界，并使用真实守卫及空子前提构造原一步／闭轨迹。bound_preserved、bound_shifted、free_head、free_tail 分别实例化原四条变量规则；自由变量规则没有额外守卫。

正向轨迹由原实际集合与 HornTraceExtension 构造，没有以“规则应当接受”为新公理。全部9组闭句经 Source→TheoryTransport→ZFReplay 返回原 nativeZF。

## 实际验收

1688构建任务、18188项审计（398无公理／17790允许依赖）、零警告；九命令及五trust=0入口全部退出0；1523份独立哈希一致、2081对精确证书足迹、15844项Internal显式声明覆盖

- scripts/verify.py 全仓 --wfail、九命令和五个 trust=0 入口实际退出0；62项新增声明全部进入 Audit。
- 9组新增闭句的核心证书精确依赖既有三项标准公理；native 证书额外继承固定七个基础句子证书。无新增自定义公理。
- CheckStep4 核查原五规则列表和绑定／自由两规则列表，并展开完整变量轨迹双条件的前提及接受式。
- 独立读回核查前提集合、原规则引用、实际 Separation 全根见证构造／消去、两个数值守卫以及四个正向轨迹；接受定义不含比较规格或宿主求值预言机。
- 旧 mode0／3 分派、全根集合及闭轨迹引擎、完整 strengthening 节点均保持基点 Git 字节不变。七锁、固定 YesMetaZFC 提交及上游干净状态不变。

机器证据：verification/original-abstract-readback.json、verification/summary.json、verification/commands.json。本地生成／读回脚本在 .local。

## 后续工程流程

| 单元 | 实现动作 | 对象验收合同 | 状态 |
|---|---|---|---|
| mode1 变量分派／引入 | 原五项规则、两变量规则、守卫、实际轨迹 | 完整变量查询↔两原有界应用，无全根集合前提 | 已验收 |
| mode1 数值变量方程 | 消去各原应用的赋值，实际读入／出变量码与守卫 | 全内部 idx／depth／候选输出的数值双条件 | 下一批 |
| mode1 项／参数列／公式 | 接实际 AbstractFreeTop 环境和量词提升，内部结构归纳 | 任意内部合法公式的原mode1运行正确性 | 待完成 |
| forall 完整节点 | 原嵌套 node9 头、四查询、全部四赋值界 | 完整纯关系式节点双条件 | 待完成 |
| logical／theory | 27逻辑模式及完整ZF／U公理检查 | 真实内部判定对象正确性 | 待完成 |
| 原共享条件／Proof／Con | quotation／Bool／Option、内部编译和完整解释 | 原nativeZF内部Con蕴含 | 未证明 |

已有 substitution／MP／strengthening 完整纯关系式节点维持已验收。新 mode1 精确分派／变量轨迹门禁为 true；完整 mode1 公式、forall 及最终 Con 门禁仍为 false。
