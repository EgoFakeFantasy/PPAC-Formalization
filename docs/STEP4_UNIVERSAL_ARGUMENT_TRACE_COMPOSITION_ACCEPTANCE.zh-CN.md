# 原完整表共享轨迹及参数列表分派验收

基点：5278e9fb8700461b50a4558f70a0e7ecfa4326f4。完成S3.4c.2b.2c.3c.2c.2a：实际共享轨迹集合、原28规则子轨迹组合、kind2参数列表完整分派及nil／cons正向轨迹引入。未完成原参数列表的精确输出方程和任意内部长度的归纳对应。

## 固定对象目标

对象语言、原nativeZF完整Collection背景和原FirstOrder.Derives保持不变。最终仍须证明Derives nativeZF [] (Con_ZF → Con_target)，目标理论ZF+PP+ACwo+¬AC；内部Con量化全部内部ω证明码，保留原六规则／27模式和完整Separation／Collection。原Horn变换表有28条规则，与Hilbert逻辑公理的27模式是不同计数。

本批使用原ZF分离、配对、并集及已验收的原表正性／单调性；不加入新的公理、选择原则、模型、标准ω或外部有限轨迹假设。运行时赋值、自然行、集合和子轨迹全部是对象变量。

## 实际通用轨迹集合

```text
Trace(w,r) := ∃R (R⊆w ∧ r∈R ∧ Closed_original(w,R))
Value(w,V) := ∀r (r∈V ↔ (r∈w ∧ Trace(w,r))).
```

HornUniversalTraceSyntax.matrix是原Trace公式的真实Separation矩阵；HornUniversalTraceValue.exists_value返回对象存在证书∃V Value(w,V)。构造对任意内部集合w成立；后续原数值规则以Omega(w)作为守卫使用它。

Trace本身已蕴含r∈w，因此Value下r∈V↔Trace(w,r)，不需要预给r自然。若R⊆w且R原表闭合，则其每个成员以同一个实际R见证Trace，故R⊆V。对r∈V，正式消去Trace的实际R见证，取原Closed(R)的一步，再用原表正性把该步传到V；得到Closed_original(w,V)。全部存在见证留在对象量词内，没有从每个Trace证明中抽取宿主轨迹函数。

在Value(w,V)及r∈w下：

```text
Trace(w,r) ↔ OriginalStep(w,r,V).
```

反向实际利用原Pairing／Union将r插入V；继承原闭合与自然范围，取得真实轨迹存在证书。这里的V是证明中构造的共享见证，未改变原Trace／规则表／执行判断的定义，也没有将它当作任意内部程序的解释器或终止性证明。

## 原全部规则的子轨迹组合

```text
TracedPremise(e,w,env) := ∃y (OriginalExprGraph(e,w,env,y) ∧ Trace(w,y)).
TracedMatrix(rule,w,r,env) := HeadGraph(rule,w,r,env)
  ∧ (OriginalGuards(rule,w,env) ∧ AllTracedPremises(rule,w,env)).
```

在实际Value(w,V)下，原premise中的y∈V与Trace(w,y)双向对应，逐个原前提、完整前提合取和完整局部矩阵均有实际Source.Derives双条件。有限前提表保持原顺序与全部成员，未将合取改成析取。

OriginalRuleHeadVariables逐条核检查锁定的28条原规则，证明每个赋值变量均出现于其真实head。因此从原head图推出每个赋值分量的原搜索界；实际环境自然性、head与原guards仍明确保留。由此对每条实际原规则，TracedMatrix可产生原application、原完整表一步及真实Trace。rule／Expr只索引固定有限源语法模式；不是对任意内部rule码的通用执行／编译正确性。

## 参数列表完整分派与正向引入

在Omega及真实五字段kind2行守卫下，原完整28规则表的一步当且仅当原nilArguments／consArguments两条规则的步骤。其余26条由实际外标签不等在对象核中排除，原表没有被截短或替换。共享V上的Trace进一步双向对应这两条规则的步骤。

nil引入保留原arity=3自然赋值、真实head图及原mode<4守卫；尚未将Num0／Num3时的守卫义务全部消去。cons引入保留原arity=7自然赋值及真实head图，其两个真实前提分别是kind1项行和kind2尾列表行。两个前提各自拥有任意内部原轨迹即可实际组合；无需预先假定它们共享同一轨迹集合。也提供给定两个实际前提行值／Expr图时的引入接口。

这些是原局部规则的完整分派和正向轨迹定理，不是尚未实现的nil／cons输出精确方程或全内部参数列表归纳。

## 模块与验收

| 模块 | 内容 |
|---|---|
| HornUniversalTraceSyntax／Value | 原Trace分离矩阵、实际集合存在、成员双条件、每个闭轨迹包含关系 |
| HornUniversalTraceClosed | 实际共享集合闭合、原一步展开双条件 |
| HornUniversalTraceRules | 原真实前提／局部矩阵双条件及共享轨迹组合 |
| OriginalRuleHeadVariables | 原28规则逐项head变量覆盖，实际搜索界义务消去 |
| OriginalArgumentsClasses／Dispatch | 原kind2完整分类及两条原规则的精确对象分派 |
| OriginalArgumentsTraceRules | 实际nil／cons轨迹引入及两个子行值接口 |
| ObjectOriginalArgumentsTrace | 11组闭句的Source.Derives→TheoryTransport→ZFReplay |

1369构建任务、15056项审计（378无公理／14678允许依赖）、零警告；九命令及五trust=0入口全部退出0；1233份工作区独立哈希一致、1662对精确证书足迹、12712项Internal显式声明覆盖。

新增9模块89声明、11组闭句和11对精确证书。核心严格为std3，native严格为std3加原七固定证书依赖。全部38项执行定义直接oracle检查通过；新三个Traced定义不引用旧项／列表变换规格或宿主求值。Value是分离见证公式，与独立执行定义分开审查。

七个理论／规则／工具链锁、隔离Choice桥和固定YesMetaZFC提交039c8e132cc19671d73a3933c66b4799d2599dd6的干净状态不变。LEAN_NUM_THREADS=1且Lean/Lake串行；定向构建与C:/Python314/python.exe -X utf8 scripts/verify.py均退出0，五个入口均使用--trust=0。实际命令在本地verification/commands.json，独立回读在verification/original-arguments-readback.json。

未运行OpenAI全仓构建、Comparator、推送或PR。

## 下一步和仍未完成的总门

下一门为原nil／cons局部矩阵及任意内部候选输出的精确方程，实际Num0／3守卫、原结构列表码和前提行存在；再用对象内部成员／长度归纳与已验收项桥连接完整参数列表，继续原kind3十一分支和量词深度后继。

全内部参数列表归纳细门明确为false。扩展语言quotation总桥、原完整数值Option接口、全mode0／3公式、原规则5／4兼容且无FreeClosed、专用ProofZF/U纯AST与全内部检查／编译、完整内部解释及最终Con均仍未完成。
