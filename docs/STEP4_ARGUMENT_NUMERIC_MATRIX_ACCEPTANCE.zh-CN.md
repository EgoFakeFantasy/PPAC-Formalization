# 原参数列表数值局部矩阵验收

基点：0fa0c754c8b4613ff2e3ba82dba9bbd00b4c508e。完成S3.4c.2b.2c.3c.2c.2b.1：原nil／cons局部矩阵、实际mode0／3守卫及所有候选行的数值结构双向对应。本批仍显式保留自然赋值与真实候选行前提；未完成赋值块消去、整体参数列表运行或内部列表归纳。

## 对象合同

语言固定纯等词／成员签名，背景固定原nativeZF完整Collection呈现，推导固定原FirstOrder.Derives。最终仍要求Derives nativeZF [] (Con_ZF → Con_target)，目标ZF+PP+ACwo+¬AC。内部Con量化全部内部ω证明码，原六规则／27模式及完整Separation／Collection不变。

本批所有模式数值、深度、参数、列表组件、输入／输出及行码是对象变量。固定kind与Bool仅索引有限原语法模式。实际原表达式图、原规则及此前原完整轨迹定义保持不变；未使用宿主列表值、标准ω、选择前提或新推导核。

## 原数值行与两个子前提

```text
Row_k(w,μ,d,p,n,q,r) := Constructor_5,k(w,[μ,d,p,n,q],r)
Run_k(w,μ,d,p,n,q) := ∃r (Row_k(w,μ,d,p,n,q,r) ∧ OriginalTrace(w,r)).
```

OriginalTransformRowSyntax只使用实际原构造器和完整原闭轨迹，不引用项程序、旧替换规格或宿主算子定义执行。两个新增执行定义均参加直接oracle检查，连同已有38项共40项。

原nil的head字段为[μ,d,p,Nil,Nil]；原cons的head字段为[μ,d,p,Cons(h,t),Cons(H,T)]。OriginalArgumentsExpr为真实原head给出原核可检查的rfl对应，然后以任意内部字段图证明head表达式与原五字段构造器的双条件。

cons的两个真实原前提分别对应Row_1(w,μ,d,p,h,H,r₁)和Row_2(w,μ,d,p,t,T,r₂)。存在同余将其TracedPremise双向变成Run_1和Run_2；中间r₁、r₂始终由对象存在量词约束，不预给内部行码或宿主求值结果。

## 原nil守卫的实际消去

原nilArguments需要自然arity=3赋值及mode<4守卫。本批在对象ZF中实际取得数码4，用原比较守卫图双条件和内部数码严格成员关系，证明Num0／Num3的模式数值满足此守卫。深度和参数自然性仍由原EnvNat保留；不因nil输出忽略参数就删除自然赋值要求。

原空列表表达式Expr.list([])对任意内部候选y等价于NilCode(w,y)。证明实际取得空森林值，借原表达式求值唯一性将其传到候选y，没有提前假设y本来是Nil码。

## 全部候选行的精确局部方程

在Omega(w)、原EnvNat₃(μ,d,p)、Num0／Num3(μ)及真实候选Row_2(w,μ,d,p,n,q,r)下：

```text
TracedMatrix(nilArguments,w,r,[μ,d,p])
 ↔ NilCode(w,n) ∧ NilCode(w,q).
```

在Omega(w)、原EnvNat₇(μ,d,p,h,t,H,T)及真实候选Row_2(w,μ,d,p,n,q,r)下：

```text
TracedMatrix(consArguments,w,r,[μ,d,p,h,t,H,T])
 ↔ (ConsCode(w,h,t,n) ∧ ConsCode(w,H,T,q))
   ∧ (Run_1(w,μ,d,p,h,H) ∧ Run_2(w,μ,d,p,t,T)).
```

n、q不预设为Nil／Cons，输出不预设为合法项列表。正方向从真实head字段恢复原Nil／Cons表达式图，再证明结构码谓词；两个子轨迹作为合取完整保留。反方向用实际结构码恢复真实head图／原guard／原前提，返回整个局部矩阵。

另有在已给结构码时的完整数值矩阵双条件，以及实际通用轨迹集合V处的原HornRuleSyntax.matrix双条件。本批使用的是原局部矩阵的实际纯语言编译，不把新数值对照关系作为原执行定义。

## 实现与实际验收

| 模块 | 内容 |
|---|---|
| OriginalTransformRowSyntax | 原五字段行／存在运行、重命名和引入 |
| OriginalArgumentsExpr | 原head及两个前提的真实语法等式、字段数值图对应 |
| OriginalArgumentsModeGuard | 原nil mode<4的对象数码守卫消去 |
| OriginalArgumentsRuleMatrix | 两个子轨迹、完整nil／cons矩阵及原矩阵双条件 |
| OriginalArgumentsNilValue | 原空列表表达式对任意候选的精确Nil码对应 |
| OriginalArgumentsRowCases | 不预给输入／输出结构合法性的候选行局部方程 |
| ObjectOriginalArgumentMatrix | 11组Source.Derives→TheoryTransport→ZFReplay闭句证书 |

1376构建任务、15129项审计（378无公理／14751允许依赖）、零警告；九命令及五trust=0入口全部退出0；1240份工作区独立哈希一致、1673对精确证书足迹、12785项Internal显式声明覆盖。

新增7模块73声明、11组闭句及11对精确证书。核心严格为std3，native严格为std3加原七固定证书依赖。七个理论／规则／工具链锁、隔离Choice桥及固定YesMetaZFC提交039c8e132cc19671d73a3933c66b4799d2599dd6的干净状态不变。

严格串行Lean/Lake、LEAN_NUM_THREADS=1。定向lake --wfail build PPAC.Migration.Internal.ObjectOriginalArgumentMatrix及C:/Python314/python.exe -X utf8 scripts/verify.py均退出0；五个入口使用--trust=0。实际命令在本地verification/commands.json，独立回读在verification/argument-matrix-readback.json。未运行OpenAI全仓构建、Comparator、推送或PR。

## 下一门

下一步消去原arity=3／7赋值存在块，对齐原模式／深度／参数字段并实际消去预给根行，取得全内部nil／cons整体运行方程；然后在原结构列表上做对象内部成员／长度归纳，接已验收项桥，再推进kind3十一公式与量词深度后继。

当前给定候选行和自然赋值的局部双条件不能替代上述整体方程或任意内部列表归纳。全内部列表归纳细门仍为false；扩展语言quotation总桥、全原数值接口、原规则5／4兼容且无FreeClosed、专用ProofZF/U及全内部检查／编译、内部解释和最终Con仍未完成。
