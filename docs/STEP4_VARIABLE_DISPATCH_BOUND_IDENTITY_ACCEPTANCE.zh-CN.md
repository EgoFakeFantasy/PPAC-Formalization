# 原完整规则表变量分派及绑定变量轨迹双条件验收

基点：30a6407ce67ff74d02b405765d8e38f7cbaec591。本批完成S3.4c.2b.2c.3c.2b.1：完整原表的mode0／3变量精确分派，以及两个绑定变量分支在合法原行上的全部内部轨迹恒等双条件。自由变量两支的完整数值对应、原扩展语言quotation总桥和最终Con仍未完成。

## 对象合同及量化范围

背景固定原nativeZF的完整Collection呈现；对象签名只有等词／成员。目标理论仍为ZF+PP+ACwo+¬AC，最终必须交付原FirstOrder.Derives nativeZF [] (Con_ZF → Con_target)。内部Con量化全部内部ω证明码，保持原六规则／27模式以及完整Separation／Collection，不添加选择、模型标准性或可数传递模型前提。

令Ctor5_1(w,xs,r)为原五字段tag1行，xs的顺序是mode、depth、parameter、input、output；Code_b(w,i,input)为原绑定／自由变量码。three是外部固定模式索引，mode(false)=0、mode(true)=3；bound=true表示绑定变量。所有w、r、R、idx及xs字段均由对象量词量化，不要求输入是宿主Nat/List，也不要求轨迹在外部有限。

本批主分派合同：

```text
Omega(w) ∧ Ctor5_1(w,xs,r) ∧ Num_mode(three)(xs[0]) ∧ Code_bound(w,idx,xs[3])
  ⊢ OriginalStep(w,r,R) ↔ Application(chosen(three,bound),w,r,R).

chosen(false,true)  = 原boundIdentity 0
chosen(true,true)   = 原boundIdentity 3
chosen(false,false) = 原freeWeaken
chosen(true,false)  = 原freeReplace.
```

同样取得原实际S(row)搜索的分派双条件，以及两个方向否定后的候选拒绝双条件。拒绝双条件指同一个候选行／轨迹上的原步骤和选中规则应用同时不成立，不声称已证明自由变量无输出的完整数值规格。

绑定变量的更强合同，在上述bound=true守卫下成立：

```text
Trace(w,r) ↔ xs[4] = xs[3]
ActualPowerTrace(w,r) ↔ xs[4] = xs[3]
¬Trace(w,r) ↔ ¬(xs[4] = xs[3]).
```

Trace量化任意内部R⊆w，并要求r∈R及完整原表闭合；ActualPowerTrace使用实际P(w)和原后继搜索接口。这里没有预给原头表达式的Graph证明：反方向实际从五字段、原输入变量码及等词重新构造原head图、实际有界赋值和闭轨迹，因而比上一批仅有原headGraph前提的正分支更强。

## 实现与证据

| 模块 | 实际对象推导／用途 |
|---|---|
| HornNodeDisjoint | 将原节点标签排斥推广到任意两个不同固定标签，保留原数码／原raw节点，不增加新的判定关系 |
| HornRowFields | 实际在对象量词内取得五个表达式值，用原构造器对应及字段单射恢复每个原头字段的Graph |
| OriginalScalarClasses | 对原28条Rule逐项给出头标签、模式字段、保留规则三分的核检查语法证据；再核对选中的三条中变量／application输入标签。仅分类外部固定原AST，不计算内部运行值 |
| OriginalModeDispatch | 不同头标签／不同内部模式数码的对象反证；完整原表在mode0／3行上与三条原规则精确等价 |
| OriginalVariableDispatch | 从原输入Code的实际scalar见证取得变量标签；排除application标签2及错误绑定／自由标签，证明四个唯一规则的全表、实际搜索、候选拒绝和闭轨迹成员应用 |
| HornVariableExpr | 从实际内部scalar／变量码构造原varCode表达式图；actual_expression逐Bool证明与原构造完全相同 |
| OriginalBoundIdentity | 原绑定恒等应用的输出码相等；任意闭轨迹可靠性；由原行／变量码／输出相等反构造原head及实际闭轨迹；实际幂集域和拒绝双条件 |
| ObjectScalarDispatch | 16组对象闭句，经Source.Derives、TheoryTransport、ZFReplay回到原nativeZF |

原完整规则表未改动。OriginalScalarClasses中的Prop分类只证明固定原AST的有限语法事实；排除错误分支和恢复字段使用Source的原推导规则，最终均返回原Hilbert核证书。绑定恒等的可靠性通过任意闭轨迹的根成员原步骤、全表精确分派及原表达式单值性取得；完备性从原变量码实际构造原Expr，推出原搜索赋值界，并复用已经验收的原根行插入及规范轨迹。

## 实际验收

1334构建任务、14599项审计（375无公理／14224允许依赖）、零警告；九命令及五trust=0入口全部退出0；1198份工作区独立哈希一致、1597对精确证书足迹、12255项Internal显式声明覆盖。新增8模块103声明、16组闭句及16对精确证书，核心为std3，原native证书为std3加原七证书依赖。七锁、隔离Choice桥、固定YesMetaZFC提交039c8e132cc19671d73a3933c66b4799d2599dd6及干净依赖状态不变。新模块没有直接调用宿主Expr.eval或SyntaxTransform.lookup／boundValue／freeValue。

本地证据：verification/commands.json、verification/scalar-dispatch-readback.json。全程LEAN_NUM_THREADS=1，Lean/Lake串行；使用lake build --wfail定向构建后执行C:/Python314/python.exe -X utf8 scripts/verify.py。未运行OpenAI原仓完整构建或Comparator，未推送、未创建PR。

## 后续工程门

下一步完成原freeWeaken／freeReplace分支的全部内部可靠性、反向、失败／无输出与独立数值规格对应。复用本批field_graph恢复parameter、index、input／output码，必须处理原lookup子行及正确的拒绝条件；不能用正分支或相同候选的否定双条件冒充无输出定理。

原BasicSetTheory扩展签名与纯成员签名的函数图消去／quotation桥仍待完成，不能直接添加扩展算术理论公理。随后仍需原十一公式递归（量词深度+1）、原规则5／4且无FreeClosed前提、专用ProofZF/U纯AST、全部内部ω检查／编译、完整L／对称扩张内部解释，最后原内部Con蕴含。本批四个细门为true，完整原数值接口、完整模式0／3、Proofchecker／解释／Con总门保持false。
