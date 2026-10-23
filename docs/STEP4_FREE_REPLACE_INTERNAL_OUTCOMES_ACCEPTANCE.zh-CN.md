# 原mode3自由替换：全部内部成功图与无输出验收

基点：c0d0ef59bb5c35c07741b21fb1dc14190f94ea29。完成S3.4c.2b.2c.3c.2b.2的freeReplace单元；mode0的freeWeaken完整双向数值接口仍待完成。

## 背景与最终对象目标

对象语言保持纯等词／成员，背景为原nativeZF完整Collection呈现；目标理论为ZF+PP+ACwo+¬AC。最终仍须原FirstOrder.Derives nativeZF [] (Con_ZF → Con_target)，内部Con量化全部内部ω证明码，保持原六规则／27模式及完整Separation／Collection。本批不添加选择、模型标准性、外部有限轨迹或新推导核；最终内部Con未证明。

本批运行参数、索引、深度、行码、轨迹与输出都是对象变量，不要求来自宿主Nat／List。原固定Expr／Rule及arity只作为外部有限定理模式索引。全部新闭句沿Source.Derives、TheoryTransport、ZFReplay回到原Hilbert核。

## 原行与变量识别

HornVariableValue.graph_iff_code证明原变量Expr的图等价于实际内部变量码；原input字段与候选输入码共同恢复内部索引，未在宿主层解码运行数据。注意内部Code(true)表示绑定变量，原varCode(false)表示绑定变量，使用已证明的actual_expression保留Bool取反。

原freeReplace的实际head是kind1的五字段行：[3,depth,parameter,freeVariable(index),output]；唯一原premise是kind0查找行：[parameter,index,output]。OriginalFreeReplaceSound从原matrix及原arity=4存在块恢复三个真实字段，把原lookup子行成员与任意内部Closed(R)接入已验收查找轨迹可靠性，最终取得独立按表码递归的Executed(parameter,index,output)。R不必在外部有限，也不需要额外R⊆ω前提来证明这一可靠性。

反方向从实际原五字段行、Num3和原自由变量输入码重构原head图及全部自然赋值，调用原freeReplace正分支实际取得闭轨迹。得到原行上的完整Trace ↔ Executed，实际P(ω)轨迹与候选否定对应也已证明。

## 消去预给行码，覆盖全部内部候选

FreeReplaceResultSyntax的执行定义没有引用Executed、旧StrictLookup返回关系或宿主数值操作：

```text
Root(w,d,p,x,y,r) := ∃mode(Num3(mode) ∧ Ctor5_1(w,[mode,d,p,x,y],r))
Run(w,d,p,x,y) := ∃r(Root(w,d,p,x,y,r) ∧ Trace(w,r))
Returned(w,d,p,x,idx,y) := Code_free(w,idx,x) ∧ Run(w,d,p,x,y)
Guard(w,d,x,idx) := d∈w ∧ Code_free(w,idx,x)
HasOutput(w,d,p,x,idx) := ∃y Returned(w,d,p,x,idx,y)
NoOutput(w,d,p,x,idx) := ¬HasOutput(w,d,p,x,idx).
```

在Omega(w)这一个背景守卫下，对所有内部d,p,x,idx,y证明：

```text
Returned ↔ Guard ∧ Executed(w,p,idx,y)
Returned ↔ Guard ∧ CheckedStrictLookup(w,p,idx,y)
HasOutput ↔ Guard ∧ LookupHasOutput(w,p,idx)
NoOutput ↔ ¬(Guard ∧ LookupHasOutput(w,p,idx)).
```

没有预给行码、固定外部语法或自然输出前提。反方向实际在对象量词内取得Num3值及原行码，再取得其原闭轨迹。Guard失败时没有任何输出；非自然输出候选被拒绝。有效Guard下有输出／无输出与独立查找程序精确对应；再有parameter∈ω时，与既有严格查找返回／Rejected对应。无输出在所有内部输出上量化，区别于固定一个候选的否定对应。

输出单值性直接由原成功图到独立查找执行、再到已验收单值性取得。输出值属于内部ω；本批没有额外断言它必为合法TermCode，这取决于后续环境／公式类型检查。严格查找仍保留原访问行为：索引0可以在未访问尾部不合法时成功，未擅自加强整个参数表的合法性。

## 模块与验收

| 模块 | 实现 |
|---|---|
| HornVariableValue | 原变量图／码双向对应、输出等词传输及码自然性 |
| LookupExecutionTransport | 参数／索引／输出三个实际值的等词传输，保持原Executed定义 |
| OriginalFreeReplaceSound | 原查找前提、原局部matrix及实际四变量存在块可靠性 |
| OriginalFreeReplace | 原行上的完整轨迹双向对应、实际幂集域及候选拒绝 |
| FreeReplaceResultSyntax | 独立原成功图、实际根行、精确守卫、有输出／无输出纯公式 |
| FreeReplaceResultRows | 实际取得模式数码／原行码、深度自然性、原行轨迹判据 |
| FreeReplaceResult | 所有内部候选的精确守卫／执行／checked对应及严格自然接口 |
| FreeReplaceOutcome | 对全部输出量化的成功／失败、非法域与非法输出拒绝、单值性 |
| ObjectFreeReplace | 22组原核闭句及CheckStep4调用 |

1343构建任务、14742项审计（375无公理／14367允许依赖）、零警告；九命令及五trust=0入口全部退出0；1207份工作区独立哈希一致、1619对精确证书足迹、12398项Internal显式声明覆盖。新增9模块143声明、22组闭句及22对精确证书，核心为std3，原native证书为std3加原七证书依赖。七锁、隔离Choice桥、固定YesMetaZFC提交039c8e132cc19671d73a3933c66b4799d2599dd6及干净依赖状态不变。

在原13个轨迹执行定义禁用宿主／旧执行oracle的检查上，新增本批7个定义，合计20个定义逐项检查。此为直接引用检查；实际定义及闭句证明已另外按上表核查。规范轨迹构造和正确性证明允许引用已验收Executed，不把证明中的引用当作执行定义的oracle。

执行LEAN_NUM_THREADS=1、串行lake build --wfail定向构建，以及C:/Python314/python.exe -X utf8 scripts/verify.py。验收命令见本地verification/commands.json，独立复核见verification/free-replace-readback.json。未执行OpenAI原仓完整构建、Comparator、推送或PR。

## 剩余工程门

下一步完成mode0自由变量freeWeaken：原输入索引恢复、输出自由变量索引实际后继、任意内部轨迹双向对应和精确成功域／失败接口。随后推进全十一公式递归及量词深度+1、原规则5／4且不附加FreeClosed。

原BasicSetTheory扩展语言到纯成员签名的函数图消去／quotation总桥仍未完成，禁止直接加入其非逻辑算术理论公理。专用ProofZF/U纯AST、全部内部ω检查／编译、完整L／对称扩张内部解释及最终内部Con均待完成。本批五个细门为true，完整原数值接口、完整模式0／3及最终Con总门仍为false。
