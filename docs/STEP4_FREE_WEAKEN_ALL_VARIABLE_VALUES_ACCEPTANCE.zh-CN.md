# 原freeWeaken全部内部后继值及四变量分支统一验收

基点：afaf2f5cc7a634b2e695c6df3b47013ccb011ac3。完成S3.4c.2b.2c.3c.2b.3：mode0自由变量分支的实际后继、全内部成功／失败，以及四个mode0／3绑定／自由变量分支的统一对象接口。未完成整个项／公式变换或最终Con。

## 对象目标保持不变

背景是原nativeZF完整Collection呈现；签名只有等词／成员；推导固定原FirstOrder.Derives。目标为ZF+PP+ACwo+¬AC，最终必须产生Derives nativeZF [] (Con_ZF → Con_target)。内部Con量化全部内部ω证明码，保持原六规则／27模式及完整Separation／Collection。不添加选择、外部ω标准性、外部有限轨迹、新推导核或模型假设。

本批所有运行值、索引、深度、参数、输出和轨迹均为对象变量。原Expr／Rule及有限Bool只索引固定原模式；Source.Derives实际构造推导，再经TheoryTransport及ZFReplay回到原Hilbert核。

## 实际后继值与原规则

```text
Shifted(w,idx,y) := ∃s (Successor(s,idx) ∧ Code_free(w,s,y)).
```

FreeWeakenValue用原Pairing／Union实际取得后继s，证明s∈ω，再实际取得原自由变量码y；没有把宿主idx+1当作内部数据。对全部内部idx，∃y Shifted恰好等价于idx∈ω。两个实际后继由原外延唯一性对齐，再调用原变量码单值性，证明所有Shifted输出相等；输出自然性及实际给定后继s处的精确Code对应也已证明。

原freeWeaken头的五字段为[0,depth,parameter,freeVariable(idx),freeVariable(succ(idx))]。OriginalFreeWeakenSound实际消去原arity=3存在赋值，用原头字段恢复及变量码单射对齐输入索引，再在对象量词内取得后继，并由原Expr图反向恢复输出码，取得Shifted。反方向从实际Successor／Code输出及原行／输入码重构原head图、原搜索赋值界和实际闭轨迹。

在Omega、原五字段tag1行、Num0及原自由变量输入码守卫下，完整原Trace ↔ Shifted；实际P(ω)轨迹及候选否定对应也已证明。轨迹不要求在外部有限。

## 全部候选成功图与真正的无输出

FreeWeakenResultSyntax只用原变量码、实际Num0／原行码及完整原闭轨迹定义Returned；不引用Shifted来定义执行，也不调用宿主操作。

```text
Guard0(w,d,p,x,idx) := d∈w ∧ p∈w ∧ Code_free(w,idx,x)
Returned(w,d,p,x,idx,y) := Code_free(w,idx,x) ∧
  ∃r (Root_mode0(w,d,p,x,y,r) ∧ Trace(w,r))
HasOutput := ∃y Returned
NoOutput := ¬HasOutput.
```

在Omega(w)这一个背景守卫下，对全部内部d,p,x,idx,y证明：

```text
Returned ↔ Guard0 ∧ Shifted(w,idx,y)
HasOutput ↔ Guard0
NoOutput ↔ ¬Guard0.
```

反方向实际取得模式数码、行码、原head图及闭轨迹，没有预给行码、预给外部语法或自然输出前提。HasOutput反方向实际取得内部后继和自由变量码，并非仅用排中划分成功／失败。NoOutput量化全部内部输出。

参数自然性不可删：虽然输出不使用parameter，原三变量EnvNat和实际原行仍强制parameter∈ω。非自然参数、非自然深度、错误自由变量输入码分别有无输出对象定理；非自然输出被拒绝。成功输出自然且唯一。实际后继s给定时，Guard0下Returned恰好等价于Code_free(w,s,y)。没有提前添加有类型上下文界或完整TermCode结论。

## 四个变量分支统一对象接口

OriginalScalarValues.valueSpec是规格公式，不是执行定义。它按固定three／bound模式选择：绑定变量为output=input；mode0自由变量为Shifted；mode3自由变量为已验收独立查找Executed(parameter,index,output)。

在原五字段行、相应Num0／Num3、原绑定／自由变量码及Omega守卫下，统一证明完整Trace ↔ valueSpec、实际P(ω)轨迹 ↔ valueSpec及候选拒绝对应。这覆盖原boundIdentity 0、boundIdentity 3、freeWeaken、freeReplace四条变量规则，供后续项／参数列表／公式证明直接调用。没有把模式1／2、完整公式递归或原规则5／4提前算作完成。

## 实现与实际验收

| 模块 | 实现 |
|---|---|
| FreeWeakenValueSyntax／FreeWeakenValue | 纯内部后继变量值、实际存在、精确自然索引域、单值性 |
| OriginalFreeWeakenSound／OriginalFreeWeaken | 原局部矩阵／arity=3应用可靠性、原完整轨迹正反方向及实际幂集域 |
| FreeWeakenResultSyntax／FreeWeakenResultRows | 独立原成功图、Num0／原行码实际构造、深度及参数自然性 |
| FreeWeakenResult／FreeWeakenOutcome | 全部内部成功域、真实存在输出、无输出、逐域拒绝、自然性及唯一性 |
| OriginalScalarValues | 原四变量规则的统一对象规格和全轨迹双向接口 |
| ObjectFreeWeaken | 28组闭句及原核证书、CheckStep4调用 |

1353构建任务、14920项审计（375无公理／14545允许依赖）、零警告；九命令及五trust=0入口全部退出0；1217份工作区独立哈希一致、1647对精确证书足迹、12576项Internal显式声明覆盖。

新增10模块178声明、28组闭句及28对精确证书；核心严格为std3，native严格为std3加原七证书依赖。七锁、隔离Choice桥及固定YesMetaZFC提交039c8e132cc19671d73a3933c66b4799d2599dd6的干净依赖状态不变。执行定义直接oracle禁用检查由20项扩展为29项，新增Shifted／HasShifted及原成功图7项；原四分支valueSpec明确是对照规格，不当作独立执行定义。

全程LEAN_NUM_THREADS=1、Lean/Lake串行；定向lake build --wfail通过后运行C:/Python314/python.exe -X utf8 scripts/verify.py。验收命令见本地verification/commands.json，独立回读见verification/free-weaken-readback.json。未运行OpenAI原仓完整构建、Comparator、推送或PR。

## 后续门

下一步接入纯签名项作用域的内部变量分支及原参数列表，再推进全十一公式和量词深度+1。当前SyntaxTermSyntax.term明确是内部contexts及bound/free变量见证的析取；后续须在相应对象守卫下实际处理／排除原application分支，不能凭纯签名名称跳过原表分支。尚未实现完整项／公式数值接口。

原扩展语言公式整体的函数图消去／quotation总桥仍未完成，不能将其非逻辑算术理论公理直接加入纯ZF。原规则5／4且无FreeClosed、专用ProofZF/U纯AST、全部内部ω检查／编译、完整L／对称扩张内部解释及最终Con仍待完成。本批六个细门为true，原完整数值接口、完整mode0／3及最终Con总门保持false。
