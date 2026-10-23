# 原列表运行与独立全内部字段像完整对应验收

基点：3363b95906335a26d805ca65c93ba815afa94553。完成S3.4c.2b.2c.3c.2c.2b.3d：原mode0／3关系式Run₂与独立项程序全内部字段像的完整双条件。覆盖一般内部长度与全部内部索引，不缩减到外部有限列表或成员原子的两个参数。

## 对象理论合同与范围

固定原纯等词／成员签名、原nativeZF完整Collection呈现及原FirstOrder.Derives。最终仍要求Derives nativeZF [] (Con_ZF → Con_target)，目标理论ZF+PP+ACwo+¬AC；内部Con的全部内部ω证明码、原六规则／27模式和完整Separation／Collection不变。最终Con未证明。

本批每组闭句均有实际Source.Derives证明，经TheoryTransport和ZFReplay取得原核原nativeZF推导。没有新对象公理、AC、标准ω、外部良基或模型前提，没有恢复退役反射。这里完成关系式有类型列表接口；原扩展语言quotation总桥、完整数值Option接口及所有非法源输入的统一拒绝接口没有据此完成。

## 独立字段像及正式双条件

令Field(w,n,i,x)为既有内部字段关系，TermProgram为既有独立纯签名项程序：

```text
RawFields(w,μ,depth,param,k,n,q) := ∀i ∀x ∀y
  ((i∈k ∧ (Field(w,n,i,x) ∧ Field(w,q,i,y)))
   → Run₁(w,μ,depth,param,x,y)).
ProgramFields(w,R,S,k,n,q) := ∀i ∀x ∀y
  ((i∈k ∧ (Field(w,n,i,x) ∧ Field(w,q,i,y)))
   → TermProgram.run(w,R,S,x,y)).
Mapped(w,R,S,k,c,d,n,q) :=
  TermList(w,k,c,d,q) ∧ ProgramFields(w,R,S,k,n,q).
```

ProgramFields／Mapped的定义不调用原Run₂、原字段正确性证明、原运行结果规格或旧变换算子；它们是独立项程序的关系式字段像规格，不冒充新列表执行器。两定义均新增直接oracle检查。目标列表类型和相同内部长度保证字段范围，反向证明还实际构造源与目标字段见证，未使用空前件伪造对应。

| 模式 | 明确对象前提 | 原核双条件 |
|---|---|---|
| mode3替换 | Omega(w)、Num3(μ)、metadata(w,depth,L)、identityCode(w,a,I)、converted(true,w,I,R,a,a,c)、参数TermList(w,b,a,c,L)、源TermList(w,k,a,b,n) | Run₂(w,μ,depth,L,n,q) ↔ Mapped(w,R,L,k,a,c,n,q) |
| mode0弱化 | Omega(w)、Num0(μ)、metadata(w,depth,param)、identityCode(w,a,I)、shiftCode(w,b,B,J)、converted(true,w,I,R,a,a,B)、converted(false,w,J,S,b,a,B)、源TermList(w,k,a,b,n) | Run₂(w,μ,depth,param,n,q) ↔ Mapped(w,R,S,k,a,B,n,q) |

q为任意内部对象，不预给自然性或目标类型；k由内部源列表类型约束，未设置外部长度界。mode3参数保持原同码L，mode0参数允许任意自然值。最终两个模式端点没有Earlier、未解Promise或agreement前提；实际环境前提继续显式保留。

## 正向：全部内部索引的对象归纳

新归纳属性对每个内部源码n量化全部内部长度k与候选输出q：源TermList及真实Run₂推出RawFields。Nil输入用实际HasLength推得Empty(k)，逐字段性质由空索引范围正式推出。

Cons运行正式消去四个内部组件，真实子运行给全部组件自然性。源列表类型给实际内部前驱长度ell及完整尾列表类型；编码的严格成员性给t∈n。归纳假设给真实尾运行的全部字段对应。

对任意内部索引i∈k，用原对象零／后继分解。零分支的两个实际字段由原Cons零字段唯一性对齐头输入／输出，再由原Run₁输入和输出等词替换给对应。后继分支实际存在内部前驱j，证明j∈ell，将源／目标字段都转到尾字段，再正式实例化尾对应。最后由原Separation／Foundation关闭成员归纳，不保留Earlier或宿主递归前提。

在实际环境下，源Field给实际源项类型；上批数值项桥对每个内部x,y证明Run₁↔TermProgram.run，从而得到RawFields↔ProgramFields的两个方向。

## 反向：实际见证及原码字段单射

先由已验收的列表Fiber实际取得原Run₂输出r及完整Value。任意真实候选运行也由该Fiber的全候选唯一性和对象等词替换取得同一候选的完整Value，因此正向目标类型对所有候选成立。

比较满足RawFields且有相同目标长度／类型的q和r：对每个内部索引实际取得源字段x和目标字段见证。源类型给Term(x)，真实对象头Promise取得实际项Value；全候选项唯一性比较q、r字段输出。对象字段输出等词替换给每个内部字段的双向等价，原StructuralListCodeInduction.unique用相同准确内部长度及完整字段等价推出q=r。再在实际Run₂(n,r)上正式替换输出得到Run₂(n,q)。

一般反向引理的Promise和目标上下文明确列为对象前提；两个模式最终特化用实际环境正式推导它们。程序字段像双条件与该原字段像双条件组合，取得上表完整端点；没有用宿主列表外延性或外部选择函数。

## 源码与闭句

| 模块 | 对象成果 |
|---|---|
| OriginalArgumentCandidateValue | 真实候选运行由实际Fiber取得完整Value |
| OriginalArgumentFieldSyntax | 全内部索引RawFields及字段归纳Property／Earlier |
| OriginalArgumentConsFields | 实际零／后继索引下的Cons字段递归 |
| OriginalArgumentFieldPoint | 实际Nil／Cons字段归纳步 |
| OriginalArgumentFieldInduction | 原Separation／Foundation关闭全部内部码字段归纳 |
| ArgumentProgramFieldSyntax | 独立项程序ProgramFields／Mapped规格 |
| OriginalArgumentProgramFields | 两个模式RawFields↔ProgramFields |
| OriginalArgumentFieldUnique | 实际字段见证、项Promise单值性及字段码单射 |
| OriginalArgumentFieldCompletion | 原Run₂与原字段像完整双条件 |
| OriginalArgumentFullProgramBridge | 两个模式的原Run₂↔独立Mapped完整双条件 |
| ObjectOriginalArgumentFields | 10组Source→原核→原nativeZF闭句 |

10组闭句：allCandidateOriginalListValue、originalAllInternalArgumentFields、originalAllInternalFieldCodeProperties、allInternalFieldImageOutputUnique、originalRunAllFieldImageIff、replaceAllInternalProgramFieldsIff、replaceWholeOriginalArgumentProgramIff、weakenAllInternalProgramFieldsIff、weakenWholeOriginalArgumentProgramIff、originalConsAllInternalFields。

## 实际验收

定向lake --wfail build PPAC.Migration.Internal.ObjectOriginalArgumentFields及C:/Python314/python.exe -X utf8 scripts/verify.py实际退出0。全仓1416构建任务、15495项审计（378无公理／15117记录允许依赖）、零警告。九命令及五trust=0入口全部退出0；Lean/Lake严格串行，LEAN_NUM_THREADS=1。

新增11模块80显式声明，10组核心证书依赖精确为标准三项，native精确为标准三项加原七固定句子证书依赖。全仓1722对精确证书足迹、13151项Internal显式声明覆盖；1280份工作区独立哈希无差异。七锁、隔离Choice桥及固定底座039c8e132cc19671d73a3933c66b4799d2599dd6的干净状态不变。

原45项执行／分支定义直接oracle检查保留，新增独立字段像两定义的直接检查通过。独立回读同时核查全部已有证书足迹和本批新定义；未扩大依赖允许范围。实际日志保留本地verification/commands.json、verification/audit.log、verification/argument-fields-readback.json。未运行OpenAI全仓构建／Comparator，未推送或创建PR。

## 门槛与下一步

全内部有类型列表变换正确性和相应原列表递归门现通过，范围就是上述实际环境／源类型守卫下的关系式双条件，不扩张到非法源、全部四模式或宿主Option评价器。独立字段像定义检查、全内部索引字段正确性、字段像两个方向及由实际原码单射取得反向四项细门通过。

下一步3e处理原完整28规则表kind3的十一公式分派与实际局部运行方程，再做3f全内部公式归纳和量词深度后继／真实环境提升。纯成员签名的relation application、符号码和实际参数列表对应须显式核查。原扩展语言quotation总桥、完整数值Option接口、原规则兼容、ProofZF/U全内部证明检查／编译、内部解释及最终Con仍未完成。
