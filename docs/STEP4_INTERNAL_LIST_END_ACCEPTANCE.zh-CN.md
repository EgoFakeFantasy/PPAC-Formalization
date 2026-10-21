# 内部递归移位与列表Nil终端验收

日期2026-10-22；分支migration/yesmeta-step3；本批基点23e9d10923250cf8f23109f3a4dd094822b31a40。
本批完成4b.c.4c.iv.b.ii.a；全部位置对应、实际完整有序字段图及往返尚未完成。

## 对象合同与真实移位

语言仅含等词与∈，背景保持原ZF，不新增对象Choice、Con或模型存在假设。
接口为Source.Derives (Source.SetLanguage.ZF.at n)，经TheoryTransport和ZFReplay得到
原FirstOrder.Derives nativeZF []完整闭句，原核及固定依赖不改。

Step_h为前批已证所有内部集合上总单值的原Cons head/tail投影；非Cons输入取实际空集。
h为两个外部公式模式索引。Iteration_h保持实际后继域、完整原递归图及实际边见证。

Coupled_h(w,a,b,r):=∀u∀v(Iteration_h(w,a,r,u)→Iteration_h(w,b,r,v)→Step_h(w,u,v))。
给定Ω(w)和Step_h(w,a,b)，对全部内部r∈w作对象ω归纳：
零点由两条求值分别等于原种子；后继步实际取得两条前驱求值。
归纳假设与第一条递归的后继方程给两种Step_h输出相等，再将第二条后继方程以对象等词替换。
原Separation归纳实例由原ZF实际消去，未在闭句中留下归纳性质假设。

由此r∈w、Succ(s,r)时，任意Iteration_h(w,a,s,y)、Iteration_h(w,b,r,z)均满足y=z，
且Iteration_h(w,a,s,y)与Iteration_h(w,b,r,y)有两个方向的实际推导。
反向方向使用真实s自然性和实际递归值存在，不以外部计算或宿主递归函数代替。
种子a,b可为任意内部集合，索引覆盖外部看来非标准的ω成员。

## 实际长度处的Nil终端与原迹恢复

Ends(w,n):=∀l∀y(HasLength(w,n,l)→Iteration_tail(w,n,l,y)→Nil(w,y))。
在内部w上沿原Cons严格尾码界作成员归纳：
Nil情形，任何实际长度为空，真实零点求值等于原码；
Cons情形，精确前缀给实际p∈w、Succ(l,p)和HasLength(w,t,p)。
已知自然Cons给真实tail步n→t，移位双条件把原n的l步求值送到t的p步，
严格尾码界t∈n允许使用归纳假设。此归纳假设也从最终闭句中消去。

因此Ω(w)下，任意实际列表长度l与真实tail求值y均满足Nil(w,y)。
给定原完整Trace(w,z,e,l,d,f,n)，原Nil唯一性给任何此求值y=e，
而实际递归存在性给Iteration_tail(w,n,l,e)，确实恢复原迹的Nil种子。
Valid(w,n)给实际内部l,y，同时满足l∈w、HasLength(w,n,l)、Iteration_tail(w,n,l,y)、Nil(w,y)。
两组实际长度/求值端点对由既有长度唯一性、索引等词替换和实际递归单值性证明相等。

| 模块 | 实际职责 |
|---|---|
| StructuralListIterationTransport | 真实求值存在唯一，种子/索引/值与投影输入/输出的对象等词替换 |
| StructuralListShiftSyntax/Step/Induction/Shift | 纯耦合公式、实际前驱值、对象ω归纳、移位等值及双条件 |
| StructuralListEndSyntax/Rules/Step/Induction | 全长度/全求值终端公式、精确前驱长度、原严格尾码成员归纳 |
| StructuralListEndExistence | 实际端点见证、端点对唯一、原迹Nil种子等值和真实恢复 |
| ObjectStructuralListEnd | 九个闭句/模式及源ZF/sourceZF原核核心/原nativeZF证书 |

## 完整闭句或模式

| 句子 | Ω(w)外的前提与结论 |
|---|---|
| coupledSentence h | r∈w、Step_h(w,a,b)→Coupled_h(w,a,b,r) |
| shiftEqualSentence h | r∈w、Succ(s,r)、Step_h(w,a,b)、两条移位真实求值→输出相等 |
| shiftIffSentence h | r∈w、Succ(s,r)、Step_h(w,a,b)→真实移位求值双条件 |
| consShiftSentence | h,t,r∈w、Succ(s,r)、Cons(w,h,t,n)→Iteration_tail(w,n,s,y)↔Iteration_tail(w,t,r,y) |
| terminalSentence | HasLength(w,n,l)、Iteration_tail(w,n,l,y)→Nil(w,y) |
| existsTerminalSentence | Valid(w,n)→实际存在内部长度/完整构造迹/真实tail求值/Nil终端见证 |
| uniquePairSentence | 两个实际长度和相应真实tail求值→两个长度相等且两个值相等 |
| traceSeedSentence | 任意原完整Trace(w,z,e,l,d,f,n)、Iteration_tail(w,n,l,y)→y=e |
| traceRecoverySentence | 任意原完整Trace(w,z,e,l,d,f,n)→Iteration_tail(w,n,l,e) |

每项有source_*、*_kernel_certificate及native_*；前三个有两个模式实例，共12个闭句实例。
CheckStep4核对Ends完整内部量词、无归纳假设的最终终端闭句、原迹种子恢复及端点的全部实际见证，
并逐一检查全部12个原nativeZF实例。

## 实际验收

C:/Python314/python.exe -X utf8 scripts/verify.py退出0；九条正式命令均退出0。
LEAN_NUM_THREADS=1；lake --no-cache --wfail build完成453个任务。
Check、CheckStep2、CheckStep3、CheckStep4和Audit均以--trust=0通过。
3848项声明审计：201项无公理依赖，3647项允许依赖；0警告。
本批11模块86项声明全部显式审计；Internal具名声明覆盖门禁累计1533项。
422份源码SHA256独立复核一致，差异0；累计123对核心/native证书或模式精确依赖核对通过。
本批九个核心恰为标准三项；native端点恰额外继承七个原有ZF闭性证书。
原choice额外证书限域、两份可信基JSON、原19规则/九类源ZF、原依赖和原核保持不变。
未新增自定义公理，未推送；原OpenAI完整构建和Comparator未运行。
独立回读位于本地verification/internal-list-end-readback.json；日志/依赖/哈希仅本地保留。

## 下一关及验收界限

先证明全部内部反向索引r+k=l下，原边edge(f,k,v)给Iteration_tail(w,n,r,v)。
零点对齐原末边；后继步用加法后继等式和原相邻Cons行反向推进；值对应仍由完整函数图单值性证明。
随后原Replacement对每个i∈l收集实际tail第i值的head输出及其原Kuratowski索引对，
证明无多余图元、完整functionOn、ω值域、原字段顺序和唯一性，再取得编码/解码往返。
当前精确端点恢复不替代上述全部位置和字段图定理。
实际完整字段图、树、专用ProofZF/U、内部编译器、任意内部码正确性和最终内部Con仍未完成。
