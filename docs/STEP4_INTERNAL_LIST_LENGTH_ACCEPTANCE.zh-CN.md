# 内部有限列表实际长度唯一性验收

日期2026-10-22；分支migration/yesmeta-step3；本批基点c3c05bb3ed46c7215c05285c2e18f3cd6f9ca1c1。
本批关闭4b.c.4c.iv.a；实际完整有序字段图及编码/解码往返尚未完成。

## 对象合同与实际长度

语言仅含等词与∈，背景保持原ZF，不加对象AC、Con或模型存在假设。
证明接口为Source.Derives (Source.SetLanguage.ZF.at n)，并实际传输至
FirstOrder.Derives nativeZF []完整闭句；不修改原推导核或固定依赖。

HasLength(w,n,l):=∃z∃e∃d∃f Trace(w,z,e,l,d,f,n)。
四个见证均为内部集合，Trace保持Empty零、Nil种子、l∈w、Succ(d,l)、完整函数图、
ω有界值、全部相邻Cons行和实际末边。
Valid(w,n)给出∃l(l∈w∧HasLength(w,n,l))，无需外部标准长度。

## 精确前缀、终端行和归纳

原valid_prefix证明提取为exists_prefix_trace，保留实际图而非仅给有效性：
Ω(w)、p∈w、Succ(l,p)、Trace(w,z,e,l,d,f,n)、edge(f,p,a)
推出∃g Trace(w,z,e,p,l,g,a)。旧valid_prefix接口作为包装保持可用。

后继长度的终端行实际存在前驱值和Cons步。若完整码已知为Cons(w,h,t,n)，
原Cons输入单射性把终端前驱值与t对齐，得到实际edge(f,p,t)。
Nil不可能有Cons终端行，因此Nil的每条迹长度为空。
Cons不可能有零长度；每条实际长度l均为尾的某个实际长度p的后继，
且实际前缀见证HasLength(w,t,p)被保留。

令Q(w,n):=∀l∀k(HasLength(w,n,l)→HasLength(w,n,k)→l=k)。
在内部w上作原Foundation/Separation支持的成员归纳。归纳步仅假设所有t∈w∩n满足Q。
Nil情形两个长度均为空；Cons情形严格尾码界给t∈n，两个实际前驱长度由Q相等，
再由原后继唯一性得到两个原长度相等。归纳假设最终被消去，不作为闭句前提。
两条迹的零、种子、域和完整图均可不同；候选长度无外部标准性限制。

## 新模块和完整闭句

| 模块 | 实际职责 |
|---|---|
| StructuralListLengthSyntax/Basic | 实际长度、前驱长度、全候选唯一性质和实际唯一纤维的纯公式；四重见证引入/消去 |
| StructuralListTerminal | 实际终端行、Nil/Cons终端互斥、已知尾的真实图边 |
| StructuralListLengthRules | Nil长度为空；Cons长度是尾的某个实际长度的后继 |
| StructuralListLengthStep/Unique | 严格尾码界、内部成员归纳、全候选长度唯一性 |
| StructuralListLengthFiber | 任意同码迹等长、每个有效码的实际唯一自然长度纤维 |
| ObjectStructuralListLength | 九个完整闭句的源ZF、sourceZF原核核心和原nativeZF端点 |

| 闭句 | Ω(w)外的前提与结论 |
|---|---|
| prefixTraceSentence | p∈w、Succ(l,p)、实际Trace及edge(f,p,a)→指定长度p和域l的实际前缀Trace存在 |
| knownTailEdgeSentence | h,t∈w、Succ(l,p)、实际Trace及Cons(w,h,t,n)→edge(f,p,t) |
| nilEmptySentence | Nil(w,n)、HasLength(w,n,l)→Empty(l) |
| consPredecessorSentence | h,t∈w、Cons(w,h,t,n)、HasLength(w,n,l)→∃p((p∈w∧Succ(l,p))∧HasLength(w,t,p)) |
| uniqueSentence | HasLength(w,n,l)、HasLength(w,n,k)→l=k |
| traceUniqueSentence | 两条任意种子、域和图的同码Trace→两个长度相等 |
| fiberSentence | Valid(w,n)→∃l((l∈w∧HasLength(w,n,l))∧∀k(HasLength(w,n,k)→k=l)) |
| rangeSentence | HasLength(w,n,l)→n∈w∧l∈w；无需Ω前提 |
| existsSentence | Valid(w,n)→∃l(l∈w∧HasLength(w,n,l))；无需Ω前提 |

每句有source_*、*_kernel_certificate和native_*，CheckStep4核对纯公式形状和九个实际nativeZF端点。

## 实际验收

C:/Python314/python.exe -X utf8 scripts/verify.py退出0；九条正式命令均退出0。
LEAN_NUM_THREADS=1；lake --no-cache --wfail build完成438个任务。
Check、CheckStep2、CheckStep3、CheckStep4、Audit均以--trust=0通过。
3676项声明审计：200项无公理依赖、3476项允许依赖；0警告。
8个新模块85项声明和原Prefix新增1项接口均进入显式Audit；合计86项。
407份源码SHA256独立复核一致，差异0。新增具名Internal声明漏审门禁覆盖1361项，
按当前单namespace文件样式识别顶层def/theorem/abbrev/structure/inductive，不宣称通用Lean语法解析。
累计103对核心/native证书精确依赖通过；本批九个核心恰为标准三项，native端点恰额外继承原七项。
原choice额外证书限域、两份可信基JSON、原19规则/九类源ZF、固定依赖与原核均保持不变。
未新增自定义公理，未远端推送；原OpenAI完整构建与Comparator未运行。
独立回读保存于本地verification/internal-list-length-readback.json，日志和审计JSON不作为发布材料。

## 剩余工作

下项先证明原Cons的head/tail投影在所有内部集合上总单值：有自然Cons输入时返回对应分量，
其余输入返回实际空集。由既有自然递归从完整码向尾递推，逐步对齐原迹，
在唯一长度处到达Nil，再用原Replacement取得按原字段顺序的完整字段图及唯一性。
这比先反转构造迹直接，但各条对应与往返仍须对象推导。
当前实际完整字段图、完整列表解码、树、专用ProofZF/U与最终内部Con均未完成。
