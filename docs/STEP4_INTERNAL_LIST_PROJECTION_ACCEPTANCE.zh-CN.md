# 原Cons内部投影与实际递归验收

日期2026-10-22；分支migration/yesmeta-step3；本批基点857dbd234816fdcc359fdb6484d620ea62a82d27。
本批完成4b.c.4c.iv.b.i，尚未完成原列表迹对齐、实际有序字段图及往返。

## 对象合同

语言仅含等词和∈，背景仍为原ZF；不新增对象AC、Con或模型存在假设。
使用Source.Derives (Source.SetLanguage.ZF.at n)，经TheoryTransport和ZFReplay得到
FirstOrder.Derives nativeZF []完整闭句。原核和固定依赖不改。

外部head:Bool只选择两个纯公式模式实例，不作为对象量词或新增语言符号。
Selected_head(w,x,y):=∃a((y∈w∧a∈w)∧Cons(w,y,a,x))。
Selected_tail(w,x,y):=∃a((y∈w∧a∈w)∧Cons(w,a,y,x))。
HasCons_h(w,x):=∃y Selected_h(w,x,y)。
Step_h(w,x,y):=Selected_h(w,x,y)∨(¬HasCons_h(w,x)∧Empty(y))。

总性量化所有内部集合输入，不假定x自然或有效列表。
有Cons分解时使用实际分量见证；否则使用Ω中实际空集。Cons输入单射性给分量单值，
两个跨分支组合由HasCons与其否定排除；空集分支由原Extensionality唯一。
所有分支的实际输出均属于w。已知自然Cons返回精确head/tail；Nil与Cons互斥，故Nil返回空集。

## 实际递归

matrix_h为Step_h的纯公式，参数w保持对象槽。
原自然递归关系总性和单值性均由本批对象推导消去，没有作为最终闭句的额外前提。
recursors_h(w,a)取得每个原内部序数域上的实际唯一原递归图。
Iteration_h(w,a,r,y)严格为NaturalEvaluationSyntax.evaluation matrix_h：
存在实际域d和图f，Succ(d,r)、原完整recursor(f,d)及edge(f,r,y)成立。

Ω(w)和r∈w下，任意内部集合种子a都有实际唯一y，比较所有具有真实求值见证的内部候选。
若r为空，y=a；两个相邻自然索引的实际求值u,v满足Step_h(w,u,v)。
a∈w时全部求值属于w。没有宿主递归函数、外部标准长度或模型外部良基性假设。

| 模块 | 实际职责 |
|---|---|
| StructuralListProjectionSyntax | 原Cons分量顺序、双分支投影、参数/递归/真实求值/唯一纤维纯公式及重命名 |
| StructuralListProjection | 全内部集合总单值、ω值域、Cons精确分量及Nil/非Cons空值 |
| StructuralListProjectionRecursion | 原递归义务实际消去、实际唯一图/值、零点/后继/范围 |
| ObjectStructuralListProjection | 11个完整闭句模式及源ZF/sourceZF原核核心/原nativeZF证书 |

## 完整闭句模式

| 模式 | 量词闭合前的内容 |
|---|---|
| totalSentence | Ω(w)→∀x∃y Step_h(w,x,y)，输入为任意内部集合 |
| functionalSentence | Ω(w)→∀x∀y∀z(Step_h(w,x,y)→Step_h(w,x,z)→y=z) |
| rangeSentence | Ω(w)→∀x∀y(Step_h(w,x,y)→y∈w) |
| consSentence | Ω(w)、h,t∈w、Cons(w,h,t,n)、Step_h(w,n,y)→y为该模式选择的实际分量 |
| nilSentence | Ω(w)、Nil(w,n)、Step_h(w,n,y)→Empty(y) |
| offConsSentence | ¬HasCons_h(w,x)、Step_h(w,x,y)→Empty(y)，无需Ω |
| recursorsSentence | Ω(w)→所有原内部序数域上的实际唯一递归图，无额外算子前提 |
| fiberSentence | Ω(w)、r∈w→任意种子a的实际唯一求值纤维，无额外算子前提 |
| closureSentence | Ω(w)、a∈w、Iteration_h(w,a,r,y)→y∈w |
| zeroSentence | Empty(r)、Iteration_h(w,a,r,y)→y=a，无需Ω |
| nextSentence | Ω(w)、r∈w、Succ(s,r)、两条实际相邻求值→Step_h(w,u,v) |

每个模式有source_*、*_kernel_certificate和native_*。CheckStep4核对head/tail原Cons分量顺序、
无Cons回空集分支、实际求值定义及纤维无额外算子前提，并逐一检查两个方向共22个原nativeZF实例。

## 实际验收

C:/Python314/python.exe -X utf8 scripts/verify.py退出0；九条正式命令均退出0。
LEAN_NUM_THREADS=1；lake --no-cache --wfail build完成442个任务。
Check、CheckStep2、CheckStep3、CheckStep4和Audit均以--trust=0通过。
3762项声明审计：201项无公理依赖，3561项允许依赖；0警告。
本批4个新模块86项声明全部显式审计：Syntax22、Projection12、Recursion8、Object44。
Internal具名声明覆盖门禁累计1447项；411份源码SHA256独立复核一致，差异0。
累计114对核心/native证书或模式精确核对；本批11个核心模式恰为标准三项，native模式恰额外继承原七项。
原choice额外证书限域、两份可信基JSON、原19规则/九类源ZF、原依赖和原核保持不变。
未新增自定义公理，未推送；原OpenAI完整构建和Comparator未运行。
日志/依赖/哈希与独立回读仅保留本地verification/；回读为internal-list-projection-readback.json。

## 下一关

需把tail实际求值与原构造迹逐步对齐，在已证唯一列表长度处到达Nil，
再用原Replacement取得按原字段顺序的实际完整head图，并证明唯一性及编码/解码往返。
当前全索引实际投影递归不自动给出上述有效列表字段解码定理。
完整字段图、树、专用ProofZF/U AST、内部编译器、任意内部码正确性及最终内部Con均未完成。
