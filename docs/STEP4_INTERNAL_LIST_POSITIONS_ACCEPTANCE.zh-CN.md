# 全内部原迹位置与真实tail求值验收

日期2026-10-22；分支migration/yesmeta-step3；本批基点76e52dda0e04cabfa967afab13df9cdab7ea55ca。
本批关闭4b.c.4c.iv.b.ii.b；实际完整有序head字段图及编码/解码往返尚未完成。

## 对象合同与全位置公式

语言仅含等词与∈，背景原ZF，不新增对象Choice、Con或模型存在假设。
使用Source.Derives (Source.SetLanguage.ZF.at n)，经TheoryTransport/ZFReplay取得
原FirstOrder.Derives nativeZF []完整闭句，原核和固定依赖不改。

Positions(w,l,f,n,r):=∀k∀y(((k∈w∧Sum(w,r,k,l))∧edge(f,k,y))→Iteration_tail(w,n,r,y))。
Ω(w)、原完整sequence(f,d,w)、全部Links(w,l,f)、末边edge(f,l,n)下，
对每个内部r∈w实际证明Positions。无需预设f来自宿主List。
给原完整Trace及r,k∈w、Sum(w,r,k,l)，对任意内部对象y证明精确双条件：
edge(f,k,y)↔Iteration_tail(w,n,r,y)。

对原迹每个k∈d，还实际构造：
∃r((r∈w∧Sum(w,r,k,l))∧∀y(edge(f,k,y)↔Iteration_tail(w,n,r,y)))。
原后继域给k≤l，域/ω传递性给k∈w，已证全内部自然差实际提供反向索引r。
差存在性、标准性和位置对应均未作为额外闭句前提。

## 证明与实际见证

原Separation支持的对象ω归纳作用于取尾次数r，包含外部看来非标准的ω成员。
零点：0+k=l经实际加法零律给k=l，原完整图单值性对齐末边与种子，再实际构造零步求值。
后继：实际原加法前驱给q=r+k且l=Succ(q)，故k∈l；原Links实际取得后继索引j和两个图值a,b。
加法后继交换给r+j=l，归纳假设取得真实tail第r值b；原Cons行反向投影给b→a。
原完整图单值性使a等于待证明边值y，实际递归存在性和单值性构造第Succ(r)值y。
全部行索引、两个值、head、算术前驱和递归图都保留内部存在见证。

反向：r+k=l给k≤l及k∈d，原完整函数图实际取得k处有界唯一值。
前向对应和真实递归单值性把该值与任意给定求值y对齐，再用原对象等词替换取得edge(f,k,y)。
最终闭句中没有归纳性质或语义满足关系作为前提。

| 模块 | 实际职责 |
|---|---|
| StructuralListPositionLogic | 实际零点/后继求值构造，原Cons行反向为tail投影 |
| StructuralListPositionArithmetic | 真实加法前驱、严格旧索引界及两个后继索引交换 |
| StructuralListPositionSyntax | 全位置性质、纯矩阵、实际反向索引与全输出双条件见证 |
| StructuralListPositionBase/Step/Induction | 末边零点、原相邻行实际后继步、全内部ω归纳 |
| StructuralListPositions | 原完整迹的前向/反向/双条件及每个域内位置的实际反向索引 |
| ObjectStructuralListPositions | 八个闭句/模式的源ZF/sourceZF原核核心/原nativeZF证书 |

## 完整闭句或模式

| 句子 | 内容 |
|---|---|
| reverseStepSentence | 自然旧值及原Cons行→实际反向tail步；无需Ω |
| advanceSentence h | Ω、自然前索引、实际后继、真实旧求值和投影步→真实后继求值；head/tail两实例 |
| oldIndexSentence | Ω、r,k∈w、s=Succ(r)、s+k=l→k∈l |
| swapSentence | 上项及j=Succ(k)→r+j=l |
| allPositionsSentence | Ω、原完整序列/Links/末边、r∈w→完整Positions性质 |
| atSentence | Ω、原完整Trace、r,k∈w、r+k=l、原边→真实tail第r求值 |
| iffSentence | Ω、原完整Trace、r,k∈w、r+k=l→原边与真实tail第r求值的精确双条件 |
| reverseExistsSentence | Ω、原完整Trace及k∈d→实际内部自然反向索引和所有输出对象的精确双条件 |

每项有source_*、*_kernel_certificate及native_*；共九个闭句实例。
CheckStep4核对真实反向见证的完整AST、闭句无归纳假设、差存在性已消去及全部原nativeZF端点。

## 实际验收

C:/Python314/python.exe -X utf8 scripts/verify.py退出0；九条正式命令均退出0。
LEAN_NUM_THREADS=1；lake --no-cache --wfail build完成461个任务。
Check、CheckStep2、CheckStep3、CheckStep4和Audit均以--trust=0通过。
3916项声明审计：201项无公理依赖，3715项允许依赖；0警告。
8个新模块68项声明全部显式审计；Internal具名声明覆盖门禁累计1601项。
430份源码SHA256独立复核一致，差异0；累计131对核心/native证书或模式精确依赖核对通过。
本批八个核心恰为标准三项；native端点恰额外继承七个原有ZF闭性证书。
原choice额外证书限域、两份可信基JSON、原19规则/九类源ZF、固定依赖和原核保持不变。
未新增自定义公理，未推送；原OpenAI完整构建和Comparator未运行。
本地回读verification/internal-list-positions-readback.json；日志/依赖/哈希仅本地保留。

下一关定义Field(w,n,i,y):=∃t(Iteration_tail(w,n,i,t)∧Step_head(w,t,y))，
证明实际总单值与原Cons零/后继关系，再以原Replacement收集全部实际Kuratowski索引对，
取得完整functionOn、精确全边式、ω值域与唯一性，然后证明原顺序编码/解码往返。
全部位置对应不替代实际完整字段图；字段图、往返、树、ProofZF/U与最终内部Con仍未完成。
