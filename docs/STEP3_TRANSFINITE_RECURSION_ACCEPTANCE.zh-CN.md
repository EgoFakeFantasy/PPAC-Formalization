# 全部内部原序数上的完整对象递归存在唯一验收
日期：2026-10-21；基点a953e84a3801f5fd4a3b4956d51a259b8b256288。
分支migration/yesmeta-step3；秩/累积层及最终内部Con主句仍未完成。

## 已完成的全对象模式
对每个任意p : Source.Formula(n+3)及任意有限参数数目n，ObjectTransfiniteRecursion给出真实原核证书：
FirstOrder.Derives nativeZF [] (Translation.sentence (existenceSentence p))及相应uniquenessSentence。
完整对象内容是关闭所有参数后的
Total(Φ)→Deterministic(Φ)→∀α[Ord(α)→∃!f Recursor(Φ,f,α)]。
唯一性明确写成∃f[Recursor(f,α)∧∀g(Recursor(g,α)→g=f)]，存在的是真实内部集合图。
Total和Deterministic只要求有效Ord(x)且完整FunctionOn(h,x)输入上的总单值性，均为对象蕴含前提。
Recursor严格保留原完整functionOn和∀x∈α∀y[Edge(f,x,y)→∃h(Restrict(h,f,x)∧Φ(x,h,y))]。
Ord保持与原Source.ordinal严格相同的传递性、严格线性及全内部非空子集极小元条件。
∀α量化全部内部原序数，未限制外部标准、有限、可数或某个外部高度。
外部p/n只是有限公式及参数数目的模式索引，不引入对象统一真值谓词。

## 原Replacement实际收集前驱图
Predecessors(Φ,α) := ∀β∈α RecursorExists(Φ,β)。
在原Ord(α)下每个β∈α是原序数；上批实际后继扩展及唯一性给唯一的图gβ，
其实际域s满足Succ(s,β)并满足完整Recursor(gβ,s)。
OrdinalRecursionCollection将该唯一纤维代入原完整Replacement矩阵successorMatrix(p)，实际取得集合C。
Range(C,α)精确为∀g[g∈C↔∃β∈α SuccessorGraph(β,g)]；Coverage另行证明为
∀β∈α∃g∈C SuccessorGraph(β,g)，没有把所有候选图预先当作集合或宿主选择一族图。
OrdinalRecursionFamilyMembers实际消去每个族成员的β和s见证；Ord(α)给s为原序数且s⊆α。
任意两成员的实际递归域都为原序数，调用上批任意域递归图相容性，实际推出全族相容。
C允许为空；精确像和覆盖都量化全部内部前驱，不只外部标准实例。

## 并图的精确域和每个历史方程
原Union实际取得g=∪C。
由任意码z∈g所属的实际族成员及其完整entriesOn，结合该成员域s⊆α，证明g中没有域外杂项。
对任意β∈α，Coverage提供对应后继图，其域包含β；原完整函数图给实际输出，并经Union传到g。
全族相容给这些实际输出唯一，因此直接得到原完整FunctionOn(g,α)，不是先假定并图域为α。
GraphFamilyRestriction对任意内部相容图族证明：并图限制到某成员的完整域时恰为该成员。
该证明保留完整entriesOn，以Kuratowski编码与实际输出存在/唯一性核验反向成员包含。
对g的每条输出边，OrdinalRecursionUnion消去所属族成员h及其实际域s；
h的递推条件提供历史k，精确成员限制h=g↾s和x⊆s通过限制复合把同一k传到g。
因此所有历史及Φ方程均保持，不只证明逐点值一致或并图是函数。

## 全内部存在和唯一的装配
令P(α):=Ord(α)→RecursorExists(Φ,α)，existenceMatrix(p)为其纯对象矩阵。
在对象全体集合归纳的进步步中，若Ord(α)，则对每个β∈α由原序数成员闭包和归纳前提取得实际前驱图。
上述Replacement收集及实际并图证明给出α上的实际Recursor，故P进步。
SetInduction.all_holds使用已证明的源Replacement版ZF传递覆盖及相应Separation实例，取得∀α P(α)。
没有调用宿主WellFounded.rec、外部序数归纳、模型外部标准性或对象AC。
OrdinalRecursionUnique再由已经证明的同域唯一构造每个内部α的真实唯一纤维。
空域、后继域和极限域由同一任意内部族路线覆盖，不另假定零图存在或一族前段图可被宿主选出。

## 四个公开模式及具体无残留前提实例
| 模式 | 对象内容概要 |
|---|---|
| collectionSentence p | Total→Deterministic→Ord(α)→Predecessors(α)→∃C[Range(C,α)∧Coverage(C,α)] |
| unionSentence p | Deterministic→Ord(α)→[Range(C,α)∧Coverage(C,α)]→RecursorExists(α) |
| existenceSentence p | Total→Deterministic→∀α(Ord(α)→RecursorExists(α)) |
| uniquenessSentence p | Total→Deterministic→∀α(Ord(α)→∃!f Recursor(f,α)) |

每个实例都有source_*、*_kernel_certificate及native_*。
所有source_*均在原Source.SetLanguage.ZF的Replacement呈现内证明；该源理论没有Collection构造子。
原YesMetaZFC回放使用既有ZFReplay，不增加语言、推导核或公理。
collectionSentence的名称指递归图收集辅助模式，不是反向完整Collection公理已证明。
OrdinalRecursionContext.Evidence只包装Extensionality/Foundation/Pairing/Union及一个agreementSeparation的实际Derives证书；
类型、构造子和所有投影均列入审计，不包含递归存在、相容、覆盖或集合收集结论。

ObjectTransfiniteRecursionIdentity取Φ(x,h,y):=y=x。
原逻辑规则实际证明其Total及Deterministic，再消去两个蕴含前提，得到
∀α[Ord(α)→∃!f Recursor(Φ,f,α)]的无残留总性/单值性前提闭句及原核证书。
它检验框架可以实例化成真正的对象存在定理；没有将该简单实例当作秩或最终一致性定理。

## 实际验收
C:/Python314/python.exe -X utf8 scripts/verify.py退出0；8条正式命令全部退出0。
Lean4.33.1，LEAN_NUM_THREADS=1；lake --no-cache --wfail build完成236个任务。
19源规则、9类源ZF及锁定SHA核对通过；Check/CheckStep2/CheckStep3/Audit均以--trust=0通过。
审计1646个声明：133个无公理依赖，1513个记录允许依赖；0条Lean警告。
新增108个审计声明，其中2个无公理依赖；四个通用模式及具体实例的源ZF像原核证书逐项核对仅有propext/Classical.choice/Quot.sound。
nativeZF回放仍继承底座七个固定公理句子FreeClosed证书的native_decide.ax_1基线，未增加自定义公理。
203个验收文件哈希复核一致；没有新增sorry/admit、unsafe或外部良基/标准性前提。
CheckStep3直接检验原Source.ordinal和全内部全称-存在量词，任意矩阵、双参数交错量词矩阵、无参数矩阵及消去前提的具体实例。
定向编译修正未用化简项、族合取的存在引入归一化、显式通用并集引理导入及entriesOn投影；最终全验收通过。
verification/保留实际命令、日志、依赖和源码哈希；未推送远端。

## 全目标仍未完成
本批完整对象超限递归模式已经完成，不能再把它标成仅给定图唯一或仅后继存在。
下一项用实际PowerSet/Replacement/Union构造历史值幂集像算子的总单值性，实例化递归取得实际Vα，再证明层单调、传递及全体集合秩覆盖。
全局ω函数图、最小传递闭包、反向完整Collection、两种AC等价、内部ProofZF/U/Con完整AST、
任意内部码编译器正确性、对象解释/对称强迫及最终Derives nativeZF [] (Con_ZF→Con_target)仍未实现。
OpenAI原4.34.1构建和Comparator仍未运行；PP/AC相对一致性最终定理未完成。
