# 实际幂集并算子与全部内部原序数的递归层值验收
日期：2026-10-21；基点6337c0fa09223e2794f92682f4cbde4f5564e60c。
分支migration/yesmeta-step3；层代数、秩覆盖及最终内部Con主句仍未完成。

## 完成范围和对象语言
对象语言仍为原单排序纯成员/等词语言，推导终点仍为实际FirstOrder.Derives nativeZF [] φ。
PowerOf(P,v) := ∀z[z∈P↔z⊆v]，闭句与原Source.powerSet由rfl严格对应；⊆仍量化全部内部集合成员。
Value(h,β,P) := ∃v[Edge(h,β,v)∧PowerOf(P,v)]。
Range(C,α,h) := ∀P[P∈C↔∃β∈α Value(h,β,P)]。
Φ(α,h,y) := ∃C[Range(C,α,h)∧UnionOf(y,C)]。
它表示历史输出各幂集组成的实际集合的并，没有增加幂集函数符号或宿主集合运算。
每条递推方程仍显式存在实际历史限制集合，完整原functionOn保留entriesOn及总单值性。
α、h、C、P、v、y及所有子集量词均遍历内部集合；不以外部标准序数、外部良基或外部可数性为前提。

## 实际幂集值与精确Replacement像
PowerSetSyntax从原PowerSet公理对任意内部v取得实际P，PowerSetLogic以原Extensionality给幂集唯一、等词传输及包含单调性。
对每个β∈α，原完整FunctionOn(h,α)给实际输出v；PowerSet提供实际P(v)。
两个输出先由图单值性取等，再用幂集外延唯一性取得P值唯一。
PowerValueSyntax.matrix保留历史图参数h和输入β、输出P，relation/unique/fiber/image/range均与原Replacement接口逐式对应。
PowerValueCollection使用这个完整Replacement实例实际取得精确Range(C,α,h)，没有仅取得含多余元素的界集合。
所有实际输出及幂集见证由原exI/exE处理，未抽取宿主选择函数，源证明没有Collection或对象AC输入。

## 具体算子总单值性及递归实例化
原Union取得y=∪C；两个Φ输出的实际像集合C、D由精确成员等价及Extensionality取等，
再由原Union唯一性得到两个实际y相等。
ObjectPowerUnion的四句有限理论只含Extensionality、PowerSet、Union以及replacement(PowerValueSyntax.matrix)。
其四个闭句是：完整历史有实际精确幂集像、完整历史有实际Φ输出、Φ在有效序数/历史输入上对象Total、Φ对象Deterministic。
未以Foundation、Pairing、Infinity、EmptySet、Collection、对象AC或预设层函数作为该有限算子理论的输入。
部分结论使用更小子集，例如Φ输出唯一只需要Extensionality；不宣称四句是每项的最小必要公理集。
HierarchyRecursion使用已实际证明的Total和Deterministic，消去通用超限递归模式的两个前提，
取得全部内部原序数上的实际递归图存在唯一，闭句中不再残留未证算子前提。

## 实际层值存在唯一与零层核验
Graph(f,s)是上述固定Φ的原完整递归图。
Layer(α,y) := ∃s∃f[Succ(s,α)∧Graph(f,s)∧Edge(f,α,y)]。
原Pairing/Union取得实际后继s，原序数后继保持性给Ord(s)，已消去前提的全序数递归取得实际f，
α∈s及完整函数图给实际y，从而得到∀α[Ord(α)→∃y Layer(α,y)]。
任意两个Layer见证的实际后继域均为原序数，原任意域递归图相容给两个α处输出相等。
因此实际证明∀α[Ord(α)→∃y(Layer(α,y)∧∀z(Layer(α,z)→z=y))]。
这只是由所给纯对象幂集并递归定义的层值存在唯一，没有先假定秩或任意集合已在某层。

PowerUnionEmpty证明：空索引的Range像为空，实际Union也为空。
HierarchyLayerZero从实际递归方程取得空索引处的Φ见证，推出空索引层值为空。
准确闭句为∀α,y[Empty(α)→Layer(α,y)→Empty(y)]，没有用宿主0或外部自然数索引替代对象空序数。
后继/极限层公式、层单调/传递及全体集合秩覆盖仍未证明，不能以本批存在唯一替代。

## 原核端点
ObjectPowerUnion有range/operation/total/deterministic四句及有限四句理论kernel_certificate、源ZF回放和native_*。
HierarchyRecursion有已消去算子前提的全存在/全唯一两句、源Replacement版ZF及原核证书。
ObjectCumulativeHierarchy有层存在、唯一纤维、两个层值相等及零层四句，全部有source_*、kernel_certificate及native_*。
原核回放仍使用既有TheoryTransport/ZFReplay和锁定YesMetaZFC，不增加推导核、语义可靠性假设或新的对象公理。

## 实际验收
C:/Python314/python.exe -X utf8 scripts/verify.py退出0；8条正式命令全部退出0。
Lean4.33.1、LEAN_NUM_THREADS=1；lake --no-cache --wfail build完成251个任务。
19源规则、9类源ZF及锁定SHA核对通过；Check/CheckStep2/CheckStep3/Audit均以--trust=0通过。
审计1778个声明：144个无公理依赖，1634个记录允许依赖；0条Lean警告。
新增132个审计声明，其中11个无公理依赖；十个新增原核kernel_certificate逐项核对仅有propext/Classical.choice/Quot.sound。
nativeZF回放仍继承原底座七个固定句子FreeClosed证书的native_decide.ax_1基线，未新增自定义公理。
218个验收文件实际哈希复核一致；没有新增sorry/admit、unsafe或外部良基/标准性输入。
CheckStep3直接检查原PowerSet和子集AST、真实像/并见证、递推矩阵对应、消去前提后的全图证明、原Source.ordinal的全层唯一以及零层原核句子。
定向编译修正图输出/幂集值命名冲突、实例归一化与证书接合、一个未用化简项；最终完整验收通过。
verification/保留实际命令、日志、依赖和源码哈希；未推送远端。

## 下一项与全目标缺口
下一项证明完整历史图的早期输出与相应Layer值严格对应，再取得层成员递归公式、后继/极限公式和层单调/传递。
非空可定义序数性质的唯一最小元及秩覆盖仍待实现；反向完整Collection不能由本批实际层值存在唯一推出而不补证明。
全局ω函数图、最小传递闭包、两种AC等价、内部ProofZF/U/Con完整AST、任意内部码编译器正确性、
对象解释/对称强迫及最终Derives nativeZF [] (Con_ZF→Con_target)仍未实现。
OpenAI原4.34.1构建和Comparator仍未运行；PP/AC相对一致性最终定理未完成。
