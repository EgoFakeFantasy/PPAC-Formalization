# 精确内部末值集合与对象ZF传递覆盖验收
日期：2026-10-21；基点74259dfeb8674fc9dfb5fe1543f3e53386616ac3。
分支migration/yesmeta-step3。本批完成末值精确收集及无额外前提的对象传递覆盖。

## 背景、语言与最终交付范围
语言仍为单排序纯等词/成员ℒ，证书输出原YesMetaZFC FirstOrder.Derives/Hilbert核。
源背景是固定原Replacement版ZF，目标背景nativeZF是原Collection版ZF的纯语言像。
没有添加AC、不可达、Con前提、新可信核、统一真值谓词或外部良基/标准ω假设。
本批最终辅助定理是完整对象闭句∀a∃b(a⊆b∧Transitive(b))，并已消去实际ω、空集和值域见证。
全局ω函数图、最小传递闭包性质及原PP/AC相对一致性主句仍未完成。

## 实际末值、唯一纤维与原Replacement
Value(n,z,a,r) := ∃d∃f[FiniteWitness(f,d,n,z,a)∧edge(f,n,r)]。
每个末值均由已构造的实际有限轨迹和完整functionOn见证，不是宿主迭代函数的值。
IterationValueExistence在任意内部n∈ω取得有限轨迹，再由对象总性取得n位置的真实输出。
IterationValueUniqueness消去两条轨迹见证，以实际轨迹图唯一性传输边，再以单值性证明r=t。
IterationValueCollection把这些推导合成为∀n∈ω∃r(Value(n,r)∧∀t(Value(n,t)→t=r))。

matrix : Formula 4精确为Value(2,0,1,3)，参数是z,a，关系输入/输出是n,r。
对它应用一个原Source.replacement实例，实际得到集合c并证明
Range(c,w,z,a) := ∀r[r∈c ↔ ∃n(n∈w∧Value(n,z,a,r))]。
末值集合覆盖全部内部ω索引，未用外部标准有限长度替代，也未仅取得含额外元素的收集界。

IterationContext.Evidence只是公开8句对象公理的Derives证书包：Extensionality、Pairing、Union、
Foundation及4个既有Separation实例。字段不包含轨迹存在、相容、值域或覆盖结论。
add/rename/under等接口仅由原弱化与重命名规则派生；该包装未增加可信推导规则。

## 种子成员与真实取并封闭
IterationRangeSeed从真实零长度轨迹证明Value(z,z,a,a)，由Empty(z)取得z∈ω，故a∈c。
IterationValueStep证明任意两条内部有限轨迹相容；相邻长度n,s满足Succ(s,n)时，
在第二条实际图中取得前驱值并以相容性对齐，再由原Next条件证明UnionOf(t,r)。
此处没有假设两个外部长度可比较，也未把内部成员关系当作宿主WellFounded。
IterationRangeClosed对每个r∈c消去其真实内部索引n，取得ω中实际后继s及其真实末值t，证明
ClosedUnion(c) := ∀r(r∈c→∃t(t∈c∧UnionOf(t,r)))。
所有索引、轨迹、输出与后继见证都由原exI/exE规则在对象推导中处理，未抽取Type层选择函数。

## 实际传递覆盖构造
原Union取得b=∪c。由a∈c，任意x∈a均属于b，故a⊆b。
若x∈b且y∈x，消去并集成员见证取得r∈c与x∈r；
再用ClosedUnion取得t∈c和t=∪r，因此y∈t，最后y∈b。
TransitiveCoverLogic由这些原成员/量词推导得到Transitive(b)，没有调用秩、递归或Collection。
TransitiveCoverExistence由实际Replacement值域与实际Union见证取得b。
ObjectTransitiveCover.source_cover进一步消去原ZF中已证明存在的ω和空集见证。

## 三个完整闭句与实际原核证书
ObjectTransitiveCover提供以下source_*（原源ZF推导）、*_kernel_certificate（源ZF像上的原核证书）
与native_*（实际nativeZF原核推导），全部显示参数均在句内全称闭合：

| 闭句 | 对象内容 |
|---|---|
| rangeSentence | Omega(w)→Empty(z)→∃c Range(c,w,z,a) |
| propertiesSentence | Omega(w)→Empty(z)→Range(c,w,z,a)→(a∈c∧ClosedUnion(c)) |
| coverSentence | ∀a∃b(a⊆b∧Transitive(b)) |

native_cover的实际类型是FirstOrder.Derives nativeZF [] (Translation.sentence coverSentence)。
源source_cover实际类型是Source.Derives (Source.SetLanguage.ZF.at 0) coverSentence。
源证明只以原Replacement版ZF为理论输入，没有Collection输入，因此没有反向Collection的循环论证。
原nativeZF回放通过已验收的Collection→原Replacement推导取得所需模式实例。

## 实际验收
C:/Python314/python.exe -X utf8 scripts/verify.py退出0；8条正式命令全部退出0。
Lean4.33.1、LEAN_NUM_THREADS=1；lake --no-cache --wfail build成功，183个任务。
19条源规则、9类ZF及锁定SHA核对通过；Check/CheckStep2/CheckStep3/Audit以--trust=0通过。
1122个列举审计声明：100个无依赖、1022个有记录允许依赖；0条Lean警告。
新增85个审计声明，其中11个无依赖；Evidence类型、构造器与8个证书字段亦逐一列举审计。
无sorry/admit、新自定义公理、对象AC/不可达前提或有限标准索引截断。
源ZF像上的三个kernel_certificate仅依赖标准propext/Classical.choice/Quot.sound；
实际nativeZF回放仍保留底座7个固定基础句子FreeClosed证书的既有基线。
verification/保存实际命令、日志、依赖及源码SHA；未推送远端。

## 下一项与最终目标缺口
已取得传递覆盖；覆盖的最小性、全局ω函数图、内部序数/递归/秩/累积层仍未完成。
后续用对象序数和秩覆盖完成源Replacement推导原完整Collection，并证明两种AC呈现等价。
内部ProofZF/U/Con完整AST、任意内部码上的编译器正确性、对象解释/对称强迫，
以及最终原核Derives nativeZF [] (Con_ZF→Con_target)仍未完成。
OpenAI原4.34.1构建及Comparator仍未运行；未宣称原PP/AC相对一致性定理已经完成。
