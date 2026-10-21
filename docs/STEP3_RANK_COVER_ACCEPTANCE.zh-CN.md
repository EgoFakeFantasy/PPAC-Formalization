# 全内部集合层覆盖与实际唯一秩验收
日期：2026-10-21；基点f71b3266ed5572d07e97f5a01bd9c8e79aef926d。
分支migration/yesmeta-step3；反向完整Collection及最终内部Con主句仍未完成。

## 对象语言、背景与准确秩定义
仍为原纯等词/成员语言及原FirstOrder.Derives；nativeZF仍是原Collection呈现的ZF纯语言像。
源证明使用完整原Replacement呈现的Source.SetLanguage.ZF，不输入Collection或对象AC。
所有x、y、α、δ、层值v和集合族C均是内部集合变量；原Ord、Layer及全部子集量词保持不变。

Contains(x,α) := ∃v[Layer(α,v)∧x⊆v]。
AtIndex(x,α) := Ord(α)∧Contains(x,α)。
Cover(x) := ∃α AtIndex(x,α)。
Rank(x,α)是Contains(x,–)的最小内部原序数：
AtIndex(x,α)∧∀β[AtIndex(x,β)→(α=β∨α∈β)]。
因此本批的秩是最小包含层索引，使用子集条件x⊆Vα；不是最小成员层索引。
这里没有宿主rank函数、外部良基前提、预设层覆盖或被选出的宿主见证族。

## 六个完整闭句

| 闭句 | 完整数学内容（缩写展示纯对象式） |
|---|---|
| coverSentence | ∀x∃α[Ord(α)∧∃v(Layer(α,v)∧x⊆v)] |
| rankSentence | ∀x∃α[Rank(x,α)∧∀β(Rank(x,β)→β=α)] |
| memberSentence | ∀x∃α∃v[Ord(α)∧Layer(α,v)∧x∈v] |
| rangeSentence | ∀x∃C∀α[α∈C↔∃y(y∈x∧Rank(y,α))] |
| equalitySentence | ∀x,α,β[Rank(x,α)→Rank(x,β)→α=β] |
| propertySentence | ∀x,α[Rank(x,α)→AtIndex(x,α)] |

ObjectRankCover为每条提供source_*、*_kernel_certificate及native_*。
最终端点均为实际FirstOrder.Derives nativeZF [] (Translation.sentence φ)，
闭句没有MembersCovered、算子总性/单值性、秩或覆盖等未证残留前提。
不是只检查外部标准集合或序数，也不以Lean模型语义代替这些对象推导。
本批没有另行给秩的上确界递推等式或逐成员严格递降专用闭句。

## 唯一秩纤维与实际Replacement精确像
LayerCoverSyntax定义实际层包含、全体成员已覆盖和内部成员覆盖公式。
LayerRankSyntax严格对接任意参数序数最小元模式；contains_pred/contains_property/contains_has保持原内部x参数。
其matrix : Formula 2精确表达Rank(input,output)，relation/fiber/image/range逐式对应原Replacement接口。
LayerCoverClosedInstances把已证明的最小序数唯一纤维闭句实例化；仅在给定Cover(y)时取得实际唯一秩。

LayerRankCollection在对象归纳前提∀y∈x Cover(y)内，取得每个内部y的真实唯一秩纤维。
本步的一个明确原Replacement实例实际构造精确集合C={α:∃y∈x Rank(y,α)}。
消去每个C成员的实际y/秩关系，证明C的每个成员是原序数；精确像不含额外杂项。
依赖的层存在、序数最小元及传递覆盖定理各按其已有证明使用源ZF，不声称整个证明只用这一个Replacement实例。

## 实际共同界、共同层及全对象归纳
LayerRankBound对任意内部序数族C使用已证严格上界闭句，实际取得δ及∀α∈C α∈δ。
原层存在闭句实际给Layer(δ,v)。对任意y∈x，消去实际秩α及Rank(y,α)中的层值u，
获得Layer(α,u)和y⊆u。精确像给α∈C，严格界给α∈δ，原完整层成员递归给y∈v。
因而x⊆v，得到实际Cover(x)。没有先假定所有这些候选层值组成集合或预设共同序数界。

LayerCoverInduction实际消去C、δ、v见证，得到Cover的对象集合归纳进步步。
原Foundation、对应完整Separation实例和已证实际传递覆盖给全体集合归纳，
从而证明∀x Cover(x)，没有模型外部WellFounded或内部ω标准性输入。
再次实例化已证序数最小元模式，得到全部内部集合的实际唯一秩。
全局Cover还给所有成员的覆盖，因而得到每个内部集合成员秩的实际精确像集合。

LayerCoverMembership从实际包含层α/v构造实际后继s和实际Layer(s,w)，
以原后继PowerOf(w,v)将x⊆v提升为x∈w，证明完整成员覆盖句。
源Proof树全部由原19规则组成，随后经既有传输/回放产生原Hilbert核证书。

## 实际验收
C:/Python314/python.exe -X utf8 scripts/verify.py退出0；8条正式命令全部退出0。
Lean4.33.1、LEAN_NUM_THREADS=1；lake --no-cache --wfail build完成278个任务。
19条源规则、9类源ZF及锁定SHA核对通过；Check/CheckStep2/CheckStep3/Audit均以--trust=0通过。
审计2043个声明：150个无公理依赖、1893个记录允许依赖；0条Lean警告。
8个新模块共84个显式声明全部加入Audit；全部新声明记录于允许依赖范围。
六个新增*_kernel_certificate逐项实际核对恰有propext/Classical.choice/Quot.sound。
nativeZF端点只继承既有七个固定句子的FreeClosed证书依赖基线，没有新增自定义公理。
245个验收文件的实际SHA256复核一致，无sorry/admit、unsafe或外部标准性输入。
CheckStep3直接核对原ordinal、所有内部子集/成员量词、最小包含层秩、Replacement纤维和精确像，
并接合六个native端点、完整∀x成员覆盖及源Replacement版ZF的实际证明类型。
定向构建修正未用化简项、抬升公式接合、矩阵命名冲突和零参数绑定变量对齐；最终全验收通过。
命令、日志、依赖和哈希保留本地verification/；未推送远端。

## 下一项与最终目标边界
下一项对任意参数原关系p(x,y)定义其实际见证秩性质：∃y[p(x,y)∧Rank(y,α)]。
从每个x存在某个y的前提出发，只取唯一最小见证秩，使用原Replacement收集这些秩，
共同界层内重新取得每个x的真实p见证，导出完整原Collection句子。
不得把本批成员秩集合或全体集合覆盖本身宣称为反向Collection已经证明。
完整ZF反向回放、两种AC等价、内部ProofZF/U/Con AST与任意内部码正确性、
对象解释/对称强迫和最终Derives nativeZF [] (Con_ZF→Con_target)仍未完成。
全局ω图、最小传递闭包是独立待办；OpenAI原4.34.1构建及Comparator仍未运行。
