# 零/极限层、实际早层族与可定义序数最小元验收
日期：2026-10-21；基点0c0efc5ff75fca6060cfc6d1f5b76b394f70f4d9。
分支migration/yesmeta-step3；全体集合秩覆盖及最终内部Con主句仍未完成。

## 对象语言、背景和量词
仍使用原纯等词/成员语言、原FirstOrder.Derives及nativeZF背景；没有新推导核或对象公理。
Ord严格对应原Source.ordinal；所有集合、序数、图、层值及子集量词遍历全部内部集合。
Layer沿用已实际构造的后继域递归图在给定索引处的原Kuratowski输出边定义。

LimitIndex(α) := Ord(α) ∧ ∀β[β∈α→∃s(Succ(s,β)∧s∈α)]。
这个零或极限条件包含空序数；零索引满足该条件有独立闭句证明。
没有把内部序数、ω或实际见证限制为外部标准对象；没有声称已证明任意序数的零/后继/极限分类。

## 六个已证层闭句

| 闭句 | 完整对象内容（缩写展示） |
|---|---|
| equationSentence | ∀α,y[LimitIndex(α)→Layer(α,y)→∀z(z∈y↔∃β∃v(β∈α∧Layer(β,v)∧z∈v))] |
| rangeSentence | ∀α[Ord(α)→∃C∀v(v∈C↔∃β(β∈α∧Layer(β,v)))] |
| rangeEqualitySentence | ∀α,C,D[Range(C,α)→Range(D,α)→C=D] |
| unionSentence | ∀α,y,C[LimitIndex(α)→Layer(α,y)→Range(C,α)→UnionOf(y,C)] |
| assembledSentence | ∀α,y[LimitIndex(α)→Layer(α,y)→∃C(Range(C,α)∧UnionOf(y,C))] |
| zeroSentence | ∀α[Empty(α)→LimitIndex(α)] |

每条均在ObjectHierarchyLimit中提供source_*、*_kernel_certificate和native_*。
UnionOf是原并集成员公式，C是真实存在的内部集合，精确像不允许多余元素。

HierarchyClosedInstances将已证层存在、唯一纤维、成员递归及后继PowerOf闭句实例化到任意上下文。
极限成员式正向消去原成员递归的β/v见证，实际取得β后继s∈α及其实际层值w，
原后继PowerOf使z⊆v转成z∈w；反向由原序数传递和层包含单调性传回α层。
HierarchyFamilySyntax.matrix的原relation/fiber/image/range逐式对应实际Layer、layerFiber和精确早层族。
HierarchyLayerCollection只用一个明确的原Replacement实例和已证唯一层纤维实际构造C；
HierarchyFamilyUnion证明并成员式与原UnionOf严格对应，并消去实际C见证。
未从存在命题抽取宿主选择族，源证明没有Collection或对象AC输入。

## 任意参数的三个最小序数模式
对任意n及p : Source.Formula (n+1)，保留全部n个参数ρ。
Property(p,ρ,a) := Ord(a) ∧ p[ρ,a]。
Least(p,ρ,a) := Property(p,ρ,a) ∧ ∀b[Property(p,ρ,b)→(a=b∨a∈b)]。
Has(p,ρ) := ∃a Property(p,ρ,a)。
UniqueLeast(p,ρ,a) := ∀b[Least(p,ρ,b)→b=a]。

ObjectOrdinalLeast逐公式提供以下完整闭句和源ZF/原核证书：

| 模式 | 完整内容（闭合全部参数） |
|---|---|
| existenceSentence p | Has(p,id)→∃a Least(p,id,a) |
| uniquenessSentence p | Has(p,id)→∃a(Least(p,id,a)∧UniqueLeast(p,id,a)) |
| equalitySentence p | ∀a,b[Least(p,params,a)→Least(p,params,b)→a=b] |

OrdinalLeastSyntax.matrix将Ord与原p合取，谓词实例化保留全部参数和末绑定槽。
已有对象全局成员极小元定理给该性质的真实内部见证a；原序数比较对任意候选b分成a=b、a∈b、b∈a。
前两支直接给最小性，最后一支违反a的对象成员极小性。
两个最小候选若互属则违反原序数不对称性，因此取等；另有least_subset给a⊆任意同性质候选b。
所有实际存在见证用原exI/exE消去；不使用外部WellFounded、宿主序数递归或选择函数。
源存在模式使用实际传递覆盖、Foundation、Extensionality及明确的完整Separation实例；没有Collection输入。

n和p是合法外部模式索引，每个实例本身产生完整对象句子及实际Derives。
这里没有内部统一真值谓词，也未将外部模式生成器宣称为已完成的内部代码表示。

## 实际工程验收
C:/Python314/python.exe -X utf8 scripts/verify.py退出0，8条正式命令全部退出0。
Lean4.33.1、LEAN_NUM_THREADS=1；lake --no-cache --wfail build完成270个任务。
19条源规则、9类源ZF及锁定SHA核对通过；Check/CheckStep2/CheckStep3/Audit均以--trust=0通过。
审计1959个声明：150个无公理依赖、1809个记录允许依赖；0条Lean警告。
11个新模块的105个显式声明全部加入审计，其中3个无公理依赖。
六条层闭句和三个模式的九个新增原核证书逐项核对恰有propext/Classical.choice/Quot.sound。
nativeZF回放只继承既有底座七个固定句子的FreeClosed证书依赖基线，未新增自定义公理。
237个验收文件的实际SHA256复核一致，无sorry/admit、unsafe或外部标准性前提。
CheckStep3直接检查原ordinal/successor、全内部极限条件和早层存在式、实际精确族/UnionOf、
Replacement唯一纤维对应、任意参数最小性及九个原核端点。
定向构建修正显式模块依赖、局部上下文/原序数投影及恒等重命名归一化；最终完整验收通过。
实际命令、日志、依赖与哈希在本地verification/；未推送远端。

## 下一项与全目标缺口
按工程表3b.3f.iv.a–iv.c，在对象集合归纳内为每个成员取得实际所属层，
以本批序数最小元取得唯一层索引，原Replacement收集索引并取实际共同严格序数界，
构造共同层及后继幂集，从而证明每个内部集合实际属于某层。
该全体集合覆盖定理尚未实现，不能由本批层并式或最小序数模式代替。
反向完整Collection、两种AC等价、专用内部ProofZF/U/Con AST与任意内部码正确性、
对象解释/对称强迫及最终Derives nativeZF [] (Con_ZF→Con_target)仍未完成。
OpenAI原4.34.1构建及Comparator仍未运行。
