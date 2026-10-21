# 原Nil/Cons构造器对象推导验收

日期2026-10-22；分支migration/yesmeta-step3；本批基点b9e20ea0ad7e71fb0ec0dd20c55694cce34c51de。
本批关闭4b.c.4b。构造器数值层已完成；递归有效列表/树、专用ProofZF/U及最终Con仍未完成。

## 对象合同与固定公式

对象语言仍仅含等词和∈，背景仍是原ZF，不增加对象AC、不可达、Con或模型存在假设。
使用Source.Derives (Source.SetLanguage.ZF.at n)，经TheoryTransport和ZFReplay取得
原FirstOrder.Derives nativeZF []的完整闭句证书，原推导核与固定依赖未改。

Raw(w,tag,payload,n)是已证原后继配数关系；Pair是固定原Gödel分支。
Nil(w,n):=∃z(Empty(z)∧Raw(w,z,z,n))。
ConsAt(w,e,h,t,n):=∃q(Pair(w,h,t,q)∧Raw(w,e,q,n))。
Cons(w,h,t,n):=∃z∃e(Empty(z)∧Succ(e,z)∧ConsAt(w,e,h,t,n))。

零标签、单位标签与内层配数值均是实际内部对象，不固定宿主0/1函数值。
再次读取固定LanguageEncoding.lean，Nil标签0/零载荷以及Cons标签1/内层Pair(head,tail)均按原定义保留。
CheckStep4以rfl核对完整Nil公式和Cons零/单位/配数嵌套公式，包含全部绑定层次和参数次序。

## 实际零/单位与构造器证明

Omega(w)实际取得空集z及其后继e；对象Extensionality对齐任意两个零/单位见证。
with_units只是在正式推导中引入并消去两个实际存在量词，不增加单位存在公理或Type层选择函数。
原Pair(z,z,z)及Succ(e,z)构造Nil值e，节点输出唯一性给Nil(w,n)↔n=e。
实际唯一Nil纤维同时保留值属于内部w及任意输出候选唯一。

Cons先实际取得q=Pair(h,t)，再实际取得原节点Raw(e,q,n)。
任意隐藏零/单位见证均可对齐同一实际e；内层配数和外层节点的唯一性给Cons输出唯一。
同一Cons输出先由外层节点单射性对齐q，再由内层Pair单射性得到head和tail分别相等。
内层head/tail≤q，外层q∈n，故head∈n、tail∈n。
Cons单位标签本身属于n，而Nil值等于此单位；若两种构造器同码便得到单位自属矛盾。
这项互斥证明不需要额外head/tail自然前提。

Empty(z)、Succ(e,z)、Succ(two,e)下，实际证明Nil(w,e)及Raw(w,z,e,two)。
其中先由乘法零点和后继式实际证明e²=e，再证明Pair(z,e,e)，最后取原后继封装。
这固定空字段列的内部1值与零叶raw封装的内部2值；完整SyntaxEncode/quotation及矛盾句码正确性仍待接入。

## 工程模块与九个闭句

| 模块 | 实际职责 |
|---|---|
| StructuralListSyntax | Nil/ConsAt/Cons纯AST、实际零/单位包、重命名及对象见证引入/消去 |
| StructuralListUnits | 实际零/单位存在、唯一、ω成员及对象存在消去；节点载荷等词替换 |
| StructuralNil | Nil实际单位值、双向等词刻画、范围及唯一纤维；零叶raw封装内部二值 |
| StructuralConsAt | 给定单位标签时的Cons范围/非零、严格头尾界、输出唯一及输入单射 |
| StructuralConsCore | 隐藏单位标签正规化、精确双条件、实际Cons存在及范围/严格界 |
| StructuralConsUnique | 实际Cons唯一纤维、输入单射及Nil/Cons互斥 |
| ObjectStructuralList | 九个完整闭句及源ZF/sourceZF原核核心/原nativeZF证书 |

下表除consTag外均保留Omega(w)，所有自由变量以.close全称闭合。

| 句子 | 其他对象前提与完整结论 |
|---|---|
| nilValueSentence | Empty(z)、Succ(e,z)→(Nil(w,n)↔n=e) |
| nilFiberSentence | 实际存在唯一n∈w满足Nil；任意满足Nil的输出候选均等于n |
| consTagSentence | Empty(z)、Succ(e,z)→(Cons(w,h,t,n)↔ConsAt(w,e,h,t,n))；此句无需Omega |
| consFiberSentence | h,t∈w→实际存在唯一n∈w满足Cons(w,h,t,n)，任意输出候选均相等 |
| closureSentence | Cons(w,h,t,n)→n∈w∧¬Empty(n)，不额外要求head/tail自然 |
| boundsSentence | h,t∈w、Cons(w,h,t,n)→h∈n∧t∈n |
| injectiveSentence | h,t,c,d∈w、Cons(w,h,t,n)、Cons(w,c,d,n)→h=c∧t=d |
| disjointSentence | Nil(w,n)、Cons(w,h,t,n)→⊥，不另要求head/tail自然 |
| leafZeroSentence | Empty(z)、Succ(e,z)、Succ(two,e)→Nil(w,e)∧Raw(w,z,e,two) |

每行都有source_*、*_kernel_certificate和native_*。
这些是原构造器数值定理，不含tail有效性前提，也不据此断言每个自然tail均编码有效列表。

## 实际验收

首次全套检查在新增CheckStep4严格头尾界核对式发现一处缺失括号，修复后重跑全部九条正式命令。
C:/Python314/python.exe -X utf8 scripts/verify.py最终退出0；九条命令全部退出0。
LEAN_NUM_THREADS=1；lake --no-cache --wfail build完成418个任务。
Check、CheckStep2、CheckStep3、CheckStep4和Audit均以--trust=0通过。
3472项显式声明审计：200项无公理依赖、3272项允许依赖；最终验收0警告。
本批7个模块、95项新增声明均进入审计；387个文件SHA256实际复核一致，差异0。
累计84个算术/顺序/编码核心证书与对应原nativeZF端点由verify.py精确核对依赖。
本批九个核心恰为propext、Classical.choice、Quot.sound；原native端点恰为这三项加七个原有闭性证书。
原choice额外证书限域、两份可信基JSON、固定底座及原核未变；未新增自定义公理或对象Choice。
原19规则及九类源ZF锁定核对通过；原OpenAI完整构建和Comparator未运行；未远端推送。
命令、依赖、哈希及独立复核仅保留本地verification/，复核文件为structural-list-constructors-readback.json。

## 下一关：全内部有限列表轨迹与有效解码

下一主项4b.c.4c需先给出纯对象ValidList。拟采用实际内部有限构造轨迹：
长度l∈w、实际后继域d、完整SequenceSyntax.sequence(f,d,w)集合图；
空索引是实际Nil值，末索引l的值是目标码，每个相邻索引的值由某个实际自然head经原Cons连接。
ValidList存在量化内部长度、后继域和完整集合图，不以宿主List或外部有限深度替代。
这是下一关规格，目前不计入已实现内容。

| 顺序 | 对象工程交付 | 验收门 |
|---|---|---|
| 1 | StructuralListTraceSyntax | 有界完整序列、Nil种子、实际末值及全部相邻Cons步的纯AST和正式目标 |
| 2 | TraceBase/Append | 实际单点Nil轨迹与实际Cons追加；保留全部旧边，单独证明相邻递推保持 |
| 3 | TraceInvert/Prefix | 内部长度零/后继分解、实际前缀、精确Nil或Cons有效尾分解 |
| 4 | Decode/Uniqueness | 实际长度与字段图唯一、有效码解码双向正确、严格字段界 |
| 5 | Check/TreeCode | 覆盖全部内部码的有效解码及无效排除，再接入原树字段结构 |

既有SequenceAppend/Prefix提供实际图和精确旧边；相邻递推涉及图参数变化，必须另证，不能直接套用旧rows模式。
后续还需全部11语法构造、bound/free长度、27逻辑模式、六规则及全Separation/Collection的专用检查器。
全ω二元运算图未单独交付；内部ProofZF/U、任意内部码正确性、内部编译器、构造解释、实际对称强迫
以及最终FirstOrder.Derives nativeZF [] (Con_ZF→Con_target)仍未完成。
相应完成标志保持False，完整目标保持进行中。
