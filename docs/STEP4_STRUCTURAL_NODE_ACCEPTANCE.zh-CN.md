# 原始结构节点对象推导验收

日期2026-10-22；分支migration/yesmeta-step3；本批基点f97729bec2f37892ed3288b2c66c0bdb1127a75e。
本批关闭4b.c.4a。原始数值节点编码/分解已经完成；有效列表/树、专用ProofZF/U和最终Con尚未完成。

## 对象语言、背景与固定节点公式

对象语言仍仅有等词和∈，背景仍为原ZF，不加入对象AC、不可达、Con或模型存在前提。
推导使用Source.Derives (Source.SetLanguage.ZF.at n)，经既有TheoryTransport和ZFReplay取得
原YesMetaZFC的FirstOrder.Derives nativeZF []完整闭句证书。底座推导核及固定依赖未改动。

Raw(w,tag,payload,n) := ∃q(Pair(w,tag,payload,q)∧Succ(n,q))。
Pair是此前已证的原严格分支Gödel配数关系，Succ也是原对象后继关系。
这个AST严格保留固定LanguageEncoding.lean的structural_raw_node_code_term后继配数定义。
标签不预先限制为某几个宿主自然常量，载荷也不默认已经是合法字段列表。

EncodeFiber(w,a,b)实际取得n∈w和Raw(w,a,b,n)，并证明每个满足Raw的任意输出候选m等于n。
节点解码定义为：Witness(w,n,a,b):=(a∈w∧b∈w)∧Raw(w,a,b,n)。
Preimage(w,n):=∃a∃b Witness(w,n,a,b)。
ExactAt(w,n,a,b):=∀c∀d(Witness(w,n,c,d)↔(c=a∧d=b))。
Fiber实际取得上述a,b及ExactAt；BoundedFiber在同一实际纤维上另外给出a∈n∧b∈n。
这里的界为严格对象成员关系，提供后续内部递归所需的真实子码下降。

## 数学证明与工程模块

原配数总性实际取得q，Omega(w)的后继封闭再实际取得n，给出Raw的全内部实际存在。
原配数输出唯一性对齐中间q，再由原后继外延唯一性得到节点输出唯一。
两个输入不超过q，而n是q的后继，所以两个输入都严格属于n。

同一节点的两个前驱q、p分别属于共同后继。原后继成员刻画给出q≤p和p≤q，
由内部自然次序反对称得到q=p，再由原配数输入单射性得到标签和载荷相等。
所有比较和见证仍在对象层，不依赖宿主Nat、外部标准ω或WellFounded。

每个正内部自然码n实际存在自然前驱q；此前全内部配数逆解码再实际取得q的自然标签/载荷。
这些见证直接构造Raw与Preimage。零码由原后继非空性排除。
节点输入单射性与对象等词替换给出双向ExactAt，再加入严格成员界取得BoundedFiber。

| 模块 | 实际职责 |
|---|---|
| StructuralNodeSyntax | Raw/ExistsRaw/EncodeFiber纯AST、重命名及实际见证引入/消去 |
| StructuralNodeExistence | 实际配数值和实际后继构造全内部节点 |
| StructuralNodeProperties | 编码值ω闭包、非空性、标签/载荷严格子码界 |
| StructuralNodeCore | 前驱消去、输出唯一、输入单射及实际唯一编码纤维 |
| StructuralNodeDecodeSyntax | 自然候选、双向精确纤维和严格有界解码纯AST |
| StructuralNodeDecodeExistence | 每个正码实际分解、零码排除及正码与解码存在的双条件 |
| StructuralNodeDecodeUnique | 精确双向解码刻画、实际唯一纤维及两个严格子码界 |
| ObjectStructuralNode | 九个完整闭句及源ZF/sourceZF原核核心/原nativeZF证书 |

## 九个完整闭句

下表除positiveSentence外均保留Omega(w)，所有自由对象变量均以.close全称闭合。

| 句子 | 其他对象前提与完整结论 |
|---|---|
| encodeFiberSentence | a,b∈w→EncodeFiber(w,a,b) |
| closureSentence | Raw(w,a,b,n)→n∈w；不额外要求a,b自然 |
| positiveSentence | Raw(w,a,b,n)→¬Empty(n)；该句不需要Omega前提 |
| componentsSentence | a,b∈w、Raw(w,a,b,n)→a∈n∧b∈n |
| injectiveSentence | a,b,c,d∈w、Raw(w,a,b,n)、Raw(w,c,d,n)→a=c∧b=d |
| positiveIffSentence | n∈w→(¬Empty(n)↔Preimage(w,n)) |
| decodeTotalSentence | n∈w、¬Empty(n)→Preimage(w,n) |
| decodeFiberSentence | n∈w、¬Empty(n)→Fiber(w,n) |
| decodeBoundsSentence | n∈w、¬Empty(n)→BoundedFiber(w,n) |

每句都有source_*、*_kernel_certificate及native_*。这些均为实际原核证书，不是模型语义断言。
CheckStep4直接核对原后继配数AST、解码候选的自然范围、严格有界纤维、正码双条件以及九个原核端点。

## 实际验收

C:/Python314/python.exe -X utf8 scripts/verify.py退出0，九条正式命令全部退出0。
LEAN_NUM_THREADS=1；lake --no-cache --wfail build完成411个任务。
Check、CheckStep2、CheckStep3、CheckStep4、Audit均以--trust=0通过。
3377项声明审计：198项无公理依赖、3179项允许依赖；正式验收0警告。
本批8个模块、81项显式声明全部进入审计；380个文件SHA256实际复核一致，差异0。
累计75个算术/顺序/编码核心证书及对应原nativeZF端点由verify.py精确核对依赖。
本批九个核心恰为propext、Classical.choice、Quot.sound；原native端点恰为这三项加七个原有闭性证书。
原choice额外依赖限域、两份可信基JSON、固定底座及原核均未变；没有新增自定义公理或对象Choice输入。
原19规则及九类源ZF锁定检查通过。原OpenAI完整构建及Comparator未运行；未远端推送。
精确依赖、命令退出码、哈希及独立复核仅保留本地verification/；复核文件为structural-node-readback.json。

## 下一关与剩余边界

本批Preimage只解析原始数值节点。它不判断标签是否属于有效构造子，也不判断载荷是否为正确字段列表。
下一关4b.c.4b使用原Nil标签0和Cons标签1，常量由内部实际零/后继指定：
Nil(w,n):=∃z(Empty(z)∧Raw(w,z,z,n))；
Cons(w,h,t,n):=∃z∃e∃q(Empty(z)∧Succ(e,z)∧Pair(w,h,t,q)∧Raw(w,e,q,n))。
这些是下一关的目标公式，目前不计入已实现内容。

| 实现顺序 | 对象交付及验收门 |
|---|---|
| Nil值 | 实际零/单位见证；Nil数值为内部1的完整等词刻画及原核闭句 |
| Cons实际值 | 实际内层配数与外层原节点；全内部自然head/tail的实际唯一输出 |
| 构造器区分 | Nil/Cons互斥，Cons相等推出head/tail分别相等 |
| 严格子码界 | 两层配数和原节点严格界推出head∈n、tail∈n |
| 内部列表/树 | 用严格下降及真实内部递归检查有效/无效码，不预设tail已是有效列表 |

之后仍需保留全部11语法构造、bound/free长度、27逻辑模式、六条原核规则及全Separation/Collection。
全ω二元运算图未单独交付；专用ProofZF/U、任意内部码检查正确性、内部编译器、构造解释、
实际对称强迫和最终FirstOrder.Derives nativeZF [] (Con_ZF→Con_target)仍未完成。
本批不提升这些完成标志，完整目标保持进行中。
