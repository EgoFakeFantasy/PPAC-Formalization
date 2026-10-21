# 全内部自然码的实际唯一解码验收

日期2026-10-22；分支migration/yesmeta-step3；本批基点7d1c8e49f27736fcb6b7d96f36f721fd06a02b21。
本批关闭4b.c.3。原配数的全内部编码与逆解码已完成；结构列表/树码及最终内部Con主句仍未完成。

## 对象合同与纯公式

对象语言仍仅含等词和∈，背景仍是原ZF，不加入AC、不可达、Con或模型存在前提。
使用Source.Derives (Source.SetLanguage.ZF.at n)，经TheoryTransport和ZFReplay返回
原FirstOrder.Derives nativeZF []的完整闭句证书。原推导核和固定依赖没有改动。
Pair严格采用已证原分支：a∈b时b²+a，否则(a²+a)+b。
所有实际算术值、分量、零和后继都是对象变量。

Witness(w,p,a,b) := (a∈w∧b∈w)∧Pair(w,a,b,p)。
Preimage(w,p) := ∃a∃b Witness(w,p,a,b)。
ExactAt(w,p,a,b) := ∀c∀d(Witness(w,p,c,d)↔(c=a∧d=b))。
Fiber(w,p) := ∃a∃b(Witness(w,p,a,b)∧ExactAt(w,p,a,b))。
BoundedFiber再在同一实际纤维上给出below(a,p)∧below(b,p)，其中below(x,y)是x=y∨x∈y。

ExactAt量化全部对象候选c,d；其左侧明确保留两者属于内部ω的范围。
反向由对象等词替换整个Witness，实际推出自然成员性和原配数关系，不把重编码对应留在宿主层。

## 对象ω归纳与四种后继转移

归纳正文是Preimage(w,p)，其唯一外部矩阵索引是固定有限纯公式。
对象归纳量化全部内部p∈w，包含模型外部看来非标准的自然对象；没有外部长度上限。
归纳零点对任意实际Empty(z)证明Pair(w,z,z,z)，实际得到两个自然分量。
后继步从实际解码(a,b)和Succ(r,p)出发：

| 原分支及实际条件 | 新编码r的实际分量 | 关键对象推导 |
|---|---|---|
| a∈b，Succ(t,a)，t∈b | (t,b) | 同一b²下的加法后继式 |
| a∈b，Succ(t,a)，t=b | (b,z)，Empty(z) | Add(b²,b,r)及Add(r,z,r)转入高支 |
| ¬a∈b，b∈a，Succ(t,b) | (a,t) | t≤a保持高支守卫，最终和的后继式 |
| ¬a∈b，b=a，Succ(t,b) | (z,t)，Empty(z) | 实际推出Mul(t,t,r)，零加法转入低支 |

低支用已证后继弱界得t=b∨t∈b；高支用原自然比较得b=a∨b∈a。
每个分量后继和零值均由Omega(w)实际取得后消去，不抽取Type层选择函数。
对角跳转使用平方的向前构造：从q=a²、u=q+a、p=u+a及r=Succ(p)，
左参数后继律得到Mul(Succ(a),a,u)，加法后继和乘法后继反向式给出Mul(Succ(a),Succ(a),r)。
因此不需要宿主sqrt、平方根算法、标准码枚举或原ZFC模型语义定理。

## 工程模块和六个闭句

| 模块 | 实际职责 |
|---|---|
| GodelUnpairSyntax | Witness/Preimage/ExactAt/Fiber/BoundedFiber纯AST、重命名、归纳正文及实际见证引入/消去 |
| GodelUnpairArithmetic | 内部零弱界、反向成员排除、后继/高支等词替换及后继平方实际构造 |
| GodelUnpairTransitions | 原零点和上述四种原配数后继转移 |
| GodelUnpairStep | 实际自然分量后继、两个分支封闭和Preimage的后继封闭 |
| GodelUnpairExistence | 对象零点/后继归纳义务及每个内部自然编码的实际Preimage |
| GodelUnpairUnique | 由原输入单射性证明双向ExactAt，实际唯一纤维与双分量界 |
| ObjectGodelUnpair | 六个完整闭句及源ZF、sourceZF原核核心和原nativeZF证书 |

下表每句均保留Omega(w)，所有自由变量以.close全称闭合：

| 句子 | 其他对象前提与完整结果 |
|---|---|
| zeroSentence | Empty(z)→Preimage(w,z) |
| successorSentence | Preimage(w,p)→Succ(r,p)→Preimage(w,r) |
| totalSentence | p∈w→Preimage(w,p) |
| characterizationSentence | Witness(w,p,a,b)→ExactAt(w,p,a,b) |
| fiberSentence | p∈w→Fiber(w,p) |
| boundedSentence | p∈w→BoundedFiber(w,p) |

每句均有source_*、*_kernel_certificate、native_*；不存在未证的递推总性或解码存在前提。
CheckStep4直接核对Witness的内部自然范围、Preimage的实际双存在、ExactAt的双向量词体和总解码闭句，
并检查六个实际原nativeZF端点。

## 实际验收

C:/Python314/python.exe -X utf8 scripts/verify.py退出0；九条正式命令全部退出0。
LEAN_NUM_THREADS=1；lake --no-cache --wfail build完成403个任务。
Check、CheckStep2、CheckStep3、CheckStep4和Audit均以--trust=0通过。
3296项显式声明审计：198项无公理依赖、3098项允许依赖；正式验收0条警告。
本批7个模块的64项声明全部进入审计；372个验收文件SHA256实际复核一致，差异0。
累计66个算术/顺序/配数/解码核心证书及原nativeZF端点均由verify.py精确检查依赖。
本批六个核心恰为propext、Classical.choice、Quot.sound；对应native端点恰为这三项加七个原有闭性证书。
原choice额外证书限域、两份可信基JSON、固定底座与原核没有改变；未新增自定义axiom或对象Choice。
原19条规则和九类源ZF锁定检查通过。原OpenAI完整构建及Comparator未运行；未远端推送。
命令退出码、精确依赖及哈希仅保留本地verification/；独立复核见verification/unpair-readback.json。

## 下一关及未完成范围

固定底座LanguageEncoding.lean和IntrinsicQuotationEvaluation.lean再次核对：
raw_node(tag,payload)=Succ(Pair(tag,payload))；
Nil=Succ(Pair(0,0))，故空结构列数值1；
Cons(head,tail)=Succ(Pair(1,Pair(head,tail)))；
Tree(tag,fields)=Succ(Pair(tag,Forest(fields)))，故叶0数值2。
这里仅核对原定义，没有把其宿主treeValue或ZFC语义结果冒充当前对象证明。

| 下一工作单元 | 对象交付与验收门 |
|---|---|
| 4b.c.4a 原节点 | 实际总单值、正码实际分解、tag/payload严格小于节点值及原核闭句 |
| 4b.c.4b Nil/Cons | 0/1由实际Empty/Successor指定；原嵌套配数AST、实际值、互斥/单射和严格head/tail界 |
| 4b.c.4c 列表/树 | 内部递归检查有效/无效码，实际有效结构解码与递归正确性；覆盖全部内部码 |
| 4c–4f 语法/Proof/Con | 保留11构造、bound/free长度、27逻辑模式、六规则和全Separation/Collection的专用检查器 |

全ω二元运算图未单独交付。结构码、专用ProofZF/U、任意内部码的检查正确性、内部编译器、构造解释、
实际对称强迫及最终FirstOrder.Derives nativeZF [] (Con_ZF→Con_target)仍未完成。
所有相应完成标志保持False，本批不提升最终目标的完成状态。
