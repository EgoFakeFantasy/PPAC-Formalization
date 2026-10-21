# 乘法代数与实际和值重排的对象推导验收
日期：2026-10-21；基点744f7a15201f18790809aafa154b20f43b637daa；分支migration/yesmeta-step3。

## 对象终点与背景
对象语言和原FirstOrder.Derives/HilbertDerivation不变，背景仍为完整原Replacement版源ZF，
经已有呈现对应传输到原nativeZF；未加入对象AC、不可达、Con或新推导核。
本批完成流程4b.b.2b.i–iv及内部乘法单位律。
全部自然数与和值/积值、递推图和中间见证均是对象量词，覆盖非标准内部ω成员。
最终Con_ZF→Con_target主句、内部证明码检查器及正确性尚未完成。

## 原ZF上下文接口
ZFContext.Evidence Γ严格定义为∀q(ZF.at m q→Γ q)，仅映射原ZF公理假设到当前上下文。
它没有算术结论字段。rename/add/under证明此包含在原规则的变量与上下文扩展下保持。
ZFArithmetic通过此前已证的闭句及明确原Separation实例实际取得递归/算术证书，
所有包装返回Source.Derives，不抽取内部集合的宿主选择函数或Lean自然数运算。
每个最终source_*显式由原ZF恒等包含及对象impI消去此接口，没有残留额外假设。
本批使用完整ZF背景，不声称只有这些包装器就证明了新的有限公理基础。

## 八个完整闭句
表中Add/Mul省略共同内部w参数；各加数/乘数有原Omega(w)及内部成员前提。

| 接口 | 实际对象内容 |
|---|---|
| ObjectNaturalAdditionReassociation.swapSentence | Add(a,b,u)、Add(a,c,v)、Add(u,c,r)推出Add(v,b,r) |
| interchangeSentence | Add(a,b,u)、Add(c,d,v)、Add(a,c,x)、Add(b,d,y)、Add(u,v,r)推出Add(x,y,r) |
| ObjectNaturalMultiplicationAlgebra.sumRightSentence | Mul(a,b,p)、Add(b,n,d)、Mul(a,n,q)下，Mul(a,d,r)↔Add(p,q,r) |
| sumLeftSentence | Add(a,b,d)、Mul(a,n,p)、Mul(b,n,q)下，Mul(d,n,r)↔Add(p,q,r) |
| leftSuccessorSentence | Succ(b,a)、Mul(a,n,p)下，Mul(b,n,r)↔Add(p,n,r) |
| commutativeSentence | Mul(a,n,p)↔Mul(n,a,p) |
| associativeSentence | Mul(a,b,u)、Mul(b,n,v)下，Mul(u,n,r)↔Mul(a,v,r) |
| unitSentence | Empty(z)、Succ(e,z)下，Mul(a,e,y)↔y=a，且Mul(e,a,y)↔y=a |

sumRight/sumLeft指发生相加的输入位置，避免把左右分配的名称与实际公式混淆。
单位元是任意实际内部空集的原后继，不固定宿主1或仅定义一个对象AST。
每句均有source_*、*_kernel_certificate与native_*证书。
核心端点为Derives ZFEquivalence.sourceZF [] (Translation.sentence sentence)，
原生端点为Derives nativeZF [] (Translation.sentence sentence)。

## 归纳与真实见证
三项重排实际取得b+c的内部和，再使用已证加法结合和交换。
四项互换实际取得(a+b)+c，再以三项重排连接(a+c)+b，保留全部实际和值。

乘法分配在内部n上归纳，固定实际a*b=p。
后继步实际取得旧索引和b+n、旧积a*n及p+a*n三个内部见证。
归纳假设给出对应真实乘积；加法/乘法后继式和加法结合把新和值接成新的原乘法递推。
逆向实际取得两个已知积之和，再以原乘积唯一性对齐输出，得到完整双向公式。

左参数后继律在内部n上归纳。后继步实际取得旧积、旧积+n及重排所需的中间和，
三项加法重排与加法后继方程给出正确的b步，原乘法后继律产生新积。
乘法交换的零点使用已证0*a=0；后继步实际取得旧积，调用左参数后继律。

结合律归纳第三乘数n，后继步实际取得b*n与(a*b)*n两个旧积，
原乘法后继式给两个加法关系，再以已证分配和归纳假设推出新的结合关系。
逆向取得实际左侧乘积并由唯一性传到给定右侧输出。
另一输入位置的分配由乘法交换和已经证明的分配正式组合。
两侧单位元律用实际Empty(z)、Succ(e,z)、零乘积、0+a=a及原乘法后继式取得。
所有归纳使用对象ω归纳原核模式；没有使用外部标准ω或Lean.Nat代数替代内部对象证明。

## 实际验收
C:/Python314/python.exe -X utf8 scripts/verify.py退出0，九条正式命令全部退出0。
LEAN_NUM_THREADS=1；lake --no-cache --wfail build完成368个任务。
Check、CheckStep2、CheckStep3、CheckStep4与Audit均以--trust=0通过。
2949项显式声明审计：198项无公理依赖、2751项记录允许依赖；0条警告。
新增17个模块、127项显式审计；337个验收文件的SHA256实际复核一致，差异0。
八个新核心证书均恰为propext/Classical.choice/Quot.sound。
verify.py强制核对累计二十七个算术核心证书及其native端点：
源核心恰为标准三项，原nativeZF端点恰为这三项加七个原有闭性证书。
这是Lean证书可信基记录，不是向对象ZF增加AC。
原choice额外证书仍只允许在既有桥接范围；两份可信基JSON、固定依赖和原核未变。
无新增自定义公理、sorry/admit、unsafe或native_decide；原19规则和九类源ZF原文锁定核对通过。
CheckStep4核对原公理包含接口、内部单位元AST及八个原nativeZF闭句端点。
日志/依赖/哈希仅保留本地verification/；未推送GitHub。

## 剩余主线
加乘关系的交换、结合、零/一及两侧分配律已经完成，精确关系半环进度标志为True。
本批不另行声称已构造全ω二元运算图；后续编码可以继续使用已证总单值对象关系。
自然次序差分、进一步单调/配数界、原Gödel配数/结构列表码正确性仍待完成。
因此完整算术与编码、专用ProofZF/U AST、任意内部码正确性和最终内部Con标志仍为False。
内部编译器、构造解释、实际对称强迫及最终相对一致性主句尚未完成。
原OpenAI完整构建及Comparator仍未运行，不据本批半环关系律宣称PP/AC主定理已完成。
